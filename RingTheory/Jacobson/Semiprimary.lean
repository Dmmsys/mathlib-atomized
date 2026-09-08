/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Semiprimary rings

## Main definition

* `IsSemiprimaryRing R`: a ring `R` is semiprimary if
  `Ring.jacobson R` is nilpotent and `R ⧸ Ring.jacobson R` is semisimple.
-/

public section

variable (R R₂ M M₂ : Type*) [Ring R] [Ring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]

/-
**IsSimpleModule.jacobson_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSimpleModule.jacobson_eq_bot [IsSimpleModule R M] : Module.jacobson R M 
= ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `isCoatom_bot`：isCoatom_bot : IsCoatom (⊥ : α)
· 使用定理 `IsSimpleModule.toIsSimpleOrder`：∀ {R : Type u_2} {inst : Ring R} {M : Ty
pe u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : IsSimpl
eModule R M], IsSimp…
-/
theorem IsSimpleModule.jacobson_eq_bot [IsSimpleModule R M] : Module.jacobson R M = ⊥ :=
  le_bot_iff.mp <| sInf_le isCoatom_bot
/-
**IsSemisimpleModule.jacobson_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemisimpleModule.jacobson_eq_bot [IsSemisimpleModule R M] : Module.jacob
son R M = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSemisimpleModule_iff_exists_linearEquiv_dfinsupp`：isSemisimpleModule_i
ff_exists_linearEquiv_dfinsupp : IsSemisimpleModule R M ↔ exists (s : Set (Submo
dule R M)) (_ : M ≃ₗ[R] Π₀ m : s, m.1), …
· 使用定理 `Module.jacobson_eq_bot_of_injective`：jacobson_eq_bot_of_injective (inj :
 Function.Injective f) (h : jacobson R₂ M₂ = ⊥) : jacobson R M = ⊥
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `DFinsupp.injective_pi_lapply`：injective_pi_lapply : Function.Injective (
LinearMap.pi (R
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Module.jacobson_pi_eq_bot`：jacobson_pi_eq_bot (h : forall i, jacobson R 
(M i) = ⊥) : jacobson R (Π i, M i) = ⊥
· 使用定理 `IsSimpleModule.jacobson_eq_bot`：IsSimpleModule.jacobson_eq_bot [IsSimple
Module R M] : Module.jacobson R M = ⊥
-/
theorem IsSemisimpleModule.jacobson_eq_bot [IsSemisimpleModule R M] :
    Module.jacobson R M = ⊥ :=
  have ⟨s, e, simple⟩ := isSemisimpleModule_iff_exists_linearEquiv_dfinsupp.mp ‹_›
  let f : M →ₗ[R] ∀ m : s, m.1 := (LinearMap.pi DFinsupp.lapply).comp e.toLinearMap
  Module.jacobson_eq_bot_of_injective f (DFinsupp.injective_pi_lapply (R := R).comp e.injective)
    (Module.jacobson_pi_eq_bot _ _ fun i ↦ IsSimpleModule.jacobson_eq_bot R _)
/-
**IsSemisimpleRing.jacobson_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemisimpleRing.jacobson_eq_bot [IsSemisimpleRing R] : Ring.jacobson R = 
⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemisimpleModule.jacobson_eq_bot`：IsSemisimpleModule.jacobson_eq_bot [
IsSemisimpleModule R M] : Module.jacobson R M = ⊥
-/
theorem IsSemisimpleRing.jacobson_eq_bot [IsSemisimpleRing R] : Ring.jacobson R = ⊥ :=
  IsSemisimpleModule.jacobson_eq_bot R R
/-
**IsSemisimpleModule.jacobson_le_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemisimpleModule.jacobson_le_ker [IsSemisimpleModule R₂ M₂] (f : M ->ₛₗ[
τ₁₂] M₂) : Module.jacobson R M <= LinearMap.ker f
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Module.le_comap_jacobson`：le_comap_jacobson : jacobson R M <= comap f (j
acobson R₂ M₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemisimpleModule.jacobson_eq_bot`：IsSemisimpleModule.jacobson_eq_bot [
IsSemisimpleModule R M] : Module.jacobson R M = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem IsSemisimpleModule.jacobson_le_ker [IsSemisimpleModule R₂ M₂] (f : M →ₛₗ[τ₁₂] M₂) :
    Module.jacobson R M ≤ LinearMap.ker f :=
  (Module.le_comap_jacobson f).trans <| by simp_rw [jacobson_eq_bot, LinearMap.ker, le_rfl]

/-- The Jacobson radical of a ring annihilates every semisimple module. -/
/-
**IsSemisimpleModule.jacobson_le_annihilator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemisimpleModule.jacobson_le_annihilator [IsSemisimpleModule R M] : Ring
.jacobson R <= Module.annihilator R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.mem_annihilator`：Module.mem_annihilator {r} : r in Module.annihil
ator R M ↔ forall m : M, r • m = 0
· 使用定理 `Module.le_comap_jacobson`：le_comap_jacobson : jacobson R M <= comap f (j
acobson R₂ M₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemisimpleModule.jacobson_eq_bot`：IsSemisimpleModule.jacobson_eq_bot [
IsSemisimpleModule R M] : Module.jacobson R M = ⊥

--- 原说明 ---
The Jacobson radical of a ring annihilates every semisimple module.
-/
theorem IsSemisimpleModule.jacobson_le_annihilator [IsSemisimpleModule R M] :
    Ring.jacobson R ≤ Module.annihilator R M :=
  fun r hr ↦ Module.mem_annihilator.mpr fun m ↦ by
    have := Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr
    rwa [jacobson_eq_bot] at this
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) (R) [CommRing R] [IsSemisimpleRing R] : IsReduced R where
  eq_zero _ := fun ⟨n, eq⟩ ↦ (IsSemisimpleRing.jacobson_eq_bot R).le <| Ideal.mem_sInf.mpr
    fun I hI ↦ (Ideal.isMaximal_def.mpr hI).isPrime.mem_of_pow_mem n (eq ▸ I.zero_mem)

/-- A ring is semiprimary if its Jacobson radical is nilpotent and its quotient by the
Jacobson radical is semisimple. -/
/-
**IsSemiprimaryRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Ring R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring is semiprimary if its Jacobson radical is nilpotent and its quotient by t
he
Jacobson radical is semisimple.
-/
@[mk_iff] class IsSemiprimaryRing : Prop where
  isSemisimpleRing : IsSemisimpleRing (R ⧸ Ring.jacobson R)
  isNilpotent : IsNilpotent (Ring.jacobson R)

attribute [instance] IsSemiprimaryRing.isSemisimpleRing
