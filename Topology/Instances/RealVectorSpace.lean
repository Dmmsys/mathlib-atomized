/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Algebra.Module.Rat

/-!
# Continuous additive maps are `ℝ`-linear

In this file we prove that a continuous map `f : E →+ F` between two topological vector spaces
over `ℝ` is `ℝ`-linear
-/

@[expose] public section


variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousSMul ℝ F] [T2Space F]

/-- A continuous additive map between two vector spaces over `ℝ` is `ℝ`-linear. -/
/-
**map_real_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_real_smul {G} [FunLike G E F] [AddMonoidHomClass G E F] (f : G) (hf : 
Continuous f) (c : Real) (x : E) : f (c • x) = c • f x
参数：f : G；hf : Continuous f；c : Real；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.equalizer`：DenseRange.equalizer (hfd : DenseRange f) {g h : β
 -> γ} (hg : Continuous g) (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `IsDenseEmbedding.toIsDenseInducing`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbe
dding e → IsDenseInducin…
· 使用定理 `Rat.isDenseEmbedding_coe_real`：isDenseEmbedding_coe_real : IsDenseEmbedd
ing ((↑) : Rat -> Real)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_ratCast_smul`：map_ratCast_smul [AddCommGroup M] [AddCommGroup M₂] {F
 : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Div
isionR…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
A continuous additive map between two vector spaces over `ℝ` is `ℝ`-linear.
-/
theorem map_real_smul {G} [FunLike G E F] [AddMonoidHomClass G E F] (f : G) (hf : Continuous f)
    (c : ℝ) (x : E) :
    f (c • x) = c • f x :=
  suffices (fun c : ℝ => f (c • x)) = fun c : ℝ => c • f x from congr_fun this c
  Rat.isDenseEmbedding_coe_real.dense.equalizer (by fun_prop)
    (continuous_id.smul continuous_const) (funext fun r => map_ratCast_smul f ℝ ℝ r x)

namespace AddMonoidHom

/-- Reinterpret a continuous additive homomorphism between two real vector spaces
as a continuous real-linear map. -/
/-
**AddMonoidHom.toRealLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：toRealLinearMap (f : E ->+ F) (hf : Continuous f) : E ->L[Real] F
参数：f : E ->+ F；hf : Continuous f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a continuous additive homomorphism between two real vector spaces
as a continuous real-linear map.
-/
def toRealLinearMap (f : E →+ F) (hf : Continuous f) : E →L[ℝ] F :=
  ⟨{  toFun := f
      map_add' := f.map_add
      map_smul' := map_real_smul f hf }, hf⟩

@[simp]
/-
**AddMonoidHom.coe_toRealLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：coe_toRealLinearMap (f : E ->+ F) (hf : Continuous f) : ⇑(f.toRealLinearMa
p hf) = f
参数：f : E ->+ F；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toRealLinearMap (f : E →+ F) (hf : Continuous f) : ⇑(f.toRealLinearMap hf) = f :=
  rfl

end AddMonoidHom

set_option backward.defeqAttrib.useBackward true in
/-- Reinterpret a continuous additive equivalence between two real vector spaces
as a continuous real-linear map. -/
/-
**AddEquiv.toRealLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.toRealLinearEquiv (e : E ≃+ F) (h₁ : Continuous e) (h₂ : Continuo
us e.symm) : E ≃L[Real] F
参数：e : E ≃+ F；h₁ : Continuous e；h₂ : Continuous e.symm。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a continuous additive equivalence between two real vector spaces
as a continuous real-linear map.
-/
def AddEquiv.toRealLinearEquiv (e : E ≃+ F) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    E ≃L[ℝ] F :=
  { e, e.toAddMonoidHom.toRealLinearMap h₁ with }

/-- A topological group carries at most one structure of a topological `ℝ`-module, so for any
topological `ℝ`-algebra `A` (e.g. `A = ℂ`) and any topological group that is both a topological
`ℝ`-module and a topological `A`-module, these structures agree. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological group carries at most one structure of a topological `ℝ`-module, s
o for any
topological `ℝ`-algebra `A` (e.g. `A = ℂ`) and any topological group that is bot
h a topological
`ℝ`-module and a topological `A`-module, these structures agree.
-/
instance (priority := 900) Real.isScalarTower [T2Space E] {A : Type*} [TopologicalSpace A] [Ring A]
    [Algebra ℝ A] [Module A E] [ContinuousSMul ℝ A] [ContinuousSMul A E] : IsScalarTower ℝ A E :=
  ⟨fun r x y => map_real_smul ((smulAddHom A E).flip y) (continuous_id.smul continuous_const) r x⟩
