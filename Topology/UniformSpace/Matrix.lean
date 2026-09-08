/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Heather Macbeth
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-!
# Uniform space structure on matrices
-/

public section


open Uniformity Topology

variable (m n 𝕜 : Type*) [UniformSpace 𝕜]

namespace Matrix

/-
**Matrix.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：instUniformSpace : UniformSpace (Matrix m n 𝕜)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniformSpace : UniformSpace (Matrix m n 𝕜) :=
  inferInstanceAs <| UniformSpace (m → n → 𝕜)
/-
**Matrix.instIsUniformAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：instIsUniformAddGroup [AddGroup 𝕜] [IsUniformAddGroup 𝕜] : IsUniformAddGro
up (Matrix m n 𝕜)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsUniformAddGroup [AddGroup 𝕜] [IsUniformAddGroup 𝕜] :
    IsUniformAddGroup (Matrix m n 𝕜) :=
  inferInstanceAs <| IsUniformAddGroup (m → n → 𝕜)
/-
**Matrix.uniformity** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：uniformity : 𝓤 (Matrix m n 𝕜) = ⨅ (i : m) (j : n), (𝓤 𝕜).comap fun a => (a
.1 i j, a.2 i j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.uniformity`：Pi.uniformity : 𝓤 (forall i, α i) = ⨅ i : ι, (Filter.coma
p fun a => (a.1 i, a.2 i)) (𝓤 (α i))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
-/
theorem uniformity :
    𝓤 (Matrix m n 𝕜) = ⨅ (i : m) (j : n), (𝓤 𝕜).comap fun a => (a.1 i j, a.2 i j) := by
  erw [Pi.uniformity]
  simp_rw [Pi.uniformity, Filter.comap_iInf, Filter.comap_comap]
  rfl
/-
**Matrix.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：uniformContinuous {β : Type*} [UniformSpace β] {f : β -> Matrix m n 𝕜} : U
niformContinuous f ↔ forall i j, UniformContinuous fun x => f x i j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.uniformity`：uniformity : 𝓤 (Matrix m n 𝕜) = ⨅ (i : m) (j : n), (𝓤
 𝕜).comap fun a => (a.1 i j, a.2 i j)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem uniformContinuous {β : Type*} [UniformSpace β] {f : β → Matrix m n 𝕜} :
    UniformContinuous f ↔ ∀ i j, UniformContinuous fun x => f x i j := by
  simp only [UniformContinuous, Matrix.uniformity, Filter.tendsto_iInf, Filter.tendsto_comap_iff]
  apply Iff.intro <;> intro a <;> apply a
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteSpace 𝕜] : CompleteSpace (Matrix m n 𝕜) :=
  inferInstanceAs <| CompleteSpace (m → n → 𝕜)

end Matrix

