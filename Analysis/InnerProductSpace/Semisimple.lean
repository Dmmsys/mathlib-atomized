/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.Semisimple

/-!
# Semisimple operators on inner product spaces

This file is a place to gather results related to semisimplicity of linear operators on inner
product spaces.

-/

public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap.IsSymmetric

variable {T : Module.End 𝕜 E} {p : Submodule 𝕜 E} (hT : T.IsSymmetric)

include hT

/-- The orthogonal complement of an invariant submodule is invariant. -/
/-
**LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule** 是 Mathlib 中的一个引
理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：orthogonalComplement_mem_invtSubmodule (hp : p in T.invtSubmodule) : pᗮ in
 T.invtSubmodule
参数：hp : p in T.invtSubmodule。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal complement of an invariant submodule is invariant.
-/
lemma orthogonalComplement_mem_invtSubmodule (hp : p ∈ T.invtSubmodule) :
    pᗮ ∈ T.invtSubmodule :=
  fun x hx y hy ↦ hT y x ▸ hx (T y) (hp hy)

/-- Symmetric operators are semisimple on finite-dimensional subspaces. -/
/-
**LinearMap.IsSymmetric.isFinitelySemisimple** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p.IsSymmetric`。
形式化陈述：isFinitelySemisimple : T.IsFinitelySemisimple
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.End.isFinitelySemisimple_iff`：isFinitelySemisimple_iff : f.IsFini
telySemisimple ↔ forall p in invtSubmodule f, Module.Finite R p -> forall q in i
nvtSubmodule f, q <= p ->…
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用引理 `Module.End.invtSubmodule.inf_mem`：inf_mem {p q : Submodule R M} (hp : p 
in f.invtSubmodule) (hq : q in f.invtSubmodule) : p ⊓ q in f.invtSubmodule
· 使用引理 `LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule`：orthogonal
Complement_mem_invtSubmodule (hp : p in T.invtSubmodule) : pᗮ in T.invtSubmodule
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.inf_orthogonal_eq_bot`：inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.finiteDimensional_of_le`：finiteDimensional_of_le {S₁ S₂ : Subm
odule K V} [FiniteDimensional K S₂] (h : S₁ <= S₂) : FiniteDimensional K S₁
· 使用定理 `Submodule.sup_orthogonal_of_hasOrthogonalProjection`：sup_orthogonal_of_h
asOrthogonalProjection [K.HasOrthogonalProjection] : K ⊔ Kᗮ = ⊤
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_inf_assoc_of_le`：sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x 
<= z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a

--- 原说明 ---
Symmetric operators are semisimple on finite-dimensional subspaces.
-/
theorem isFinitelySemisimple :
    T.IsFinitelySemisimple := by
  refine Module.End.isFinitelySemisimple_iff.mpr fun p hp₁ hp₂ q hq₁ hq₂ ↦
    ⟨qᗮ ⊓ p, inf_le_right, Module.End.invtSubmodule.inf_mem ?_ hp₁, ?_, ?_⟩
  · exact orthogonalComplement_mem_invtSubmodule hT hq₁
  · simp [disjoint_iff, ← inf_assoc, Submodule.inf_orthogonal_eq_bot q]
  · suffices q ⊔ qᗮ = ⊤ by rw [← sup_inf_assoc_of_le _ hq₂, this, top_inf_eq p]
    replace hp₂ : Module.Finite 𝕜 q := Submodule.finiteDimensional_of_le hq₂
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

end LinearMap.IsSymmetric

