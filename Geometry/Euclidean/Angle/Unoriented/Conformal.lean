/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
module

public import Mathlib.Analysis.Calculus.Conformal.NormedSpace
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angles and conformal maps

This file proves that conformal maps preserve angles.

-/

public section


namespace InnerProductGeometry

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-
**InnerProductGeometry.IsConformalMap.preserves_angle** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductGeometry.IsConformalMap`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : InnerProductSpa
ce ℝ F] {f' : E →L[ℝ] F},   IsConformalMap f' → ∀ (u v : E), InnerProductGeometr
y.angle (f' u) (f' v) = InnerProductGeometry.angle u v
参数：u v : E；f' u；f' v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `InnerProductGeometry.angle_smul_smul`：angle_smul_smul {c : Real} (hc : c
 != 0) (x y : V) : angle (c • x) (c • y) = angle x y
· 使用定理 `LinearIsometry.angle_map`：∀ {E : Type u_2} {F : Type u_3} [inst : Normed
AddCommGroup E] [inst_1 : NormedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ 
E] [inst_3 : I…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsConformalMap.preserves_angle {f' : E →L[ℝ] F} (h : IsConformalMap f') (u v : E) :
    angle (f' u) (f' v) = angle u v := by
  obtain ⟨c, hc, li, rfl⟩ := h
  exact (angle_smul_smul hc _ _).trans (li.angle_map _ _)

/-- If a real differentiable map `f` is conformal at a point `x`,
then it preserves the angles at that point. -/
/-
**InnerProductGeometry.ConformalAt.preserves_angle** 是 Mathlib 中的一个定理，位于命名空间 `In
nerProductGeometry.ConformalAt`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedAddCommGroup F]   [inst_2 : InnerProductSpace ℝ E] [inst_3 : InnerProductSpa
ce ℝ F] {f : E → F} {x : E} {f' : E →L[ℝ] F},   HasFDerivAt f f' x →     Conform
alAt f x → ∀ (u v : E), InnerProductGeometry.angle (f' u) (f' v) = InnerProductG
eometry.angle u v
参数：u v : E；f' u；f' v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductGeometry.IsConformalMap.preserves_angle`：∀ {E : Type u_1} {F
 : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [in
st_2 : InnerProductSpace ℝ E] [inst_3 : I…
· 使用定理 `HasFDerivAt.unique`：HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : H
asFDerivAt f f₁' x) : f' = f₁'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
If a real differentiable map `f` is conformal at a point `x`,
then it preserves the angles at that point.
-/
theorem ConformalAt.preserves_angle {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : HasFDerivAt f f' x)
    (H : ConformalAt f x) (u v : E) : angle (f' u) (f' v) = angle u v :=
  let ⟨_, h₁, c⟩ := H
  h₁.unique h ▸ IsConformalMap.preserves_angle c u v

end InnerProductGeometry

