/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Mathlib.CategoryTheory.Sites.Hypercover.One

/-!
# The 1-hypercover of a glue data

In this file, given `D : Scheme.GlueData`, we construct a 1-hypercover
`D.openHypercover` of the scheme `D.glued` in the big Zariski site.
We use this 1-hypercover in order to define a constructor `D.sheafValGluedMk`
for sections over `D.glued` of a sheaf of types over the big Zariski site.

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.

-/

@[expose] public section

universe v u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme.GlueData

variable (D : Scheme.GlueData.{u})

/-- The 1-hypercover of `D.glued` in the big Zariski site that is given by the
open cover `D.U` from the glue data `D`.
The "covering of the intersection of two such open subsets" is the trivial
covering given by `D.V`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.GlueData.oneHypercover** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.Scheme.GlueData`。
形式化陈述：oneHypercover : Scheme.zariskiTopology.OneHypercover D.glued where I₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 1-hypercover of `D.glued` in the big Zariski site that is given by the
open cover `D.U` from the glue data `D`.
The "covering of the intersection of two such open subsets" is the trivial
covering given by `D.V`.
-/
noncomputable def oneHypercover : Scheme.zariskiTopology.OneHypercover D.glued where
  I₀ := D.J
  X := D.U
  f := D.ι
  I₁ _ _ := PUnit
  Y i₁ i₂ _ := D.V (i₁, i₂)
  p₁ i₁ i₂ _ := D.f i₁ i₂
  p₂ i₁ i₂ _ := D.t i₁ i₂ ≫ D.f i₂ i₁
  w i₁ i₂ _ := by simp only [Category.assoc, Scheme.GlueData.glue_condition]
  mem₀ := by
    refine zariskiTopology.superset_covering ?_ D.openCover.mem_grothendieckTopology
    rw [Sieve.generate_le_iff]
    rintro W _ ⟨i⟩
    exact ⟨_, 𝟙 _, _, ⟨i⟩, by simp; rfl⟩
  mem₁ i₁ i₂ W p₁ p₂ fac := by
    refine zariskiTopology.superset_covering (fun T g _ ↦ ?_) (zariskiTopology.top_mem _)
    have ⟨φ, h₁, h₂⟩ := PullbackCone.IsLimit.lift' (D.vPullbackConeIsLimit i₁ i₂)
      (g ≫ p₁) (g ≫ p₂) (by simpa using g ≫= fac)
    exact ⟨⟨⟩, φ, h₁.symm, h₂.symm⟩

section

variable {F : Sheaf Scheme.zariskiTopology (Type v)}
  (s : ∀ (j : D.J), F.obj.obj (op (D.U j)))
  (h : ∀ (i j : D.J), F.obj.map (D.f i j).op (s i) =
    F.obj.map ((D.f j i).op ≫ (D.t i j).op) (s j))

/-- Constructor for sections over `D.glued` of a sheaf of types on the big Zariski site. -/
/-
**AlgebraicGeometry.Scheme.GlueData.sheafValGluedMk** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.GlueData`。
形式化陈述：sheafValGluedMk : F.obj.obj (op D.glued)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for sections over `D.glued` of a sheaf of types on the big Zariski s
ite.
-/
noncomputable def sheafValGluedMk : F.obj.obj (op D.glued) :=
  Multifork.IsLimit.sectionsEquiv (D.oneHypercover.isLimitMultifork F)
    { val := s
      property := fun _ ↦ h _ _ }

@[simp]
/-
**AlgebraicGeometry.Scheme.GlueData.sheafValGluedMk_val** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.GlueData`。
形式化陈述：sheafValGluedMk_val (j : D.J) : F.obj.map (D.ι j).op (D.sheafValGluedMk s 
h) = s j
参数：j : D.J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.Multifork.IsLimit.sectionsEquiv_apply_val`：section
sEquiv_apply_val (s : I.sections) (i : J.L) : c.ι i (sectionsEquiv hc s) = s.val
 i
-/
lemma sheafValGluedMk_val (j : D.J) : F.obj.map (D.ι j).op (D.sheafValGluedMk s h) = s j :=
  Multifork.IsLimit.sectionsEquiv_apply_val (D.oneHypercover.isLimitMultifork F) _ _

end

end AlgebraicGeometry.Scheme.GlueData

