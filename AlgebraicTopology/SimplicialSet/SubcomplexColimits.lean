/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.Limits.Types.Multicoequalizer

/-!
# Colimits involving subcomplexes of a simplicial set

If `X` is a simplicial set, and we have subcomplexes `A`, `U i` (for `i : ι`) and
`V i j` which satisfy `Subcomplex.MulticoequalizerDiagram A U V` (an abbreviation
for `CompleteLattice.MulticoequalizerDiagram`), we
show that the simplicial sset corresponding to `A` is the multicoequalizer of
the `U i` along the `V i j`.

Similarly, bicartesian squares in the lattice `Subcomplex X` give pushout
squares in the category of simplicial sets.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}}

section

variable {A : X.Subcomplex} {ι : Type*}
  {U : ι → X.Subcomplex} {V : ι → ι → X.Subcomplex}

variable (A U V) in
/-- Abbreviation for multicoequalizer diagrams in the complete lattice of
subcomplexes of a simplicial set. -/
/-
**SSet.Subcomplex.MulticoequalizerDiagram** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Subc
omplex`。
形式化陈述：MulticoequalizerDiagram
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation for multicoequalizer diagrams in the complete lattice of
subcomplexes of a simplicial set.
-/
abbrev MulticoequalizerDiagram := CompleteLattice.MulticoequalizerDiagram A U V

namespace MulticoequalizerDiagram

variable (h : MulticoequalizerDiagram A U V)

/-- The colimit multicofork attached to a `MulticoequalizerDiagram`
/-
**SSet.Subcomplex.MulticoequalizerDiagram.in** 是 Mathlib 中的一个结构，位于命名空间 `SSet.Sub
complex.MulticoequalizerDiagram`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure in the complete lattice of subcomplexes of a simplicial set. -/
/-
**SSet.Subcomplex.MulticoequalizerDiagram.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `S
Set.Subcomplex.MulticoequalizerDiagram`。
形式化陈述：isColimit : IsColimit (h.multicofork.map toSSetFunctor)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit multicofork attached to a `MulticoequalizerDiagram`
structure in the complete lattice of subcomplexes of a simplicial set.
-/
noncomputable def isColimit :
    IsColimit (h.multicofork.map toSSetFunctor) :=
  evaluationJointlyReflectsColimits _ (fun n ↦ by
    have h' : CompleteLattice.MulticoequalizerDiagram (A.obj n) (fun i ↦ (U i).obj n)
        (fun i j ↦ (V i j).obj n) :=
      { eq_inf := by simp [h.eq_inf]
        iSup_eq := by simp [← h.iSup_eq] }
    exact (Multicofork.isColimitMapEquiv _ _).2
      (Types.isColimitOfMulticoequalizerDiagram h'))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A colimit multicofork attached to a `MulticoequalizerDiagram`
structure in the complete lattice of subcomplexes of a simplicial set.
In this variant, we assume that the index type `ι` has a linear order. This allows
to consider only the "relations" given by tuples `(i, j)` such that `i < j`. -/
/-
**SSet.Subcomplex.MulticoequalizerDiagram.isColimit'** 是 Mathlib 中的一个定义，位于命名空间 `
SSet.Subcomplex.MulticoequalizerDiagram`。
形式化陈述：isColimit' [LinearOrder ι] : IsColimit (h.multicofork.toLinearOrder.map to
SSetFunctor)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A colimit multicofork attached to a `MulticoequalizerDiagram`
structure in the complete lattice of subcomplexes of a simplicial set.
In this variant, we assume that the index type `ι` has a linear order. This allo
ws
to consider only the "relations" given by tuples `(i, j)` such that `i < j`.
-/
noncomputable def isColimit' [LinearOrder ι] :
    IsColimit (h.multicofork.toLinearOrder.map toSSetFunctor) :=
  Multicofork.isColimitToLinearOrder _ h.isColimit
    { iso i j := toSSetFunctor.mapIso (eqToIso (by
        dsimp
        rw [h.eq_inf, h.eq_inf, inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

end MulticoequalizerDiagram

end

/-- Abbreviation for bicartesian squares in the lattice of subcomplexes of a simplicial set. -/
/-
**SSet.Subcomplex.BicartSq** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：BicartSq (A₁ A₂ A₃ A₄ : X.Subcomplex)
参数：A₁ A₂ A₃ A₄ : X.Subcomplex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation for bicartesian squares in the lattice of subcomplexes of a simplic
ial set.
-/
abbrev BicartSq (A₁ A₂ A₃ A₄ : X.Subcomplex) := Lattice.BicartSq A₁ A₂ A₃ A₄
/-
**SSet.Subcomplex.BicartSq.isPushout** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Subcomplex.
BicartSq`。
形式化陈述：∀ {X : _root_.SSet} {A₁ A₂ A₃ A₄ : X.Subcomplex} (sq : A₁.BicartSq A₂ A₃ A
₄),   CategoryTheory.IsPushout (SSet.Subcomplex.homOfLE ⋯) (SSet.Subcomplex.homO
fLE ⋯) (SSet.Subcomplex.homOfLE ⋯)     (SSet.Subcomplex.homOfLE ⋯)
参数：sq : A₁.BicartSq A₂ A₃ A₄；SSet.Subcomplex.homOfLE ⋯；SSet.Subcomplex.homOfLE ⋯
；SSet.Subcomplex.homOfLE ⋯；SSet.Subcomplex.homOfLE ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Lattice.BicartSq.le₁₂`：le₁₂ : x₁ <= x₂
· 使用引理 `Lattice.BicartSq.le₁₃`：le₁₃ : x₁ <= x₃
· 使用引理 `Lattice.BicartSq.le₂₄`：le₂₄ : x₂ <= x₄
· 使用引理 `Lattice.BicartSq.le₃₄`：le₃₄ : x₃ <= x₄
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lattice.BicartSq.sup_eq`：∀ {T : Type u} {x₁ x₂ x₃ x₄ : T} [inst : Lattic
e T], Lattice.BicartSq x₁ x₂ x₃ x₄ → x₂ ⊔ x₃ = x₄
· 使用定理 `Lattice.BicartSq.inf_eq`：∀ {T : Type u} {x₁ x₂ x₃ x₄ : T} [inst : Lattic
e T], Lattice.BicartSq x₁ x₂ x₃ x₄ → x₂ ⊓ x₃ = x₁
· 使用引理 `CategoryTheory.Limits.Types.isPushout_of_bicartSq`：isPushout_of_bicartSq
 {S₁ S₂ S₃ S₄ : Set X} (h : Lattice.BicartSq S₁ S₂ S₃ S₄) : IsPushout (Set.funct
orToTypes.map (homOfLE h.le₁₂)) (Set.fu…
-/
lemma BicartSq.isPushout {A₁ A₂ A₃ A₄ : X.Subcomplex} (sq : BicartSq A₁ A₂ A₃ A₄) :
    IsPushout (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) where
  w := rfl
  isColimit' :=
    ⟨evaluationJointlyReflectsColimits _
      (fun n ↦ (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (by
        have h : Lattice.BicartSq (A₁.obj n) (A₂.obj n) (A₃.obj n) (A₄.obj n) :=
          { sup_eq := by
              rw [← sq.sup_eq]
              rfl
            inf_eq := by
              rw [← sq.inf_eq]
              rfl }
        exact (Types.isPushout_of_bicartSq h).isColimit))⟩

end Subcomplex

end SSet

