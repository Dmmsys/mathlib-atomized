/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Shift.ShiftedHomOpposite
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# The Yoneda functors are homological

Let `C` be a pretriangulated category. In this file, we show that the
functors `preadditiveCoyoneda.obj A : C ⥤ AddCommGrpCat` for `A : Cᵒᵖ` and
`preadditiveYoneda.obj B : Cᵒᵖ ⥤ AddCommGrpCat` for `B : C` are homological functors.

-/

public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]

namespace CategoryTheory

open Limits Opposite Pretriangulated.Opposite

namespace Pretriangulated

section

variable [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]

@[stacks 0149]
/-
**CategoryTheory.Pretriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pret
riangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Cᵒᵖ) : (preadditiveCoyoneda.obj A).IsHomological where
  exact T hT := by
    rw [ShortComplex.ab_exact_iff]
    intro (x₂ : A.unop ⟶ T.obj₂) (hx₂ : x₂ ≫ T.mor₂ = 0)
    obtain ⟨x₁, hx₁⟩ := T.coyoneda_exact₂ hT x₂ hx₂
    exact ⟨x₁, hx₁.symm⟩

@[stacks 0149]
/-
**CategoryTheory.Pretriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pret
riangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (B : C) : (preadditiveYoneda.obj B).IsHomological where
  exact T hT := by
    rw [ShortComplex.ab_exact_iff]
    intro (x₂ : T.obj₂.unop ⟶ B) (hx₂ : T.mor₂.unop ≫ x₂ = 0)
    obtain ⟨x₃, hx₃⟩ := Triangle.yoneda_exact₂ _ (unop_distinguished T hT) x₂ hx₂
    exact ⟨x₃, hx₃.symm⟩
/-
**CategoryTheory.Pretriangulated.preadditiveYoneda_map_distinguished** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：preadditiveYoneda_map_distinguished (T : Triangle C) (hT : T in distTriang
 C) (B : C) : ((shortComplexOfDistTriangle T hT).op.map (preadditiveYoneda.obj B
)).Exact
参数：T : Triangle C；hT : T in distTriang C；B : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.map_distinguished_op_exact`：map_distinguished_op_
exact {A : Type*} [Category* A] [Abelian A] (F : Cᵒᵖ ⥤ A) [F.IsHomological] (T :
 Triangle C) (hT : T in distTriang C) :…
· 使用定理 `CategoryTheory.Pretriangulated.instIsHomologicalOppositeAddCommGrpCatObj
FunctorPreadditiveYoneda`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1,
 u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.HasS
hift C…
-/
lemma preadditiveYoneda_map_distinguished
    (T : Triangle C) (hT : T ∈ distTriang C) (B : C) :
    ((shortComplexOfDistTriangle T hT).op.map (preadditiveYoneda.obj B)).Exact :=
  (preadditiveYoneda.obj B).map_distinguished_op_exact T hT

end

/-
**CategoryTheory.Pretriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pret
riangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (A : Cᵒᵖ) : (preadditiveCoyoneda.obj A).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _
/-
**CategoryTheory.Pretriangulated.preadditiveCoyoneda_homologySequence** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preadditiveCoyoneda_homologySequenceδ_apply
    (T : Triangle C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) {A : Cᵒᵖ} (x : A.unop ⟶ T.obj₃⟦n₀⟧) :
    (preadditiveCoyoneda.obj A).homologySequenceδ T n₀ n₁ h x =
      x ≫ T.mor₃⟦n₀⟧' ≫ (shiftFunctorAdd' C 1 n₀ n₁ (by lia)).inv.app _ := by
  apply Category.assoc

section

variable [∀ (n : ℤ), (shiftFunctor C n).Additive]

/-
**CategoryTheory.Pretriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pret
riangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (B : C) : (preadditiveYoneda.obj B).ShiftSequence ℤ where
  sequence n := preadditiveYoneda.obj (B⟦n⟧)
  isoZero := preadditiveYoneda.mapIso ((shiftFunctorZero C ℤ).app B)
  shiftIso n a a' h := NatIso.ofComponents (fun A ↦ AddEquiv.toAddCommGrpIso
    { toEquiv := Quiver.Hom.opEquiv.trans (ShiftedHom.opEquiv' n a a' h).symm
      map_add' := fun _ _ ↦ ShiftedHom.opEquiv'_symm_add _ _ _ h })
        (by intros; ext; apply ShiftedHom.opEquiv'_symm_comp _ _ _ h)
  shiftIso_zero a := by ext; apply ShiftedHom.opEquiv'_zero_add_symm
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext _ x
    exact ShiftedHom.opEquiv'_add_symm n m a a' a'' ha' ha'' x.op
/-
**CategoryTheory.Pretriangulated.preadditiveYoneda_shiftMap_apply** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：preadditiveYoneda_shiftMap_apply (B : C) {X Y : Cᵒᵖ} (n : Int) (f : X ⟶ Y⟦
n⟧) (a a' : Int) (h : n + a = a') (z : X.unop ⟶ B⟦a⟧) : (preadditiveYoneda.obj B
).shiftMap f a a' h z = ((ShiftedHom.opEquiv _).symm f).comp z (show a + n = a' 
by lia)
参数：B : C；n : Int；f : X ⟶ Y⟦n⟧；a a' : Int；h : n + a = a'；z : X.unop ⟶ B⟦a⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.ShiftedHom.opEquiv_symm_apply_comp`：opEquiv_symm_apply_co
mp {X Y : C} {a : Int} (f : ShiftedHom (Opposite.op X) (Opposite.op Y) a) {b : I
nt} {Z : C} (z : ShiftedHom X Z b) {c :…
-/
lemma preadditiveYoneda_shiftMap_apply (B : C) {X Y : Cᵒᵖ} (n : ℤ) (f : X ⟶ Y⟦n⟧)
    (a a' : ℤ) (h : n + a = a') (z : X.unop ⟶ B⟦a⟧) :
    (preadditiveYoneda.obj B).shiftMap f a a' h z =
      ((ShiftedHom.opEquiv _).symm f).comp z (show a + n = a' by lia) := by
  symm
  apply ShiftedHom.opEquiv_symm_apply_comp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Pretriangulated.preadditiveYoneda_homologySequence** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preadditiveYoneda_homologySequenceδ_apply
    (T : Triangle C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) {B : C} (x : T.obj₁ ⟶ B⟦n₀⟧) :
    (preadditiveYoneda.obj B).homologySequenceδ
      ((triangleOpEquivalence _).functor.obj (op T)) n₀ n₁ h x =
      T.mor₃ ≫ x⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C n₀ 1 n₁ h).inv.app B := by
  simp only [Functor.homologySequenceδ, preadditiveYoneda_shiftMap_apply,
    ShiftedHom.comp, ← Category.assoc]
  congr 2
  apply (ShiftedHom.opEquiv _).injective
  rw [Equiv.apply_symm_apply]
  rfl

end

end Pretriangulated

end CategoryTheory

