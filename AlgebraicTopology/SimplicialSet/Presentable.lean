/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.AlgebraicTopology.SimplicialSet.RegularEpi
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.Presheaf

/-!
# Finite simplicial sets are presentable

In this file, we show that finite simplicial sets are finitely presentable,
which will allow the use of the small object argument in `SSet`.

-/

public section

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

namespace Finite

/-
**SSet.Finite.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : SimplexCategory) :
    IsFinitelyPresentable.{u} (stdSimplex.{u}.obj n) :=
  inferInstanceAs (IsFinitelyPresentable.{u} (uliftYoneda.obj n))

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Finite.exists_epi_from_isCardinalPresentable** 是 Mathlib 中的一个引理，位于命名空间 `S
Set.Finite`。
形式化陈述：exists_epi_from_isCardinalPresentable (X : SSet.{u}) [X.Finite] : exists (
Y : SSet.{u}) (_ : Y.Finite) (_ : IsFinitelyPresentable.{u} Y) (p : Y ⟶ X), Epi 
p
参数：X : SSet.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `SSet.instFiniteSigmaObjOfFinite`：∀ {ι : Type v} [Finite ι] (X : ι → _roo
t_.SSet) [inst : CategoryTheory.Limits.HasCoproduct X] [∀ (j : ι), (X j).Finite]
,   (∐ X).Finite
· 使用定理 `SSet.Finite.finite`：∀ {X : _root_.SSet} [self : X.Finite], Finite X.N
· 使用定理 `SSet.stdSimplex.instFiniteObjSimplexCategory`：∀ (n : SimplexCategory), (
SSet.stdSimplex.obj n).Finite
· 使用引理 `CategoryTheory.isCardinalPresentable_of_isColimit'`：isCardinalPresentabl
e_of_isColimit' {K : Type u'} [Category.{v'} K] {Y : K ⥤ C} (c : Cocone Y) (hc :
 IsColimit c) (κ : Cardinal.{w}) [Fact κ…
· 使用引理 `Cardinal.fact_isRegular_aleph0`：fact_isRegular_aleph0 : Fact (IsRegular 
ℵ₀) where out
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用引理 `hasCardinalLT_of_finite`：hasCardinalLT_of_finite (X : Type*) [Finite X] 
(κ : Cardinal) (hκ : Cardinal.aleph0 <= κ) : HasCardinalLT X κ
· 使用定理 `CategoryTheory.instFiniteArrowDiscrete`：∀ (X : Type u) [Finite X], Finit
e (CategoryTheory.Arrow (CategoryTheory.Discrete X))
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SSet.Finite.instIsFinitelyPresentableObjSimplexCategoryStdSimplex`：∀ (n 
: SimplexCategory), CategoryTheory.IsFinitelyPresentable (SSet.stdSimplex.obj n)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.range_eq_iSup_sigma_ι`：range_eq_iSup_sigma_ι {ι : Type v} [HasColim
itsOfShape (Discrete ι) (Type u)] {X : ι -> SSet.{u}} {Y : SSet.{u}} [HasCoprodu
ct X] (f : ∐ X ⟶…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用引理 `SSet.Subcomplex.range_eq_ofSimplex`：range_eq_ofSimplex {n : Nat} (f : Δ[
n] ⟶ X) : range f = ofSimplex (yonedaEquiv f)
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_epi_from_isCardinalPresentable (X : SSet.{u}) [X.Finite] :
    ∃ (Y : SSet.{u}) (_ : Y.Finite) (_ : IsFinitelyPresentable.{u} Y)
      (p : Y ⟶ X), Epi p := by
  refine ⟨∐ (fun (s : X.N) ↦ Δ[s.dim]), inferInstance, ?_,
    Sigma.desc (fun s ↦ yonedaEquiv.symm s.simplex), ?_⟩
  · apply +allowSynthFailures isCardinalPresentable_of_isColimit' _ (coproductIsCoproduct _)
    · exact hasCardinalLT_of_finite _ _ (by rfl)
    · rintro s
      dsimp
      infer_instance
  · simp only [← Subcomplex.range_eq_top_iff, range_eq_iSup_sigma_ι,
        colimit.ι_desc, Cofan.mk_ι_app, ← N.iSup_subcomplex_eq_top,
        Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]
/-
**SSet.Finite.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : SSet.{u}) [X.Finite] : IsFinitelyPresentable.{u} X := by
  obtain ⟨Y, _, _, p, _⟩ := exists_epi_from_isCardinalPresentable X
  obtain ⟨Z, _, _, q, _⟩ := exists_epi_from_isCardinalPresentable (pullback p p)
  have := Cardinal.fact_isRegular_aleph0.{u}
  have := IsRegularEpiCategory.regularEpiOfEpi p
  apply +allowSynthFailures isCardinalPresentable_of_isColimit' _
      (isCoequalizerEpiComp ((EffectiveEpi.getStruct p).isColimitCoforkOfIsPullback
        (IsPullback.of_hasPullback p p)) q) _
  · exact hasCardinalLT_of_finite _ _ (by rfl)
  · rintro (_ | _) <;> dsimp <;> infer_instance

end Finite

end SSet

