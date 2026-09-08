/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Singular homology

In this file, we define the singular chain complex and singular homology of a topological space.
We also calculate the homology of a totally disconnected space as an example.

-/

@[expose] public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory Limits

universe w v u

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C]
variable [Preadditive C] (n : ℕ)

/-- The singular chain complex functor with coefficients in `C`. -/
/-
**AlgebraicTopology.singularChainComplexFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicTopology`。
形式化陈述：singularChainComplexFunctor : C ⥤ TopCat.{w} ⥤ ChainComplex C Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The singular chain complex functor with coefficients in `C`.
-/
def singularChainComplexFunctor :
    C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ :=
  SSet.chainComplexFunctor.{w} C ⋙ (Functor.whiskeringLeft _ _ _).obj TopCat.toSSet.{w}
/-
**AlgebraicTopology.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (singularChainComplexFunctor C).Additive := by
  delta singularChainComplexFunctor
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicTopology.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Limits.HasPullbacks C] {X : C} :
    ((singularChainComplexFunctor C).obj X).PreservesMonomorphisms where
  preserves f _ := by
    dsimp [singularChainComplexFunctor, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
    apply +allowSynthFailures Functor.map_mono
    dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
    infer_instance

/-- The `n`-th singular homology functor with coefficients in `C`. -/
/-
**AlgebraicTopology.singularHomologyFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Topology`。
形式化陈述：singularHomologyFunctor [CategoryWithHomology C] : C ⥤ TopCat.{w} ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th singular homology functor with coefficients in `C`.
-/
def singularHomologyFunctor [CategoryWithHomology C] : C ⥤ TopCat.{w} ⥤ C :=
  singularChainComplexFunctor C ⋙
    (Functor.whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n)

section Adjunction

open Limits _root_.SSet
open scoped Simplicial
open HomologicalComplex (eval)

/-- The adjunction `Hom(Cⁿ(-, X), F) ≃ Hom(X, F(Δ[n]))` for `X : C` and `F : Top ⥤ C`. -/
/-
**AlgebraicTopology.singularChainComplexFunctorAdjunction** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicTopology`。
形式化陈述：singularChainComplexFunctorAdjunction : (Functor.postcompose₂.obj (eval _ 
_ n)).obj (singularChainComplexFunctor C) ⊣ (evaluation _ _).obj (SimplexCategor
y.toTop.obj ⦋n⦌)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `Hom(Cⁿ(-, X), F) ≃ Hom(X, F(Δ[n]))` for `X : C` and `F : Top ⥤ C
`.
-/
def singularChainComplexFunctorAdjunction : (Functor.postcompose₂.obj (eval _ _ n)).obj
    (singularChainComplexFunctor C) ⊣ (evaluation _ _).obj (SimplexCategory.toTop.obj ⦋n⦌) :=
  ((SSet.chainComplexFunctorAdjunction C n).comp (sSetTopAdj.whiskerLeft _)).ofNatIsoRight
    ((evaluation TopCat C).mapIso (SSet.toTopSimplex.app _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicTopology.singularChainComplexFunctorAdjunction_unit_app** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicTopology`。
形式化陈述：singularChainComplexFunctorAdjunction_unit_app (R : C) : (singularChainCom
plexFunctorAdjunction C n).unit.app R = Sigma.ι (fun _ => R) ((stdSimplexToTop.a
pp ⦋n⦌).app (.op ⦋n⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))
参数：R : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.whiskerLeft_unit_app_app`：∀ (C : Type u_1) {D 
: Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_comp_map'`：∀ {β : Type w} {α : Type w₂} {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [
inst_1 : CategoryTheory.Limit…
-/
lemma singularChainComplexFunctorAdjunction_unit_app (R : C) :
    (singularChainComplexFunctorAdjunction C n).unit.app R =
      Sigma.ι (fun _ ↦ R) ((stdSimplexToTop.app ⦋n⦌).app (.op ⦋n⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) := by
  dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
    Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
    Adjunction.comp, singularChainComplexFunctor,
    SSet.chainComplexFunctorAdjunction, SSet.chainComplexFunctor]
  simp [stdSimplexToTop]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicTopology.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_singularChainComplexFunctorAdjunction_counit_app_app (F : TopCat ⥤ C) (X : TopCat) (i) :
    Sigma.ι _ i ≫ ((singularChainComplexFunctorAdjunction C n).counit.app F).app X =
      F.map i.down := by
  trans F.map (SSet.toTopSimplex.inv.app ⦋n⦌ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm i) ≫
      sSetTopAdj.counit.app X)
  · dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
      Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
      Adjunction.comp, singularChainComplexFunctor, SSet.chainComplexFunctor,
      SSet.chainComplexFunctorAdjunction]
    simp
  · congr 1
    rw [← reassoc_of% sSetTopAdj_unit_app_app_down]
    exact congr(($(sSetTopAdj.right_triangle_components X).app (.op ⦋n⦌) i).down)

end Adjunction

section TotallyDisconnectedSpace

variable (R : C) (X : TopCat.{w}) [TotallyDisconnectedSpace X]

/-- If `X` is totally disconnected,
its singular chain complex is given by `R[X] ←0- R[X] ←𝟙- R[X] ←0- R[X] ⋯`,
where `R[X]` is the coproduct of copies of `R` indexed by elements of `X`. -/
noncomputable
/-
**AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace** 是
 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology`。
形式化陈述：singularChainComplexFunctorIsoOfTotallyDisconnectedSpace : ((singularChain
ComplexFunctor C).obj R).obj X ≅ (ChainComplex.alternatingConst.obj (∐ fun _ : X
 => R))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def singularChainComplexFunctorIsoOfTotallyDisconnectedSpace :
    ((singularChainComplexFunctor C).obj R).obj X ≅
      (ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ R)) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (((SimplicialObject.whiskering _ _).obj _).mapIso
    (TopCat.toSSetIsoConst X) ≪≫ Functor.constComp _ _ _) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app _
/-
**AlgebraicTopology.singularChainComplexFunctor_exactAt_of_totallyDisconnectedSp
ace** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicTopology`。
形式化陈述：singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace (hn : n !=
 0) : (((singularChainComplexFunctor C).obj R).obj X).ExactAt n
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasCoproducts_shrink`：hasCoproducts_shrink [HasCop
roducts.{max w w'} C] : HasCoproducts.{w} C
· 使用定理 `CategoryTheory.Limits.IsInitial.isZero`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroMorphisms C] {X : C}   (h
X : CategoryTheory.Limits.Is…
· 使用定理 `HomologicalComplex.ExactAt.of_iso`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   
{ι : Type u_2} {c : Com…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `ChainComplex.alternatingConst_exactAt`：alternatingConst_exactAt (X : C) 
(n : Nat) (hn : n != 0) : (alternatingConst.obj X).ExactAt n
-/
lemma singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
    (hn : n ≠ 0) :
    (((singularChainComplexFunctor C).obj R).obj X).ExactAt n :=
  have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  .of_iso (ChainComplex.alternatingConst_exactAt _ _ hn)
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X).symm
/-
**AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace**
 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicTopology`。
形式化陈述：isZero_singularHomologyFunctor_of_totallyDisconnectedSpace [CategoryWithHo
mology C] (hn : n != 0) : IsZero (((singularHomologyFunctor C n).obj R).obj X)
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasCoproducts_shrink`：hasCoproducts_shrink [HasCop
roducts.{max w w'} C] : HasCoproducts.{w} C
· 使用定理 `CategoryTheory.Limits.IsInitial.isZero`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroMorphisms C] {X : C}   (h
X : CategoryTheory.Limits.Is…
· 使用定理 `HomologicalComplex.ExactAt.isZero_homology`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C]   {ι : Type u_2} {c : Com…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用引理 `AlgebraicTopology.singularChainComplexFunctor_exactAt_of_totallyDisconne
ctedSpace`：singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace (hn :
 n != 0) : (((singularChainComplexFunctor C).obj R).obj X).ExactAt n
-/
lemma isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    [CategoryWithHomology C] (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj X) :=
  have := hasCoproducts_shrink.{0, w} (C := C)
  have : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  (singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace C n R X hn).isZero_homology

/-- The zeroth singular homology of a totally disconnected space is the
free `R`-module generated by elements of `X`. -/
noncomputable
/-
**AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace** 是 Ma
thlib 中的一个定义，位于命名空间 `AlgebraicTopology`。
形式化陈述：singularHomologyFunctorZeroOfTotallyDisconnectedSpace [CategoryWithHomolog
y C] : ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ fun _ : X => R
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def singularHomologyFunctorZeroOfTotallyDisconnectedSpace [CategoryWithHomology C] :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ fun _ : X ↦ R :=
  have : HasZeroObject C :=
    have := hasCoproducts_shrink.{0, w} (C := C)
    ⟨_, initialIsInitial.isZero⟩
  (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace C R X) ≪≫
    ChainComplex.alternatingConstHomologyZero _

end TotallyDisconnectedSpace

end AlgebraicTopology

