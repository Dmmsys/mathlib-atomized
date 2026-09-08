/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Monoidal.Braided.PushoutObjObj
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Inner anodyne extensions and pushout-products, inner fibrations and pullbacks

This file is mirrored from `SSet/AnodyneExtensions/PushoutProduct`.

The main result in this file is that if `i : X₁ ⟶ Y₁` is a monomorphism in `SSet`
and `j : X₂ ⟶ Y₂` is an inner anodyne extension, then the pushout-product
of `i` and `j` is an inner anodyne extension
(`SSet.innerAnodyneExtensions_pushoutObjObjι`). This is closely related to the lemma
`SSet.innerFibration_pullbackObjObjπ` which says that if `i : X₁ ⟶ Y₁` is a monomorphism
and `p : E ⟶ B` is an inner fibration, then the canonical morphism
from `Y₁ ⟶[SSet] E` to the pullback of `X₁ ⟶[SSet] E` and `Y₁ ⟶[SSet] B`
over `X₁ ⟶[SSet] B` is also an inner fibration. In particular, if `A : SSet`
and `X` is a quasi-category, then the internal hom `A ⟶[SSet] X` is also a quasi-category.

For implementation details, see `SSet/AnodyneExtensions/PushoutProduct`.

## References

- [Jack McKoen, *A Formalization of Functor Quasi-Categories in Lean 4*][mckoen2026]

## Note

The result that the internal hom into a quasi-category is also a quasi-category was first
formalized by Jack McKoen for his master's thesis, following an approach outlined on
Kerodon (https://kerodon.net/tag/0066). Specifically, this approach hinges on the lemma
https://kerodon.net/tag/0079 which is avoided in the mathlib implementation.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Simplicial HomotopicalAlgebra Limits

namespace SSet

namespace prodStdSimplex

/-
**SSet.prodStdSimplex.innerAnodyneExtensions_unionProd_** 是 Mathlib 中的一个引理，位于命名空
间 `SSet.prodStdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma innerAnodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (h0 : 0 < k)
    (hn : k < Fin.last (m + 1)) (n : ℕ) :
    innerAnodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι := by
  obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hn)
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero
    (Fin.ne_zero_of_lt (show 0 < k from Fin.val_pos_iff.mp h0))
  exact (pairing k.castSucc.succ n).innerAnodyneExtensions

end prodStdSimplex

section

variable {X₁ X₂ Y₁ Y₂ E B : SSet.{u}}
  {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂} {p : E ⟶ B}

/-
**SSet.innerFibration_pullbackObjObj** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma innerFibration_pullbackObjObjπ [Mono i] [InnerFibration p]
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    InnerFibration sq₁₃.π := by
  rw [innerFibration_iff]
  intro _ _ _ ⟨k, h0, hn⟩
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i Λ[_, k].ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂]
  suffices innerAnodyneExtensions sq₁₂.ι from
    this _ (by rwa [← innerFibration_iff])
  intro E B p hp
  rw [HasLiftingProperty.iff_of_arrow_iso_left
    (show Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂.flipTensor.ι from
      Arrow.isoMk (Iso.refl _) (β_ _ _))]
  let sq₁₃' := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom Λ[_, k].ι p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃']
  suffices (MorphismProperty.monomorphisms _).rlp sq₁₃'.π from this _ inferInstance
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Subcomplex.unionProd.pushoutObjObj.{u} _ _),
    Subcomplex.unionProd.pushoutObjObj_ι]
  exact prodStdSimplex.innerAnodyneExtensions_unionProd_ι k h0 hn n _ hp
/-
**SSet.innerAnodyneExtensions_pushoutObjObj** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma innerAnodyneExtensions_pushoutObjObjι
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono i] (hj : innerAnodyneExtensions j) :
    innerAnodyneExtensions sq₁₂.ι := by
  intro E B p hp
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  apply hj
  rw [← innerFibration_iff] at hp ⊢
  exact innerFibration_pullbackObjObjπ sq₁₃
/-
**SSet.innerAnodyneExtensions_pushoutObjObj** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma innerAnodyneExtensions_pushoutObjObjι'
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j)
    [Mono j] (hi : innerAnodyneExtensions i) :
    innerAnodyneExtensions sq₁₂.ι := by
  refine (innerAnodyneExtensions.arrow_mk_iso_iff ?_).1
    (innerAnodyneExtensions_pushoutObjObjι sq₁₂.flipTensor hi)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _)

end

/-
**SSet.innerAnodyneExtensions_unionProd_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma innerAnodyneExtensions_unionProd_ι
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hB : innerAnodyneExtensions B.ι) :
    innerAnodyneExtensions (A.unionProd B).ι :=
  innerAnodyneExtensions_pushoutObjObjι (Subcomplex.unionProd.pushoutObjObj A B) hB
/-
**SSet.innerAnodyneExtensions_unionProd_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma innerAnodyneExtensions_unionProd_ι'
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hA : innerAnodyneExtensions A.ι) :
    innerAnodyneExtensions (A.unionProd B).ι :=
  innerAnodyneExtensions_pushoutObjObjι' (Subcomplex.unionProd.pushoutObjObj A B) hA
/-
**SSet.innerAnodyneExtensions.whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `SSet.inner
AnodyneExtensions`。
形式化陈述：∀ {X Y : _root_.SSet} {f : X ⟶ Y},   SSet.innerAnodyneExtensions f →     ∀
 (Z : _root_.SSet), SSet.innerAnodyneExtensions (CategoryTheory.MonoidalCategory
Struct.whiskerRight f Z)
参数：Z : _root_.SSet；CategoryTheory.MonoidalCategoryStruct.whiskerRight f Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.innerAnodyneExtensions_pushoutObjObjι'`：innerAnodyneExtensions_push
outObjObjι' (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono j] (hi : innerAno
dyneExtensions i) : innerAnodyneE…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.SimplicialObject.instHasColimits`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C],   Categ
oryTheory.Limits.HasColimits (Categor…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Functor.Monoidal.instPreservesColimitsOfShapeTensorLeftOf
HasColimitsOfShape`：∀ {J : Type u_1} {C : Type u_2} [inst : CategoryTheory.Categ
ory.{v_1, u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C] [inst_2 : Ca
…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instPreservesColimitsTensorLeft`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] (A
 : C)   [CategoryTheory.Closed A], C…
· 使用定理 `CategoryTheory.Initial.mono_to`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   [inst_2
 : CategoryTheory.Li…
-/
lemma innerAnodyneExtensions.whiskerRight
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : innerAnodyneExtensions f) (Z : SSet.{u}) :
    innerAnodyneExtensions (f ▷ Z) :=
  innerAnodyneExtensions_pushoutObjObjι'
    (.ofIsInitialRight (curriedTensor _) f (initial.to Z) initialIsInitial) hf
/-
**SSet.innerAnodyneExtensions.whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `SSet.innerA
nodyneExtensions`。
形式化陈述：∀ {X Y : _root_.SSet} {f : X ⟶ Y},   SSet.innerAnodyneExtensions f →     ∀
 (Z : _root_.SSet), SSet.innerAnodyneExtensions (CategoryTheory.MonoidalCategory
Struct.whiskerLeft Z f)
参数：Z : _root_.SSet；CategoryTheory.MonoidalCategoryStruct.whiskerLeft Z f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.innerAnodyneExtensions_pushoutObjObjι`：innerAnodyneExtensions_pusho
utObjObjι (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono i] (hj : innerAnody
neExtensions j) : innerAnodyneEx…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.SimplicialObject.instHasColimits`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C],   Categ
oryTheory.Limits.HasColimits (Categor…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.ihom.instIsLeftAdjointTensorRightOfClosed`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Monoid
alCategory C]   [CategoryTheory.BraidedCategor…
· 使用定理 `CategoryTheory.Initial.mono_to`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   [inst_2
 : CategoryTheory.Li…
-/
lemma innerAnodyneExtensions.whiskerLeft
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : innerAnodyneExtensions f) (Z : SSet.{u}) :
    innerAnodyneExtensions (Z ◁ f) :=
  innerAnodyneExtensions_pushoutObjObjι
    (.ofIsInitialLeft (curriedTensor _) (initial.to Z) f initialIsInitial) hf
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E B X : SSet.{u}} (p : E ⟶ B) [InnerFibration p] :
    InnerFibration ((ihom X).map p) :=
  innerFibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsInitial
    MonoidalClosed.internalHom (initial.to X) p initialIsInitial)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (X : SSet.{u}) [Quasicategory X] :
    InnerFibration ((MonoidalClosed.pre i).app X) :=
  innerFibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsTerminal
    MonoidalClosed.internalHom i (terminal.from X) terminalIsTerminal)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : SSet.{u}) : Quasicategory ((ihom A).obj (⊤_ _)) := by
  have : IsIso (terminal.from ((ihom A).obj (⊤_ _))) :=
    isIso_of_isTerminal (IsTerminal.isTerminalObj _ _ terminalIsTerminal)
      terminalIsTerminal _
  infer_instance
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A X : SSet.{u}} [Quasicategory X] : Quasicategory ((ihom A).obj X) :=
  quasicategory_of_innerFibration ((ihom A).map (terminal.from X))

end SSet

