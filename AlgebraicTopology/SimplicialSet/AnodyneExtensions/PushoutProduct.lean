/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Monoidal.Braided.PushoutObjObj
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Anodyne extensions and pushout-products, fibrations and pullbacks

The main result in this file is that if `i : X₁ ⟶ Y₁` is a monomorphism in `SSet`
and `j : X₂ ⟶ Y₂` is an anodyne extension, then the map from the pushout-product
of `i` and `j` into `Y₁ ⊗ Y₂` is an anodyne extension
(`SSet.anodyneExtensions_pushoutObjObjι`). This is closely related to the lemma
`SSet.fibration_pullbackObjObjπ` which says that if `i : X₁ ⟶ Y₁` is a monomorphism
and `p : E ⟶ B` is a fibration, then the canonical morphism
from `Y₁ ⟶[SSet] E` to the pullback of `X₁ ⟶[SSet] E` and `Y₁ ⟶[SSet] B`
over `X₁ ⟶[SSet] B` is also a fibration. In particular, if `A : SSet`
and `X` is a Kan complex, then the internal hom `A ⟶[SSet] X` is also a Kan complex.

Besides abstract arguments involving parametrized adjunctions and lifting properties,
the proof relies on two facts:
* the case `i : ∂Δ[n] ⟶ Δ[n]` and `j : Λ[m, k] ⟶ Δ[m]` which was obtained
in the file `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/UnionProd.lean`
* the fact that a morphism has the right lifting property with respect to
all monomorphisms iff it has the right lifting property with respect
to morphisms of the form `∂Δ[n] ⟶ Δ[n]` (see `SSet.rlp_monomorphisms`
in the file `Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean`),
which follows from the fact that any monomorphism is a relative cell complex with
basic cells of the form `∂Δ[n] ⟶ Δ[n]`, see
the file `Mathlib/AlgebraicTopology/SimplicialSet/Skeleton.lean`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Simplicial HomotopicalAlgebra Limits

namespace SSet

open modelCategoryQuillen

namespace prodStdSimplex

/-
**SSet.prodStdSimplex.strongAnodyneExtensions_unionProd_** 是 Mathlib 中的一个引理，位于命名
空间 `SSet.prodStdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma strongAnodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    strongAnodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι :=
  (pairing k n).strongAnodyneExtensions
/-
**SSet.prodStdSimplex.anodyneExtensions_unionProd_** 是 Mathlib 中的一个引理，位于命名空间 `SS
et.prodStdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma anodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2)) (n : ℕ) :
    anodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι :=
  (pairing k n).anodyneExtensions

end prodStdSimplex

section

variable {X₁ X₂ Y₁ Y₂ E B : SSet.{u}}
  {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂} {p : E ⟶ B}

/-
**SSet.fibration_pullbackObjObj** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fibration_pullbackObjObjπ [Mono i] [Fibration p]
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    Fibration sq₁₃.π := by
  rw [fibration_iff]
  intro _ _ _ h
  simp only [J, MorphismProperty.iSup_iff] at h
  obtain ⟨m, ⟨k⟩⟩ := h
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i Λ[m + 1, k].ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂]
  suffices anodyneExtensions sq₁₂.ι from
    this _ (by rwa [← HomotopicalAlgebra.fibration_iff])
  intro E B p hp
  rw [HasLiftingProperty.iff_of_arrow_iso_left
    (show Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂.flipTensor.ι from
      Arrow.isoMk (Iso.refl _) (β_ _ _))]
  let sq₁₃' := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom Λ[m + 1, k].ι p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃']
  suffices (MorphismProperty.monomorphisms _).rlp sq₁₃'.π from this _ inferInstance
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Subcomplex.unionProd.pushoutObjObj.{u} _ _),
    Subcomplex.unionProd.pushoutObjObj_ι]
  exact prodStdSimplex.anodyneExtensions_unionProd_ι _ _ _ hp
/-
**SSet.anodyneExtensions_pushoutObjObj** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma anodyneExtensions_pushoutObjObjι
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono i] (hj : anodyneExtensions j) :
    anodyneExtensions sq₁₂.ι := by
  intro E B p hp
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  apply hj
  rw [← HomotopicalAlgebra.fibration_iff] at hp ⊢
  exact fibration_pullbackObjObjπ sq₁₃
/-
**SSet.anodyneExtensions_pushoutObjObj** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma anodyneExtensions_pushoutObjObjι'
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j)
    [Mono j] (hi : anodyneExtensions i) :
    anodyneExtensions sq₁₂.ι := by
  refine (anodyneExtensions.arrow_mk_iso_iff ?_).1
    (anodyneExtensions_pushoutObjObjι sq₁₂.flipTensor hi)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _)

end

/-
**SSet.anodyneExtensions_unionProd_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma anodyneExtensions_unionProd_ι
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hB : anodyneExtensions B.ι) :
    anodyneExtensions (A.unionProd B).ι :=
  anodyneExtensions_pushoutObjObjι (Subcomplex.unionProd.pushoutObjObj A B) hB
/-
**SSet.anodyneExtensions_unionProd_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma anodyneExtensions_unionProd_ι'
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hA : anodyneExtensions A.ι) :
    anodyneExtensions (A.unionProd B).ι :=
  anodyneExtensions_pushoutObjObjι' (Subcomplex.unionProd.pushoutObjObj A B) hA
/-
**SSet.anodyneExtensions.whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `SSet.anodyneExt
ensions`。
形式化陈述：∀ {X Y : _root_.SSet} {f : X ⟶ Y},   SSet.anodyneExtensions f →     ∀ (Z :
 _root_.SSet), SSet.anodyneExtensions (CategoryTheory.MonoidalCategoryStruct.whi
skerRight f Z)
参数：Z : _root_.SSet；CategoryTheory.MonoidalCategoryStruct.whiskerRight f Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.anodyneExtensions_pushoutObjObjι'`：anodyneExtensions_pushoutObjObjι
' (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono j] (hi : anodyneExtensions 
i) : anodyneExtensions sq₁₂.…
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
lemma anodyneExtensions.whiskerRight
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : anodyneExtensions f) (Z : SSet.{u}) :
    anodyneExtensions (f ▷ Z) :=
  anodyneExtensions_pushoutObjObjι'
    (.ofIsInitialRight (curriedTensor _) f (initial.to Z) initialIsInitial) hf
/-
**SSet.anodyneExtensions.whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `SSet.anodyneExte
nsions`。
形式化陈述：∀ {X Y : _root_.SSet} {f : X ⟶ Y},   SSet.anodyneExtensions f →     ∀ (Z :
 _root_.SSet), SSet.anodyneExtensions (CategoryTheory.MonoidalCategoryStruct.whi
skerLeft Z f)
参数：Z : _root_.SSet；CategoryTheory.MonoidalCategoryStruct.whiskerLeft Z f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.anodyneExtensions_pushoutObjObjι`：anodyneExtensions_pushoutObjObjι 
(sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono i] (hj : anodyneExtensions j)
 : anodyneExtensions sq₁₂.ι
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
lemma anodyneExtensions.whiskerLeft
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : anodyneExtensions f) (Z : SSet.{u}) :
    anodyneExtensions (Z ◁ f) :=
  anodyneExtensions_pushoutObjObjι
    (.ofIsInitialLeft (curriedTensor _) (initial.to Z) f initialIsInitial) hf
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E B X : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    Fibration ((ihom X).map p) :=
  fibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsInitial
    MonoidalClosed.internalHom (initial.to X) p initialIsInitial)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (X : SSet.{u}) [KanComplex X] :
    Fibration ((MonoidalClosed.pre i).app X) :=
  fibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsTerminal
    MonoidalClosed.internalHom i (terminal.from X) terminalIsTerminal)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : SSet.{u}) : KanComplex ((ihom A).obj (⊤_ _)) := by
  have : IsIso (terminal.from ((ihom A).obj (⊤_ _))) :=
    isIso_of_isTerminal (IsTerminal.isTerminalObj _ _ terminalIsTerminal)
      terminalIsTerminal _
  infer_instance
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A X : SSet.{u}} [KanComplex X] : KanComplex ((ihom A).obj X) :=
  isFibrant_of_fibration ((ihom A).map (terminal.from X))

end SSet

