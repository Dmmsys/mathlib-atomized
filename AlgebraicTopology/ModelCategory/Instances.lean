/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations

/-!
# Consequences of model category axioms

In this file, we deduce basic properties of fibrations, cofibrations,
and weak equivalences from the axioms of model categories.

-/

public section


universe w v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable (C : Type u) [Category.{v} C]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
    [(cofibrations C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderRetracts] :
    (trivialCofibrations C).IsStableUnderRetracts := by
  dsimp [trivialCofibrations]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithWeakEquivalences C] [CategoryWithFibrations C]
    [(fibrations C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderRetracts] :
    (trivialFibrations C).IsStableUnderRetracts := by
  dsimp [trivialFibrations]
  infer_instance

section IsStableUnderComposition

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithCofibrations C] [(cofibrations C).IsStableUnderComposition]
    [hf : Cofibration f] [hg : Cofibration g] : Cofibration (f ≫ g) :=
  (cofibration_iff _).2 ((cofibrations C).comp_mem _ _ hf.mem hg.mem)
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithFibrations C] [(fibrations C).IsStableUnderComposition]
    [hf : Fibration f] [hg : Fibration g] : Fibration (f ≫ g) :=
  (fibration_iff _).2 ((fibrations C).comp_mem _ _ hf.mem hg.mem)
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CategoryWithWeakEquivalences C] [(weakEquivalences C).IsStableUnderComposition]
    [hf : WeakEquivalence f] [hg : WeakEquivalence g] : WeakEquivalence (f ≫ g) :=
  (weakEquivalence_iff _).2 ((weakEquivalences C).comp_mem _ _ hf.mem hg.mem)

end IsStableUnderComposition

variable [CategoryWithWeakEquivalences C]

section HasTwoOutOfThreeProperty

variable [(weakEquivalences C).HasTwoOutOfThreeProperty]
  {C} {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

/-
**HomotopicalAlgebra.weakEquivalence_of_postcomp** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra`。
形式化陈述：weakEquivalence_of_postcomp [hg : WeakEquivalence g] [hfg : WeakEquivalenc
e (f ≫ g)] : WeakEquivalence f
参数：f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopicalAlgebra.weakEquivalence_iff`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C…
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toHasOfPostcomp
Property`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Category
Theory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Ha…
-/
lemma weakEquivalence_of_postcomp
    [hg : WeakEquivalence g] [hfg : WeakEquivalence (f ≫ g)] :
    WeakEquivalence f := by
  rw [weakEquivalence_iff] at hg hfg ⊢
  exact of_postcomp _ _ _ hg hfg
/-
**HomotopicalAlgebra.weakEquivalence_of_precomp** 是 Mathlib 中的一个引理，位于命名空间 `Homot
opicalAlgebra`。
形式化陈述：weakEquivalence_of_precomp [hf : WeakEquivalence f] [hfg : WeakEquivalence
 (f ≫ g)] : WeakEquivalence g
参数：f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopicalAlgebra.weakEquivalence_iff`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C…
· 使用引理 `CategoryTheory.MorphismProperty.of_precomp`：of_precomp [W.HasOfPrecompPr
operty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f) (hfg : W (f ≫ g)) : W
 g
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toHasOfPrecompP
roperty`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryT
heory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Ha…
-/
lemma weakEquivalence_of_precomp
    [hf : WeakEquivalence f] [hfg : WeakEquivalence (f ≫ g)] :
    WeakEquivalence g := by
  rw [weakEquivalence_iff] at hf hfg ⊢
  exact of_precomp _ _ _ hf hfg
/-
**HomotopicalAlgebra.weakEquivalence_postcomp_iff** 是 Mathlib 中的一个引理，位于命名空间 `Hom
otopicalAlgebra`。
形式化陈述：weakEquivalence_postcomp_iff [WeakEquivalence g] : WeakEquivalence (f ≫ g)
 ↔ WeakEquivalence f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.weakEquivalence_of_postcomp`：weakEquivalence_of_postc
omp [hg : WeakEquivalence g] [hfg : WeakEquivalence (f ≫ g)] : WeakEquivalence f
· 使用定理 `HomotopicalAlgebra.instWeakEquivalenceCompOfIsStableUnderCompositionWeak
Equivalences`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {X Y Z : 
C} (f : X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : HomotopicalAlgebra.CategoryWithWeak…
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toIsStableUnder
Composition`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Is…
-/
lemma weakEquivalence_postcomp_iff [WeakEquivalence g] :
    WeakEquivalence (f ≫ g) ↔ WeakEquivalence f :=
  ⟨fun _ ↦ weakEquivalence_of_postcomp f g, fun _ ↦ inferInstance⟩
/-
**HomotopicalAlgebra.weakEquivalence_precomp_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra`。
形式化陈述：weakEquivalence_precomp_iff [WeakEquivalence f] : WeakEquivalence (f ≫ g) 
↔ WeakEquivalence g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.weakEquivalence_of_precomp`：weakEquivalence_of_precom
p [hf : WeakEquivalence f] [hfg : WeakEquivalence (f ≫ g)] : WeakEquivalence g
· 使用定理 `HomotopicalAlgebra.instWeakEquivalenceCompOfIsStableUnderCompositionWeak
Equivalences`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {X Y Z : 
C} (f : X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : HomotopicalAlgebra.CategoryWithWeak…
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toIsStableUnder
Composition`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Is…
-/
lemma weakEquivalence_precomp_iff [WeakEquivalence f] :
    WeakEquivalence (f ≫ g) ↔ WeakEquivalence g :=
  ⟨fun _ ↦ weakEquivalence_of_precomp f g, fun _ ↦ inferInstance⟩

variable {f g} {fg : X ⟶ Z}
/-
**HomotopicalAlgebra.weakEquivalence_of_postcomp_of_fac** 是 Mathlib 中的一个引理，位于命名空
间 `HomotopicalAlgebra`。
形式化陈述：weakEquivalence_of_postcomp_of_fac (fac : f ≫ g = fg) [WeakEquivalence g] 
[hfg : WeakEquivalence fg] : WeakEquivalence f
参数：fac : f ≫ g = fg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.weakEquivalence_of_postcomp`：weakEquivalence_of_postc
omp [hg : WeakEquivalence g] [hfg : WeakEquivalence (f ≫ g)] : WeakEquivalence f
-/
lemma weakEquivalence_of_postcomp_of_fac (fac : f ≫ g = fg)
    [WeakEquivalence g] [hfg : WeakEquivalence fg] :
    WeakEquivalence f := by
  subst fac
  exact weakEquivalence_of_postcomp f g
/-
**HomotopicalAlgebra.weakEquivalence_of_precomp_of_fac** 是 Mathlib 中的一个引理，位于命名空间
 `HomotopicalAlgebra`。
形式化陈述：weakEquivalence_of_precomp_of_fac (fac : f ≫ g = fg) [WeakEquivalence f] [
WeakEquivalence fg] : WeakEquivalence g
参数：fac : f ≫ g = fg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopicalAlgebra.weakEquivalence_of_precomp`：weakEquivalence_of_precom
p [hf : WeakEquivalence f] [hfg : WeakEquivalence (f ≫ g)] : WeakEquivalence g
-/
lemma weakEquivalence_of_precomp_of_fac (fac : f ≫ g = fg)
    [WeakEquivalence f] [WeakEquivalence fg] :
    WeakEquivalence g := by
  subst fac
  exact weakEquivalence_of_precomp f g

end HasTwoOutOfThreeProperty

variable [CategoryWithCofibrations C] [CategoryWithFibrations C]

section

variable [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]

/-
**HomotopicalAlgebra.fibrations_llp** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlgebr
a`。
形式化陈述：fibrations_llp : (fibrations C).llp = trivialCofibrations C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.llp_eq_of_wfs`：llp_eq_of_wfs : W₂.llp = 
W₁
-/
lemma fibrations_llp :
    (fibrations C).llp = trivialCofibrations C :=
  llp_eq_of_wfs _ _
/-
**HomotopicalAlgebra.trivialCofibrations_rlp** 是 Mathlib 中的一个引理，位于命名空间 `Homotopi
calAlgebra`。
形式化陈述：trivialCofibrations_rlp : (trivialCofibrations C).rlp = fibrations C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.rlp_eq_of_wfs`：rlp_eq_of_wfs : W₁.rlp = 
W₂
-/
lemma trivialCofibrations_rlp :
    (trivialCofibrations C).rlp = fibrations C :=
  rlp_eq_of_wfs _ _
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (trivialCofibrations C).IsStableUnderCobaseChange := by
  rw [← fibrations_llp]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fibrations C).IsStableUnderBaseChange := by
  rw [← trivialCofibrations_rlp]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (trivialCofibrations C).IsMultiplicative := by
  rw [← fibrations_llp]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fibrations C).IsMultiplicative := by
  rw [← trivialCofibrations_rlp]
  infer_instance

variable (J : Type w)
/-
**HomotopicalAlgebra.isStableUnderCoproductsOfShape_trivialCofibrations** 是 Math
lib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：isStableUnderCoproductsOfShape_trivialCofibrations : (trivialCofibrations 
C).IsStableUnderCoproductsOfShape J
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.fibrations_llp`：fibrations_llp : (fibrations C).llp =
 trivialCofibrations C
-/
instance isStableUnderCoproductsOfShape_trivialCofibrations :
    (trivialCofibrations C).IsStableUnderCoproductsOfShape J := by
  rw [← fibrations_llp]
  apply MorphismProperty.llp_isStableUnderCoproductsOfShape
/-
**HomotopicalAlgebra.isStableUnderProductsOfShape_fibrations** 是 Mathlib 中的一个实例，
位于命名空间 `HomotopicalAlgebra`。
形式化陈述：isStableUnderProductsOfShape_fibrations : (fibrations C).IsStableUnderProd
uctsOfShape J
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.trivialCofibrations_rlp`：trivialCofibrations_rlp : (t
rivialCofibrations C).rlp = fibrations C
-/
instance isStableUnderProductsOfShape_fibrations :
    (fibrations C).IsStableUnderProductsOfShape J := by
  rw [← trivialCofibrations_rlp]
  apply MorphismProperty.rlp_isStableUnderProductsOfShape

end

section

variable [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]

/-
**HomotopicalAlgebra.trivialFibrations_llp** 是 Mathlib 中的一个引理，位于命名空间 `Homotopica
lAlgebra`。
形式化陈述：trivialFibrations_llp : (trivialFibrations C).llp = cofibrations C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.llp_eq_of_wfs`：llp_eq_of_wfs : W₂.llp = 
W₁
-/
lemma trivialFibrations_llp :
    (trivialFibrations C).llp = cofibrations C :=
  llp_eq_of_wfs _ _
/-
**HomotopicalAlgebra.cofibrations_rlp** 是 Mathlib 中的一个引理，位于命名空间 `HomotopicalAlge
bra`。
形式化陈述：cofibrations_rlp : (cofibrations C).rlp = trivialFibrations C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.rlp_eq_of_wfs`：rlp_eq_of_wfs : W₁.rlp = 
W₂
-/
lemma cofibrations_rlp :
    (cofibrations C).rlp = trivialFibrations C :=
  rlp_eq_of_wfs _ _
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (cofibrations C).IsStableUnderCobaseChange := by
  rw [← trivialFibrations_llp]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (trivialFibrations C).IsStableUnderBaseChange := by
  rw [← cofibrations_rlp]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (cofibrations C).IsMultiplicative := by
  rw [← trivialFibrations_llp]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (trivialFibrations C).IsMultiplicative := by
  rw [← cofibrations_rlp]
  infer_instance


variable (J : Type w)
/-
**HomotopicalAlgebra.isStableUnderCoproductsOfShape_cofibrations** 是 Mathlib 中的一
个实例，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：isStableUnderCoproductsOfShape_cofibrations : (cofibrations C).IsStableUnd
erCoproductsOfShape J
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.trivialFibrations_llp`：trivialFibrations_llp : (trivi
alFibrations C).llp = cofibrations C
-/
instance isStableUnderCoproductsOfShape_cofibrations :
    (cofibrations C).IsStableUnderCoproductsOfShape J := by
  rw [← trivialFibrations_llp]
  apply MorphismProperty.llp_isStableUnderCoproductsOfShape
/-
**HomotopicalAlgebra.isStableUnderProductsOfShape_trivialFibrations** 是 Mathlib 
中的一个实例，位于命名空间 `HomotopicalAlgebra`。
形式化陈述：isStableUnderProductsOfShape_trivialFibrations : (trivialFibrations C).IsS
tableUnderProductsOfShape J
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopicalAlgebra.cofibrations_rlp`：cofibrations_rlp : (cofibrations C)
.rlp = trivialFibrations C
-/
instance isStableUnderProductsOfShape_trivialFibrations :
    (trivialFibrations C).IsStableUnderProductsOfShape J := by
  rw [← cofibrations_rlp]
  apply MorphismProperty.rlp_isStableUnderProductsOfShape

end

section Pullbacks

section

variable {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(cofibrations C).IsStableUnderCobaseChange] [hg : Cofibration g] :
    Cofibration (pushout.inl f g) := by
  rw [cofibration_iff] at hg ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g) hg
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(cofibrations C).IsStableUnderCobaseChange] [hf : Cofibration f] :
    Cofibration (pushout.inr f g) := by
  rw [cofibration_iff] at hf ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip hf
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(trivialCofibrations C).IsStableUnderCobaseChange]
    [Cofibration g] [WeakEquivalence g] : WeakEquivalence (pushout.inl f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g)
    (mem_trivialCofibrations g)).2
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(trivialCofibrations C).IsStableUnderCobaseChange]
    [Cofibration f] [WeakEquivalence f] : WeakEquivalence (pushout.inr f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip
    (mem_trivialCofibrations f)).2

end

section

variable {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(fibrations C).IsStableUnderBaseChange]
    [hf : Fibration f] : Fibration (pullback.snd f g) := by
  rw [fibration_iff] at hf ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g) hf
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(fibrations C).IsStableUnderBaseChange]
    [hg : Fibration g] : Fibration (pullback.fst f g) := by
  rw [fibration_iff] at hg ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip hg
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(trivialFibrations C).IsStableUnderBaseChange]
    [Fibration f] [WeakEquivalence f] : WeakEquivalence (pullback.snd f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g)
    (mem_trivialFibrations f)).2
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(trivialFibrations C).IsStableUnderBaseChange]
    [Fibration g] [WeakEquivalence g] : WeakEquivalence (pullback.fst f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip
    (mem_trivialFibrations g)).2

end

end Pullbacks

section Products

variable (J : Type w) {C J} {X Y : J → C} (f : ∀ i, X i ⟶ Y i)

section

variable [HasCoproduct X] [HasCoproduct Y] [h : ∀ i, Cofibration (f i)]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)] :
    Cofibration (Limits.Sigma.map f) := by
  simp only [cofibration_iff] at h ⊢
  exact MorphismProperty.colimMap _ (fun ⟨i⟩ ↦ h i)
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [∀ i, WeakEquivalence (f i)] :
    WeakEquivalence (Limits.Sigma.map f) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.colimMap (W := (trivialCofibrations C)) _
    (fun ⟨i⟩ ↦ mem_trivialCofibrations (f i))).2

end

section

variable [HasProduct X] [HasProduct Y] [h : ∀ i, Fibration (f i)]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)] :
    Fibration (Limits.Pi.map f) := by
  simp only [fibration_iff] at h ⊢
  exact MorphismProperty.limMap _ (fun ⟨i⟩ ↦ h i)
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]
    [∀ i, WeakEquivalence (f i)] :
    WeakEquivalence (Limits.Pi.map f) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.limMap (W := (trivialFibrations C)) _
    (fun ⟨i⟩ ↦ mem_trivialFibrations (f i))).2

end

end Products

section BinaryProducts

variable {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]
    [h₁ : Cofibration f₁] [h₂ : Cofibration f₂] [HasBinaryCoproduct X₁ X₂]
    [HasBinaryCoproduct Y₁ Y₂] : Cofibration (coprod.map f₁ f₂) := by
  rw [cofibration_iff] at h₁ h₂ ⊢
  apply MorphismProperty.colimMap
  rintro (_ | _) <;> assumption
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [h₁ : Fibration f₁] [h₂ : Fibration f₂] [HasBinaryProduct X₁ X₂]
    [HasBinaryProduct Y₁ Y₂] : Fibration (prod.map f₁ f₂) := by
  rw [fibration_iff] at h₁ h₂ ⊢
  apply MorphismProperty.limMap
  rintro (_ | _) <;> assumption

end BinaryProducts

section IsIso

variable {X Y : C} (f : X ⟶ Y)

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)] [IsIso f] :
    Cofibration f := by
  have := (fibrations C).llp_of_isIso f
  rw [fibrations_llp] at this
  simpa only [cofibration_iff] using this.1
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)] [IsIso f] :
    Fibration f := by
  have := (cofibrations C).rlp_of_isIso f
  rw [cofibrations_rlp] at this
  simpa only [fibration_iff] using this.1
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [(weakEquivalences C).IsStableUnderRetracts] [IsIso f] :
    WeakEquivalence f := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) f
  rw [weakEquivalence_iff]
  exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty h.fac) h.hi.2

end IsIso

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [(weakEquivalences C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderComposition] :
    (weakEquivalences C).IsMultiplicative where
  id_mem _ := by
    rw [← weakEquivalence_iff]
    infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [(weakEquivalences C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderComposition] :
    (weakEquivalences C).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ _ (_ : IsIso _) ↦ by
    rw [← weakEquivalence_iff]
    infer_instance)
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(weakEquivalences C).ContainsIdentities] (X : C) :
    WeakEquivalence (𝟙 X) := by
  rw [weakEquivalence_iff]
  apply id_mem

section MapFactorizationData

variable {X Y : C} (f : X ⟶ Y)

section

variable (h : MapFactorizationData (cofibrations C) (trivialFibrations C) f)

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Cofibration h.i := by
  simpa only [cofibration_iff] using h.hi
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fibration h.p := by
  simpa only [fibration_iff] using h.hp.1
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WeakEquivalence h.p := by
  simpa only [weakEquivalence_iff] using h.hp.2

end

section

variable (h : MapFactorizationData (trivialCofibrations C) (fibrations C) f)

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Cofibration h.i := by
  simpa only [cofibration_iff] using h.hi.1
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WeakEquivalence h.i := by
  simpa only [weakEquivalence_iff] using h.hi.2
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fibration h.p := by
  simpa only [fibration_iff] using h.hp

end

end MapFactorizationData

end HomotopicalAlgebra

