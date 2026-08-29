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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithWeakEquivalences
  signature: C] [CategoryWithCofibrations C]
  body: by
  dsimp [trivialCofibrations]
  infer_instance

中文:
实例 [带弱等价范畴
  签名: C] [带余纤维化范畴 C]
  定义体: by
  dsimp [trivialCofibrations]
  infer_instance

Depends on / 依赖: infer_instance, trivialCofibrations
-/
instance [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
    [(cofibrations C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderRetracts] :
    (trivialCofibrations C).IsStableUnderRetracts := by
  dsimp [trivialCofibrations]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithWeakEquivalences
  signature: C] [CategoryWithFibrations C]
  body: by
  dsimp [trivialFibrations]
  infer_instance

中文:
实例 [带弱等价范畴
  签名: C] [带纤维化范畴 C]
  定义体: by
  dsimp [trivialFibrations]
  infer_instance

Depends on / 依赖: infer_instance, trivialFibrations
-/
instance [CategoryWithWeakEquivalences C] [CategoryWithFibrations C]
    [(fibrations C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderRetracts] :
    (trivialFibrations C).IsStableUnderRetracts := by
  dsimp [trivialFibrations]
  infer_instance

section IsStableUnderComposition

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithCofibrations
  signature: C] [(cofibrations C).IsStableUnderComposition]
  body: (cofibration_iff _).2 ((cofibrations C).comp_mem _ _ hf.mem hg.mem)

中文:
实例 [带余纤维化范畴
  签名: C] [(cofibrations C).是StableUnderComposition]
  定义体: (cofibration_iff _).2 ((cofibrations C).comp_mem _ _ hf.mem hg.mem)

Depends on / 依赖: cofibration_iff, cofibrations, comp_mem, hf.mem, hg.mem
-/
instance [CategoryWithCofibrations C] [(cofibrations C).IsStableUnderComposition]
    [hf : Cofibration f] [hg : Cofibration g] : Cofibration (f ≫ g) :=
  (cofibration_iff _).2 ((cofibrations C).comp_mem _ _ hf.mem hg.mem)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithFibrations
  signature: C] [(fibrations C).IsStableUnderComposition]
  body: (fibration_iff _).2 ((fibrations C).comp_mem _ _ hf.mem hg.mem)

中文:
实例 [带纤维化范畴
  签名: C] [(fibrations C).是StableUnderComposition]
  定义体: (fibration_iff _).2 ((fibrations C).comp_mem _ _ hf.mem hg.mem)

Depends on / 依赖: comp_mem, fibration_iff, fibrations, hf.mem, hg.mem
-/
instance [CategoryWithFibrations C] [(fibrations C).IsStableUnderComposition]
    [hf : Fibration f] [hg : Fibration g] : Fibration (f ≫ g) :=
  (fibration_iff _).2 ((fibrations C).comp_mem _ _ hf.mem hg.mem)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithWeakEquivalences
  signature: C] [(weakEquivalences C).IsStableUnderComposition]
  body: (weakEquivalence_iff _).2 ((weakEquivalences C).comp_mem _ _ hf.mem hg.mem)

中文:
实例 [带弱等价范畴
  签名: C] [(weakEquivalences C).是StableUnderComposition]
  定义体: (weakEquivalence_iff _).2 ((weakEquivalences C).comp_mem _ _ hf.mem hg.mem)

Depends on / 依赖: comp_mem, hf.mem, hg.mem, weakEquivalence_iff, weakEquivalences
-/
instance [CategoryWithWeakEquivalences C] [(weakEquivalences C).IsStableUnderComposition]
    [hf : WeakEquivalence f] [hg : WeakEquivalence g] : WeakEquivalence (f ≫ g) :=
  (weakEquivalence_iff _).2 ((weakEquivalences C).comp_mem _ _ hf.mem hg.mem)

end IsStableUnderComposition

variable [CategoryWithWeakEquivalences C]

section HasTwoOutOfThreeProperty

variable [(weakEquivalences C).HasTwoOutOfThreeProperty]
  {C} {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

/--
lemma `weakEquivalence_of_postcomp` / 引理 `weakEquivalence_of_postcomp`

English:
lemma weakEquivalence_of_postcomp
  proof: by
  rw [weakEquivalence_iff] at hg hfg ⊢
  exact of_postcomp _ _ _ hg hfg

中文:
引理 weakEquivalence_of_postcomp
  证明: by
  rw [weakEquivalence_iff] at hg hfg ⊢
  exact of_postcomp _ _ _ hg hfg

Depends on / 依赖: of_postcomp, weakEquivalence_iff
-/
lemma weakEquivalence_of_postcomp
    [hg : WeakEquivalence g] [hfg : WeakEquivalence (f ≫ g)] :
    WeakEquivalence f := by
  rw [weakEquivalence_iff] at hg hfg ⊢
  exact of_postcomp _ _ _ hg hfg

/--
lemma `weakEquivalence_of_precomp` / 引理 `weakEquivalence_of_precomp`

English:
lemma weakEquivalence_of_precomp
  proof: by
  rw [weakEquivalence_iff] at hf hfg ⊢
  exact of_precomp _ _ _ hf hfg

中文:
引理 weakEquivalence_of_precomp
  证明: by
  rw [weakEquivalence_iff] at hf hfg ⊢
  exact of_precomp _ _ _ hf hfg

Depends on / 依赖: of_precomp, weakEquivalence_iff
-/
lemma weakEquivalence_of_precomp
    [hf : WeakEquivalence f] [hfg : WeakEquivalence (f ≫ g)] :
    WeakEquivalence g := by
  rw [weakEquivalence_iff] at hf hfg ⊢
  exact of_precomp _ _ _ hf hfg

/--
lemma `weakEquivalence_postcomp_iff` / 引理 `weakEquivalence_postcomp_iff`

English:
lemma weakEquivalence_postcomp_iff
  given: [WeakEquivalence g]
  proof: ⟨fun _ => weakEquivalence_of_postcomp f g, fun _ => inferInstance⟩

中文:
引理 weakEquivalence_postcomp_iff
  条件: [弱等价 g]
  证明: ⟨fun _ => weakEquivalence_of_postcomp f g, fun _ => inferInstance⟩

Depends on / 依赖: weakEquivalence_of_postcomp
-/
lemma weakEquivalence_postcomp_iff [WeakEquivalence g] :
    WeakEquivalence (f ≫ g) ↔ WeakEquivalence f :=
  ⟨fun _ => weakEquivalence_of_postcomp f g, fun _ => inferInstance⟩

/--
lemma `weakEquivalence_precomp_iff` / 引理 `weakEquivalence_precomp_iff`

English:
lemma weakEquivalence_precomp_iff
  given: [WeakEquivalence f]
  proof: ⟨fun _ => weakEquivalence_of_precomp f g, fun _ => inferInstance⟩

中文:
引理 weakEquivalence_precomp_iff
  条件: [弱等价 f]
  证明: ⟨fun _ => weakEquivalence_of_precomp f g, fun _ => inferInstance⟩

Depends on / 依赖: weakEquivalence_of_precomp
-/
lemma weakEquivalence_precomp_iff [WeakEquivalence f] :
    WeakEquivalence (f ≫ g) ↔ WeakEquivalence g :=
  ⟨fun _ => weakEquivalence_of_precomp f g, fun _ => inferInstance⟩

variable {f g} {fg : X ⟶ Z}

/--
lemma `weakEquivalence_of_postcomp_of_fac` / 引理 `weakEquivalence_of_postcomp_of_fac`

English:
lemma weakEquivalence_of_postcomp_of_fac
  statement: (fac : f ≫ g = fg)
  proof: by
  subst fac
  exact weakEquivalence_of_postcomp f g

中文:
引理 weakEquivalence_of_postcomp_of_fac
  结论: (fac : f ≫ g = fg)
  证明: by
  subst fac
  exact weakEquivalence_of_postcomp f g

Depends on / 依赖: weakEquivalence_of_postcomp
-/
lemma weakEquivalence_of_postcomp_of_fac (fac : f ≫ g = fg)
    [WeakEquivalence g] [hfg : WeakEquivalence fg] :
    WeakEquivalence f := by
  subst fac
  exact weakEquivalence_of_postcomp f g

/--
lemma `weakEquivalence_of_precomp_of_fac` / 引理 `weakEquivalence_of_precomp_of_fac`

English:
lemma weakEquivalence_of_precomp_of_fac
  statement: (fac : f ≫ g = fg)
  proof: by
  subst fac
  exact weakEquivalence_of_precomp f g

中文:
引理 weakEquivalence_of_precomp_of_fac
  结论: (fac : f ≫ g = fg)
  证明: by
  subst fac
  exact weakEquivalence_of_precomp f g

Depends on / 依赖: weakEquivalence_of_precomp
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

/--
lemma `fibrations_llp` / 引理 `fibrations_llp`

English:
lemma fibrations_llp
  proof: llp_eq_of_wfs _ _

中文:
引理 fibrations_llp
  证明: llp_eq_of_wfs _ _

Depends on / 依赖: llp_eq_of_wfs
-/
lemma fibrations_llp :
    (fibrations C).llp = trivialCofibrations C :=
  llp_eq_of_wfs _ _

/--
lemma `trivialCofibrations_rlp` / 引理 `trivialCofibrations_rlp`

English:
lemma trivialCofibrations_rlp
  proof: rlp_eq_of_wfs _ _

中文:
引理 trivialCofibrations_rlp
  证明: rlp_eq_of_wfs _ _

Depends on / 依赖: rlp_eq_of_wfs
-/
lemma trivialCofibrations_rlp :
    (trivialCofibrations C).rlp = fibrations C :=
  rlp_eq_of_wfs _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (trivialCofibrations C).IsStableUnderCobaseChange
  body: by
  rw [← fibrations_llp]
  infer_instance

中文:
实例 :
  签名: (trivialCofibrations C).是StableUnderCobaseChange
  定义体: by
  rw [← fibrations_llp]
  infer_instance

Depends on / 依赖: fibrations_llp, infer_instance
-/
instance : (trivialCofibrations C).IsStableUnderCobaseChange := by
  rw [← fibrations_llp]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fibrations C).IsStableUnderBaseChange
  body: by
  rw [← trivialCofibrations_rlp]
  infer_instance

中文:
实例 :
  签名: (fibrations C).是StableUnderBaseChange
  定义体: by
  rw [← trivialCofibrations_rlp]
  infer_instance

Depends on / 依赖: infer_instance, trivialCofibrations_rlp
-/
instance : (fibrations C).IsStableUnderBaseChange := by
  rw [← trivialCofibrations_rlp]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (trivialCofibrations C).IsMultiplicative
  body: by
  rw [← fibrations_llp]
  infer_instance

中文:
实例 :
  签名: (trivialCofibrations C).是Multiplicative
  定义体: by
  rw [← fibrations_llp]
  infer_instance

Depends on / 依赖: fibrations_llp, infer_instance
-/
instance : (trivialCofibrations C).IsMultiplicative := by
  rw [← fibrations_llp]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fibrations C).IsMultiplicative
  body: by
  rw [← trivialCofibrations_rlp]
  infer_instance

中文:
实例 :
  签名: (fibrations C).是Multiplicative
  定义体: by
  rw [← trivialCofibrations_rlp]
  infer_instance

Depends on / 依赖: infer_instance, trivialCofibrations_rlp
-/
instance : (fibrations C).IsMultiplicative := by
  rw [← trivialCofibrations_rlp]
  infer_instance

variable (J : Type w)

/--
Instance `isStableUnderCoproductsOfShape_trivialCofibrations` / 实例 `isStableUnderCoproductsOfShape_trivialCofibrations`

English:
instance isStableUnderCoproductsOfShape_trivialCofibrations
  signature: :
  body: by
  rw [← fibrations_llp]
  apply MorphismProperty.llp_isStableUnderCoproductsOfShape

中文:
实例 isStableUnderCoproductsOfShape_trivialCofibrations
  签名: :
  定义体: by
  rw [← fibrations_llp]
  apply MorphismProperty.llp_isStableUnderCoproductsOfShape

Depends on / 依赖: MorphismProperty, MorphismProperty.llp_isStableUnderCoproductsOfShape, fibrations_llp, llp_isStableUnderCoproductsOfShape
-/
instance isStableUnderCoproductsOfShape_trivialCofibrations :
    (trivialCofibrations C).IsStableUnderCoproductsOfShape J := by
  rw [← fibrations_llp]
  apply MorphismProperty.llp_isStableUnderCoproductsOfShape

/--
Instance `isStableUnderProductsOfShape_fibrations` / 实例 `isStableUnderProductsOfShape_fibrations`

English:
instance isStableUnderProductsOfShape_fibrations
  signature: :
  body: by
  rw [← trivialCofibrations_rlp]
  apply MorphismProperty.rlp_isStableUnderProductsOfShape

中文:
实例 isStableUnderProductsOfShape_fibrations
  签名: :
  定义体: by
  rw [← trivialCofibrations_rlp]
  apply MorphismProperty.rlp_isStableUnderProductsOfShape

Depends on / 依赖: MorphismProperty, MorphismProperty.rlp_isStableUnderProductsOfShape, rlp_isStableUnderProductsOfShape, trivialCofibrations_rlp
-/
instance isStableUnderProductsOfShape_fibrations :
    (fibrations C).IsStableUnderProductsOfShape J := by
  rw [← trivialCofibrations_rlp]
  apply MorphismProperty.rlp_isStableUnderProductsOfShape

end

section

variable [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]

/--
lemma `trivialFibrations_llp` / 引理 `trivialFibrations_llp`

English:
lemma trivialFibrations_llp
  proof: llp_eq_of_wfs _ _

中文:
引理 trivialFibrations_llp
  证明: llp_eq_of_wfs _ _

Depends on / 依赖: llp_eq_of_wfs
-/
lemma trivialFibrations_llp :
    (trivialFibrations C).llp = cofibrations C :=
  llp_eq_of_wfs _ _

/--
lemma `cofibrations_rlp` / 引理 `cofibrations_rlp`

English:
lemma cofibrations_rlp
  proof: rlp_eq_of_wfs _ _

中文:
引理 cofibrations_rlp
  证明: rlp_eq_of_wfs _ _

Depends on / 依赖: rlp_eq_of_wfs
-/
lemma cofibrations_rlp :
    (cofibrations C).rlp = trivialFibrations C :=
  rlp_eq_of_wfs _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (cofibrations C).IsStableUnderCobaseChange
  body: by
  rw [← trivialFibrations_llp]
  infer_instance

中文:
实例 :
  签名: (cofibrations C).是StableUnderCobaseChange
  定义体: by
  rw [← trivialFibrations_llp]
  infer_instance

Depends on / 依赖: infer_instance, trivialFibrations_llp
-/
instance : (cofibrations C).IsStableUnderCobaseChange := by
  rw [← trivialFibrations_llp]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (trivialFibrations C).IsStableUnderBaseChange
  body: by
  rw [← cofibrations_rlp]
  infer_instance

中文:
实例 :
  签名: (trivialFibrations C).是StableUnderBaseChange
  定义体: by
  rw [← cofibrations_rlp]
  infer_instance

Depends on / 依赖: cofibrations_rlp, infer_instance
-/
instance : (trivialFibrations C).IsStableUnderBaseChange := by
  rw [← cofibrations_rlp]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (cofibrations C).IsMultiplicative
  body: by
  rw [← trivialFibrations_llp]
  infer_instance

中文:
实例 :
  签名: (cofibrations C).是Multiplicative
  定义体: by
  rw [← trivialFibrations_llp]
  infer_instance

Depends on / 依赖: infer_instance, trivialFibrations_llp
-/
instance : (cofibrations C).IsMultiplicative := by
  rw [← trivialFibrations_llp]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (trivialFibrations C).IsMultiplicative
  body: by
  rw [← cofibrations_rlp]
  infer_instance

中文:
实例 :
  签名: (trivialFibrations C).是Multiplicative
  定义体: by
  rw [← cofibrations_rlp]
  infer_instance

Depends on / 依赖: cofibrations_rlp, infer_instance
-/
instance : (trivialFibrations C).IsMultiplicative := by
  rw [← cofibrations_rlp]
  infer_instance


variable (J : Type w)

/--
Instance `isStableUnderCoproductsOfShape_cofibrations` / 实例 `isStableUnderCoproductsOfShape_cofibrations`

English:
instance isStableUnderCoproductsOfShape_cofibrations
  signature: :
  body: by
  rw [← trivialFibrations_llp]
  apply MorphismProperty.llp_isStableUnderCoproductsOfShape

中文:
实例 isStableUnderCoproductsOfShape_cofibrations
  签名: :
  定义体: by
  rw [← trivialFibrations_llp]
  apply MorphismProperty.llp_isStableUnderCoproductsOfShape

Depends on / 依赖: MorphismProperty, MorphismProperty.llp_isStableUnderCoproductsOfShape, llp_isStableUnderCoproductsOfShape, trivialFibrations_llp
-/
instance isStableUnderCoproductsOfShape_cofibrations :
    (cofibrations C).IsStableUnderCoproductsOfShape J := by
  rw [← trivialFibrations_llp]
  apply MorphismProperty.llp_isStableUnderCoproductsOfShape

/--
Instance `isStableUnderProductsOfShape_trivialFibrations` / 实例 `isStableUnderProductsOfShape_trivialFibrations`

English:
instance isStableUnderProductsOfShape_trivialFibrations
  signature: :
  body: by
  rw [← cofibrations_rlp]
  apply MorphismProperty.rlp_isStableUnderProductsOfShape

中文:
实例 isStableUnderProductsOfShape_trivialFibrations
  签名: :
  定义体: by
  rw [← cofibrations_rlp]
  apply MorphismProperty.rlp_isStableUnderProductsOfShape

Depends on / 依赖: MorphismProperty, MorphismProperty.rlp_isStableUnderProductsOfShape, cofibrations_rlp, rlp_isStableUnderProductsOfShape
-/
instance isStableUnderProductsOfShape_trivialFibrations :
    (trivialFibrations C).IsStableUnderProductsOfShape J := by
  rw [← cofibrations_rlp]
  apply MorphismProperty.rlp_isStableUnderProductsOfShape

end

section Pullbacks

section

variable {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(cofibrations
  signature: C).IsStableUnderCobaseChange] [hg : Cofibration g] :
  body: by
  rw [cofibration_iff] at hg ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g) hg

中文:
实例 [(cofibrations
  签名: C).是StableUnderCobaseChange] [hg : 余纤维化 g] :
  定义体: by
  rw [cofibration_iff] at hg ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g) hg

Depends on / 依赖: IsPushout, IsPushout.of_hasPushout, MorphismProperty, MorphismProperty.of_isPushout, cofibration_iff, of_hasPushout, of_isPushout
-/
instance [(cofibrations C).IsStableUnderCobaseChange] [hg : Cofibration g] :
    Cofibration (pushout.inl f g) := by
  rw [cofibration_iff] at hg ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g) hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(cofibrations
  signature: C).IsStableUnderCobaseChange] [hf : Cofibration f] :
  body: by
  rw [cofibration_iff] at hf ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip hf

中文:
实例 [(cofibrations
  签名: C).是StableUnderCobaseChange] [hf : 余纤维化 f] :
  定义体: by
  rw [cofibration_iff] at hf ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip hf

Depends on / 依赖: IsPushout, IsPushout.of_hasPushout, MorphismProperty, MorphismProperty.of_isPushout, cofibration_iff, of_hasPushout, of_isPushout
-/
instance [(cofibrations C).IsStableUnderCobaseChange] [hf : Cofibration f] :
    Cofibration (pushout.inr f g) := by
  rw [cofibration_iff] at hf ⊢
  exact MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(trivialCofibrations
  signature: C).IsStableUnderCobaseChange]
  body: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g)
    (mem_trivialCofibrations g)).2

中文:
实例 [(trivialCofibrations
  签名: C).是StableUnderCobaseChange]
  定义体: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g)
    (mem_trivialCofibrations g)).2

Depends on / 依赖: IsPushout, IsPushout.of_hasPushout, MorphismProperty, MorphismProperty.of_isPushout, mem_trivialCofibrations, of_hasPushout, of_isPushout, weakEquivalence_iff
-/
instance [(trivialCofibrations C).IsStableUnderCobaseChange]
    [Cofibration g] [WeakEquivalence g] : WeakEquivalence (pushout.inl f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g)
    (mem_trivialCofibrations g)).2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(trivialCofibrations
  signature: C).IsStableUnderCobaseChange]
  body: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip
    (mem_trivialCofibrations f)).2

中文:
实例 [(trivialCofibrations
  签名: C).是StableUnderCobaseChange]
  定义体: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip
    (mem_trivialCofibrations f)).2

Depends on / 依赖: IsPushout, IsPushout.of_hasPushout, MorphismProperty, MorphismProperty.of_isPushout, mem_trivialCofibrations, of_hasPushout, of_isPushout, weakEquivalence_iff
-/
instance [(trivialCofibrations C).IsStableUnderCobaseChange]
    [Cofibration f] [WeakEquivalence f] : WeakEquivalence (pushout.inr f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (IsPushout.of_hasPushout f g).flip
    (mem_trivialCofibrations f)).2

end

section

variable {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(fibrations
  signature: C).IsStableUnderBaseChange]
  body: by
  rw [fibration_iff] at hf ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g) hf

中文:
实例 [(fibrations
  签名: C).是StableUnderBaseChange]
  定义体: by
  rw [fibration_iff] at hf ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g) hf

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, MorphismProperty, MorphismProperty.of_isPullback, fibration_iff, of_hasPullback, of_isPullback
-/
instance [(fibrations C).IsStableUnderBaseChange]
    [hf : Fibration f] : Fibration (pullback.snd f g) := by
  rw [fibration_iff] at hf ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g) hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(fibrations
  signature: C).IsStableUnderBaseChange]
  body: by
  rw [fibration_iff] at hg ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip hg

中文:
实例 [(fibrations
  签名: C).是StableUnderBaseChange]
  定义体: by
  rw [fibration_iff] at hg ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip hg

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, MorphismProperty, MorphismProperty.of_isPullback, fibration_iff, of_hasPullback, of_isPullback
-/
instance [(fibrations C).IsStableUnderBaseChange]
    [hg : Fibration g] : Fibration (pullback.fst f g) := by
  rw [fibration_iff] at hg ⊢
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(trivialFibrations
  signature: C).IsStableUnderBaseChange]
  body: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g)
    (mem_trivialFibrations f)).2

中文:
实例 [(trivialFibrations
  签名: C).是StableUnderBaseChange]
  定义体: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g)
    (mem_trivialFibrations f)).2

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, MorphismProperty, MorphismProperty.of_isPullback, mem_trivialFibrations, of_hasPullback, of_isPullback, weakEquivalence_iff
-/
instance [(trivialFibrations C).IsStableUnderBaseChange]
    [Fibration f] [WeakEquivalence f] : WeakEquivalence (pullback.snd f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g)
    (mem_trivialFibrations f)).2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(trivialFibrations
  signature: C).IsStableUnderBaseChange]
  body: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip
    (mem_trivialFibrations g)).2

中文:
实例 [(trivialFibrations
  签名: C).是StableUnderBaseChange]
  定义体: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip
    (mem_trivialFibrations g)).2

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, MorphismProperty, MorphismProperty.of_isPullback, mem_trivialFibrations, of_hasPullback, of_isPullback, weakEquivalence_iff
-/
instance [(trivialFibrations C).IsStableUnderBaseChange]
    [Fibration g] [WeakEquivalence g] : WeakEquivalence (pullback.fst f g) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip
    (mem_trivialFibrations g)).2

end

end Pullbacks

section Products

variable (J : Type w) {C J} {X Y : J -> C} (f : forall i, X i ⟶ Y i)

section

variable [HasCoproduct X] [HasCoproduct Y] [h : forall i, Cofibration (f i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWeakFactorizationSystem
  signature: (cofibrations C) (trivialFibrations C)] :
  body: by
  simp only [cofibration_iff] at h ⊢
  exact MorphismProperty.colimMap _ (fun ⟨i⟩ => h i)

中文:
实例 [是WeakFactorizationSystem
  签名: (cofibrations C) (trivialFibrations C)] :
  定义体: by
  simp only [cofibration_iff] at h ⊢
  exact MorphismProperty.colimMap _ (fun ⟨i⟩ => h i)

Depends on / 依赖: MorphismProperty, MorphismProperty.colimMap, cofibration_iff, colimMap
-/
instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)] :
    Cofibration (Limits.Sigma.map f) := by
  simp only [cofibration_iff] at h ⊢
  exact MorphismProperty.colimMap _ (fun ⟨i⟩ => h i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWeakFactorizationSystem
  signature: (trivialCofibrations C) (fibrations C)]
  body: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.colimMap (W := (trivialCofibrations C)) _
    (fun ⟨i⟩ => mem_trivialCofibrations (f i))).2

中文:
实例 [是WeakFactorizationSystem
  签名: (trivialCofibrations C) (fibrations C)]
  定义体: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.colimMap (W := (trivialCofibrations C)) _
    (fun ⟨i⟩ => mem_trivialCofibrations (f i))).2

Depends on / 依赖: MorphismProperty, MorphismProperty.colimMap, colimMap, mem_trivialCofibrations, trivialCofibrations, weakEquivalence_iff
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [forall i, WeakEquivalence (f i)] :
    WeakEquivalence (Limits.Sigma.map f) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.colimMap (W := (trivialCofibrations C)) _
    (fun ⟨i⟩ => mem_trivialCofibrations (f i))).2

end

section

variable [HasProduct X] [HasProduct Y] [h : forall i, Fibration (f i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWeakFactorizationSystem
  signature: (trivialCofibrations C) (fibrations C)] :
  body: by
  simp only [fibration_iff] at h ⊢
  exact MorphismProperty.limMap _ (fun ⟨i⟩ => h i)

中文:
实例 [是WeakFactorizationSystem
  签名: (trivialCofibrations C) (fibrations C)] :
  定义体: by
  simp only [fibration_iff] at h ⊢
  exact MorphismProperty.limMap _ (fun ⟨i⟩ => h i)

Depends on / 依赖: MorphismProperty, MorphismProperty.limMap, fibration_iff, limMap
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)] :
    Fibration (Limits.Pi.map f) := by
  simp only [fibration_iff] at h ⊢
  exact MorphismProperty.limMap _ (fun ⟨i⟩ => h i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWeakFactorizationSystem
  signature: (cofibrations C) (trivialFibrations C)]
  body: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.limMap (W := (trivialFibrations C)) _
    (fun ⟨i⟩ => mem_trivialFibrations (f i))).2

中文:
实例 [是WeakFactorizationSystem
  签名: (cofibrations C) (trivialFibrations C)]
  定义体: by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.limMap (W := (trivialFibrations C)) _
    (fun ⟨i⟩ => mem_trivialFibrations (f i))).2

Depends on / 依赖: MorphismProperty, MorphismProperty.limMap, limMap, mem_trivialFibrations, trivialFibrations, weakEquivalence_iff
-/
instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]
    [forall i, WeakEquivalence (f i)] :
    WeakEquivalence (Limits.Pi.map f) := by
  rw [weakEquivalence_iff]
  exact (MorphismProperty.limMap (W := (trivialFibrations C)) _
    (fun ⟨i⟩ => mem_trivialFibrations (f i))).2

end

end Products

section BinaryProducts

variable {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWeakFactorizationSystem
  signature: (cofibrations C) (trivialFibrations C)]
  body: by
  rw [cofibration_iff] at h₁ h₂ ⊢
  apply MorphismProperty.colimMap
  rintro (_ | _) <;> assumption

中文:
实例 [是WeakFactorizationSystem
  签名: (cofibrations C) (trivialFibrations C)]
  定义体: by
  rw [cofibration_iff] at h₁ h₂ ⊢
  apply MorphismProperty.colimMap
  rintro (_ | _) <;> assumption

Depends on / 依赖: MorphismProperty, MorphismProperty.colimMap, cofibration_iff, colimMap
-/
instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]
    [h₁ : Cofibration f₁] [h₂ : Cofibration f₂] [HasBinaryCoproduct X₁ X₂]
    [HasBinaryCoproduct Y₁ Y₂] : Cofibration (coprod.map f₁ f₂) := by
  rw [cofibration_iff] at h₁ h₂ ⊢
  apply MorphismProperty.colimMap
  rintro (_ | _) <;> assumption

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWeakFactorizationSystem
  signature: (trivialCofibrations C) (fibrations C)]
  body: by
  rw [fibration_iff] at h₁ h₂ ⊢
  apply MorphismProperty.limMap
  rintro (_ | _) <;> assumption

中文:
实例 [是WeakFactorizationSystem
  签名: (trivialCofibrations C) (fibrations C)]
  定义体: by
  rw [fibration_iff] at h₁ h₂ ⊢
  apply MorphismProperty.limMap
  rintro (_ | _) <;> assumption

Depends on / 依赖: MorphismProperty, MorphismProperty.limMap, fibration_iff, limMap
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWeakFactorizationSystem
  signature: (trivialCofibrations C) (fibrations C)] [IsIso f] :
  body: by
  have := (fibrations C).llp_of_isIso f
  rw [fibrations_llp] at this
  simpa only [cofibration_iff] using this.1

中文:
实例 [是WeakFactorizationSystem
  签名: (trivialCofibrations C) (fibrations C)] [是同构 f] :
  定义体: by
  have := (fibrations C).llp_of_isIso f
  rw [fibrations_llp] at this
  simpa only [cofibration_iff] using this.1

Depends on / 依赖: cofibration_iff, fibrations, fibrations_llp, llp_of_isIso
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)] [IsIso f] :
    Cofibration f := by
  have := (fibrations C).llp_of_isIso f
  rw [fibrations_llp] at this
  simpa only [cofibration_iff] using this.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWeakFactorizationSystem
  signature: (cofibrations C) (trivialFibrations C)] [IsIso f] :
  body: by
  have := (cofibrations C).rlp_of_isIso f
  rw [cofibrations_rlp] at this
  simpa only [fibration_iff] using this.1

中文:
实例 [是WeakFactorizationSystem
  签名: (cofibrations C) (trivialFibrations C)] [是同构 f] :
  定义体: by
  have := (cofibrations C).rlp_of_isIso f
  rw [cofibrations_rlp] at this
  simpa only [fibration_iff] using this.1

Depends on / 依赖: cofibrations, cofibrations_rlp, fibration_iff, rlp_of_isIso
-/
instance [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)] [IsIso f] :
    Fibration f := by
  have := (cofibrations C).rlp_of_isIso f
  rw [cofibrations_rlp] at this
  simpa only [fibration_iff] using this.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWeakFactorizationSystem
  signature: (trivialCofibrations C) (fibrations C)]
  body: by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) f
  rw [weakEquivalence_iff]
  exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty h.fac) h.hi.2

中文:
实例 [是WeakFactorizationSystem
  签名: (trivialCofibrations C) (fibrations C)]
  定义体: by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) f
  rw [weakEquivalence_iff]
  exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty h.fac) h.hi.2

Depends on / 依赖: MorphismProperty, MorphismProperty.factorizationData, MorphismProperty.of_retract, RetractArrow, RetractArrow.ofLeftLiftingProperty, factorizationData, fibrations, h.fac, h.hi, ofLeftLiftingProperty, of_retract, trivialCofibrations, weakEquivalence_iff
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [(weakEquivalences C).IsStableUnderRetracts] [IsIso f] :
    WeakEquivalence f := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) f
  rw [weakEquivalence_iff]
  exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty h.fac) h.hi.2

end IsIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWeakFactorizationSystem
  signature: (trivialCofibrations C) (fibrations C)]
  body: by
    rw [← weakEquivalence_iff]
    infer_instance

中文:
实例 [是WeakFactorizationSystem
  签名: (trivialCofibrations C) (fibrations C)]
  定义体: by
    rw [← weakEquivalence_iff]
    infer_instance

Depends on / 依赖: infer_instance, weakEquivalence_iff
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [(weakEquivalences C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderComposition] :
    (weakEquivalences C).IsMultiplicative where
  id_mem _ := by
    rw [← weakEquivalence_iff]
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWeakFactorizationSystem
  signature: (trivialCofibrations C) (fibrations C)]
  body: MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ _ (_ : IsIso _) => by
    rw [← weakEquivalence_iff]
    infer_instance)

中文:
实例 [是WeakFactorizationSystem
  签名: (trivialCofibrations C) (fibrations C)]
  定义体: MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ _ (_ : IsIso _) => by
    rw [← weakEquivalence_iff]
    infer_instance)

Depends on / 依赖: MorphismProperty, MorphismProperty.respectsIso_of_isStableUnderComposition, infer_instance, respectsIso_of_isStableUnderComposition, weakEquivalence_iff
-/
instance [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [(weakEquivalences C).IsStableUnderRetracts]
    [(weakEquivalences C).IsStableUnderComposition] :
    (weakEquivalences C).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ _ (_ : IsIso _) => by
    rw [← weakEquivalence_iff]
    infer_instance)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(weakEquivalences
  signature: C).ContainsIdentities] (X : C) :
  body: by
  rw [weakEquivalence_iff]
  apply id_mem

中文:
实例 [(weakEquivalences
  签名: C).余ntainsIdentities] (X : C) :
  定义体: by
  rw [weakEquivalence_iff]
  apply id_mem

Depends on / 依赖: id_mem, weakEquivalence_iff
-/
instance [(weakEquivalences C).ContainsIdentities] (X : C) :
    WeakEquivalence (𝟙 X) := by
  rw [weakEquivalence_iff]
  apply id_mem

section MapFactorizationData

variable {X Y : C} (f : X ⟶ Y)

section

variable (h : MapFactorizationData (cofibrations C) (trivialFibrations C) f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Cofibration h.i
  body: by
  simpa only [cofibration_iff] using h.hi

中文:
实例 :
  签名: 余纤维化 h.i
  定义体: by
  simpa only [cofibration_iff] using h.hi

Depends on / 依赖: cofibration_iff, h.hi
-/
instance : Cofibration h.i := by
  simpa only [cofibration_iff] using h.hi

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fibration h.p
  body: by
  simpa only [fibration_iff] using h.hp.1

中文:
实例 :
  签名: 纤维化 h.p
  定义体: by
  simpa only [fibration_iff] using h.hp.1

Depends on / 依赖: fibration_iff, h.hp
-/
instance : Fibration h.p := by
  simpa only [fibration_iff] using h.hp.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WeakEquivalence h.p
  body: by
  simpa only [weakEquivalence_iff] using h.hp.2

中文:
实例 :
  签名: 弱等价 h.p
  定义体: by
  simpa only [weakEquivalence_iff] using h.hp.2

Depends on / 依赖: h.hp, weakEquivalence_iff
-/
instance : WeakEquivalence h.p := by
  simpa only [weakEquivalence_iff] using h.hp.2

end

section

variable (h : MapFactorizationData (trivialCofibrations C) (fibrations C) f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Cofibration h.i
  body: by
  simpa only [cofibration_iff] using h.hi.1

中文:
实例 :
  签名: 余纤维化 h.i
  定义体: by
  simpa only [cofibration_iff] using h.hi.1

Depends on / 依赖: cofibration_iff, h.hi
-/
instance : Cofibration h.i := by
  simpa only [cofibration_iff] using h.hi.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WeakEquivalence h.i
  body: by
  simpa only [weakEquivalence_iff] using h.hi.2

中文:
实例 :
  签名: 弱等价 h.i
  定义体: by
  simpa only [weakEquivalence_iff] using h.hi.2

Depends on / 依赖: h.hi, weakEquivalence_iff
-/
instance : WeakEquivalence h.i := by
  simpa only [weakEquivalence_iff] using h.hi.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fibration h.p
  body: by
  simpa only [fibration_iff] using h.hp

中文:
实例 :
  签名: 纤维化 h.p
  定义体: by
  simpa only [fibration_iff] using h.hp

Depends on / 依赖: fibration_iff, h.hp
-/
instance : Fibration h.p := by
  simpa only [fibration_iff] using h.hp

end

end MapFactorizationData

end HomotopicalAlgebra
