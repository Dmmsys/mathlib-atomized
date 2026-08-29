/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving terminal object

Constructions to relate the notions of preserving terminal objects and reflecting terminal objects
to concrete objects.

In particular, we show that `terminalComparison G` is an isomorphism iff `G` preserves terminal
objects.
-/

@[expose] public section


universe w v v₁ v₂ u u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable (X : C)

section Terminal

/--
Definition of `isLimitMapConeEmptyConeEquiv` / `isLimitMapConeEmptyConeEquiv` 的定义

English:
definition isLimitMapConeEmptyConeEquiv
  signature: :
  body: isLimitEmptyConeEquiv D _ _ (eqToIso rfl)

中文:
定义 isLimitMapConeEmptyConeEquiv
  签名: :
  定义体: isLimitEmptyConeEquiv D _ _ (eqToIso rfl)

Depends on / 依赖: eqToIso, isLimitEmptyConeEquiv
-/
def isLimitMapConeEmptyConeEquiv :
    IsLimit (G.mapCone (asEmptyCone X)) ≃ IsTerminal (G.obj X) :=
  isLimitEmptyConeEquiv D _ _ (eqToIso rfl)

/--
Definition of `IsTerminal.isTerminalObj` / `IsTerminal.isTerminalObj` 的定义

English:
definition IsTerminal.isTerminalObj
  signature: [PreservesLimit (Functor.empty.{0} C) G] (l : IsTerminal X)
  body: isLimitMapConeEmptyConeEquiv G X (isLimitOfPreserves G l)

中文:
定义 是终止.isTerminalObj
  签名: [保持极限 (函子.empty.{0} C) G] (l : 是终止 X)
  定义体: isLimitMapConeEmptyConeEquiv G X (isLimitOfPreserves G l)

Depends on / 依赖: isLimitMapConeEmptyConeEquiv, isLimitOfPreserves
-/
def IsTerminal.isTerminalObj [PreservesLimit (Functor.empty.{0} C) G] (l : IsTerminal X) :
    IsTerminal (G.obj X) :=
  isLimitMapConeEmptyConeEquiv G X (isLimitOfPreserves G l)

/--
Definition of `IsTerminal.isTerminalOfObj` / `IsTerminal.isTerminalOfObj` 的定义

English:
definition IsTerminal.isTerminalOfObj
  signature: [ReflectsLimit (Functor.empty.{0} C) G] (l : IsTerminal (G.obj X))
  body: isLimitOfReflects G ((isLimitMapConeEmptyConeEquiv G X).symm l)

中文:
定义 是终止.isTerminalOfObj
  签名: [反映极限 (函子.empty.{0} C) G] (l : 是终止 (G.obj X))
  定义体: isLimitOfReflects G ((isLimitMapConeEmptyConeEquiv G X).symm l)

Depends on / 依赖: isLimitMapConeEmptyConeEquiv, isLimitOfReflects
-/
def IsTerminal.isTerminalOfObj [ReflectsLimit (Functor.empty.{0} C) G] (l : IsTerminal (G.obj X)) :
    IsTerminal X :=
  isLimitOfReflects G ((isLimitMapConeEmptyConeEquiv G X).symm l)

/--
Definition of `IsTerminal.isTerminalIffObj` / `IsTerminal.isTerminalIffObj` 的定义

English:
definition IsTerminal.isTerminalIffObj
  signature: [PreservesLimit (Functor.empty.{0} C) G]
  body: IsTerminal.isTerminalObj G X
  invFun := IsTerminal.isTerminalOfObj G X
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 是终止.isTerminalIffObj
  签名: [保持极限 (函子.empty.{0} C) G]
  定义体: IsTerminal.isTerminalObj G X
  invFun := IsTerminal.isTerminalOfObj G X
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: IsTerminal, IsTerminal.isTerminalObj, isTerminalObj
-/
def IsTerminal.isTerminalIffObj [PreservesLimit (Functor.empty.{0} C) G]
    [ReflectsLimit (Functor.empty.{0} C) G] (X : C) :
    IsTerminal X ≃ IsTerminal (G.obj X) where
  toFun := IsTerminal.isTerminalObj G X
  invFun := IsTerminal.isTerminalOfObj G X
  left_inv := by cat_disch
  right_inv := by cat_disch

/--
lemma `preservesLimitsOfShape_pempty_of_preservesTerminal` / 引理 `preservesLimitsOfShape_pempty_of_preservesTerminal`

English:
lemma preservesLimitsOfShape_pempty_of_preservesTerminal
  given: [PreservesLimit (Functor.empty.{0} C) G]
  proof: preservesLimit_of_iso_diagram G (Functor.emptyExt (Functor.empty.{0} C) _)

中文:
引理 preservesLimitsOfShape_pempty_of_preservesTerminal
  条件: [保持极限 (函子.empty.{0} C) G]
  证明: preservesLimit_of_iso_diagram G (Functor.emptyExt (Functor.empty.{0} C) _)

Depends on / 依赖: Functor, Functor.empty, Functor.emptyExt, emptyExt, preservesLimit_of_iso_diagram
-/
lemma preservesLimitsOfShape_pempty_of_preservesTerminal [PreservesLimit (Functor.empty.{0} C) G] :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) G where
  preservesLimit := preservesLimit_of_iso_diagram G (Functor.emptyExt (Functor.empty.{0} C) _)

variable [HasTerminal C]

/--
Definition of `isLimitOfHasTerminalOfPreservesLimit` / `isLimitOfHasTerminalOfPreservesLimit` 的定义

English:
definition isLimitOfHasTerminalOfPreservesLimit
  signature: [PreservesLimit (Functor.empty.{0} C) G]
  body: terminalIsTerminal.isTerminalObj G (⊤_ C)

中文:
定义 isLimitOfHasTerminalOfPreservesLimit
  签名: [保持极限 (函子.empty.{0} C) G]
  定义体: terminalIsTerminal.isTerminalObj G (⊤_ C)

Depends on / 依赖: isTerminalObj, terminalIsTerminal, terminalIsTerminal.isTerminalObj
-/
def isLimitOfHasTerminalOfPreservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    IsTerminal (G.obj (⊤_ C)) :=
  terminalIsTerminal.isTerminalObj G (⊤_ C)

/--
theorem `hasTerminal_of_hasTerminal_of_preservesLimit` / 定理 `hasTerminal_of_hasTerminal_of_preservesLimit`

English:
theorem hasTerminal_of_hasTerminal_of_preservesLimit
  given: [PreservesLimit (Functor.empty.{0} C) G]
  proof: ⟨fun F => by
  have := HasLimit.mk ⟨_, isLimitOfHasTerminalOfPreservesLimit G⟩
  apply hasLimit_of_iso F.uniqueFromEmpty.symm⟩

中文:
定理 hasTerminal_of_hasTerminal_of_preservesLimit
  条件: [保持极限 (函子.empty.{0} C) G]
  证明: ⟨fun F => by
  have := HasLimit.mk ⟨_, isLimitOfHasTerminalOfPreservesLimit G⟩
  apply hasLimit_of_iso F.uniqueFromEmpty.symm⟩

Depends on / 依赖: F.uniqueFromEmpty.symm, HasLimit, HasLimit.mk, hasLimit_of_iso, isLimitOfHasTerminalOfPreservesLimit, uniqueFromEmpty
-/
theorem hasTerminal_of_hasTerminal_of_preservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    HasTerminal D := ⟨fun F => by
  have := HasLimit.mk ⟨_, isLimitOfHasTerminalOfPreservesLimit G⟩
  apply hasLimit_of_iso F.uniqueFromEmpty.symm⟩

variable [HasTerminal D]

/--
lemma `PreservesTerminal.of_iso_comparison` / 引理 `PreservesTerminal.of_iso_comparison`

English:
lemma PreservesTerminal.of_iso_comparison
  given: [i : IsIso (terminalComparison G)]
  proof: by
  apply preservesLimit_of_preserves_limit_cone terminalIsTerminal
  apply (isLimitMapConeEmptyConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (Functor.empty.{0} D)) i

中文:
引理 PreservesTerminal.of_iso_comparison
  条件: [i : 是同构 (terminalComparison G)]
  证明: by
  apply preservesLimit_of_preserves_limit_cone terminalIsTerminal
  apply (isLimitMapConeEmptyConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (Functor.empty.{0} D)) i

Depends on / 依赖: Functor, Functor.empty, IsLimit, IsLimit.ofPointIso, isLimit, isLimitMapConeEmptyConeEquiv, limit.isLimit, ofPointIso, preservesLimit_of_preserves_limit_cone, terminalIsTerminal
-/
lemma PreservesTerminal.of_iso_comparison [i : IsIso (terminalComparison G)] :
    PreservesLimit (Functor.empty.{0} C) G := by
  apply preservesLimit_of_preserves_limit_cone terminalIsTerminal
  apply (isLimitMapConeEmptyConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (Functor.empty.{0} D)) i

/--
lemma `preservesTerminal_of_isIso` / 引理 `preservesTerminal_of_isIso`

English:
lemma preservesTerminal_of_isIso
  given: (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : IsIso f]
  proof: by
  rw [Subsingleton.elim f (terminalComparison G)] at i
  exact PreservesTerminal.of_iso_comparison G

中文:
引理 preservesTerminal_of_isIso
  条件: (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : 是同构 f]
  证明: by
  rw [Subsingleton.elim f (terminalComparison G)] at i
  exact PreservesTerminal.of_iso_comparison G

Depends on / 依赖: PreservesTerminal, PreservesTerminal.of_iso_comparison, Subsingleton, Subsingleton.elim, of_iso_comparison, terminalComparison
-/
lemma preservesTerminal_of_isIso (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : IsIso f] :
    PreservesLimit (Functor.empty.{0} C) G := by
  rw [Subsingleton.elim f (terminalComparison G)] at i
  exact PreservesTerminal.of_iso_comparison G

/--
lemma `preservesTerminal_of_iso` / 引理 `preservesTerminal_of_iso`

English:
lemma preservesTerminal_of_iso
  given: (f : G.obj (⊤_ C) ≅ ⊤_ D)
  statement: PreservesLimit (Functor.empty.{0} C) G
  proof: preservesTerminal_of_isIso G f.hom

中文:
引理 preservesTerminal_of_iso
  条件: (f : G.obj (⊤_ C) ≅ ⊤_ D)
  结论: 保持极限 (函子.empty.{0} C) G
  证明: preservesTerminal_of_isIso G f.hom

Depends on / 依赖: f.hom, preservesTerminal_of_isIso
-/
lemma preservesTerminal_of_iso (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty.{0} C) G :=
  preservesTerminal_of_isIso G f.hom

variable [PreservesLimit (Functor.empty.{0} C) G]

/--
Definition of `PreservesTerminal.iso` / `PreservesTerminal.iso` 的定义

English:
definition PreservesTerminal.iso
  signature: : G.obj (⊤_ C) ≅ ⊤_ D
  body: (isLimitOfHasTerminalOfPreservesLimit G).conePointUniqueUpToIso (limit.isLimit _)

@[simp]

中文:
定义 PreservesTerminal.iso
  签名: : G.obj (⊤_ C) ≅ ⊤_ D
  定义体: (isLimitOfHasTerminalOfPreservesLimit G).conePointUniqueUpToIso (limit.isLimit _)

@[simp]

Depends on / 依赖: conePointUniqueUpToIso, isLimit, isLimitOfHasTerminalOfPreservesLimit, limit.isLimit
-/
def PreservesTerminal.iso : G.obj (⊤_ C) ≅ ⊤_ D :=
  (isLimitOfHasTerminalOfPreservesLimit G).conePointUniqueUpToIso (limit.isLimit _)

@[simp]
/--
theorem `PreservesTerminal.iso_hom` / 定理 `PreservesTerminal.iso_hom`

English:
theorem PreservesTerminal.iso_hom
  statement: (PreservesTerminal.iso G).hom = terminalComparison G
  proof: rfl

中文:
定理 PreservesTerminal.iso_hom
  结论: (PreservesTerminal.iso G).hom = terminalComparison G
  证明: rfl
-/
theorem PreservesTerminal.iso_hom : (PreservesTerminal.iso G).hom = terminalComparison G :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (terminalComparison G)
  body: by
  rw [← PreservesTerminal.iso_hom]
  infer_instance

中文:
实例 :
  签名: 是同构 (terminalComparison G)
  定义体: by
  rw [← PreservesTerminal.iso_hom]
  infer_instance

Depends on / 依赖: PreservesTerminal, PreservesTerminal.iso_hom, infer_instance, iso_hom
-/
instance : IsIso (terminalComparison G) := by
  rw [← PreservesTerminal.iso_hom]
  infer_instance

end Terminal

section Initial

/--
Definition of `isColimitMapCoconeEmptyCoconeEquiv` / `isColimitMapCoconeEmptyCoconeEquiv` 的定义

English:
definition isColimitMapCoconeEmptyCoconeEquiv
  signature: :
  body: isColimitEmptyCoconeEquiv D _ _ (eqToIso rfl)

中文:
定义 isColimitMapCoconeEmptyCoconeEquiv
  签名: :
  定义体: isColimitEmptyCoconeEquiv D _ _ (eqToIso rfl)

Depends on / 依赖: eqToIso, isColimitEmptyCoconeEquiv
-/
def isColimitMapCoconeEmptyCoconeEquiv :
    IsColimit (G.mapCocone (asEmptyCocone.{v₁} X)) ≃ IsInitial (G.obj X) :=
  isColimitEmptyCoconeEquiv D _ _ (eqToIso rfl)

/--
Definition of `IsInitial.isInitialObj` / `IsInitial.isInitialObj` 的定义

English:
definition IsInitial.isInitialObj
  signature: [PreservesColimit (Functor.empty.{0} C) G] (l : IsInitial X)
  body: isColimitMapCoconeEmptyCoconeEquiv G X (isColimitOfPreserves G l)

中文:
定义 IsInitial.isInitialObj
  签名: [保持余极限 (函子.empty.{0} C) G] (l : IsInitial X)
  定义体: isColimitMapCoconeEmptyCoconeEquiv G X (isColimitOfPreserves G l)

Depends on / 依赖: isColimitMapCoconeEmptyCoconeEquiv, isColimitOfPreserves
-/
def IsInitial.isInitialObj [PreservesColimit (Functor.empty.{0} C) G] (l : IsInitial X) :
    IsInitial (G.obj X) :=
  isColimitMapCoconeEmptyCoconeEquiv G X (isColimitOfPreserves G l)

/--
Definition of `IsInitial.isInitialOfObj` / `IsInitial.isInitialOfObj` 的定义

English:
definition IsInitial.isInitialOfObj
  signature: [ReflectsColimit (Functor.empty.{0} C) G] (l : IsInitial (G.obj X))
  body: isColimitOfReflects G ((isColimitMapCoconeEmptyCoconeEquiv G X).symm l)

中文:
定义 IsInitial.isInitialOfObj
  签名: [反映余极限 (函子.empty.{0} C) G] (l : IsInitial (G.obj X))
  定义体: isColimitOfReflects G ((isColimitMapCoconeEmptyCoconeEquiv G X).symm l)

Depends on / 依赖: isColimitMapCoconeEmptyCoconeEquiv, isColimitOfReflects
-/
def IsInitial.isInitialOfObj [ReflectsColimit (Functor.empty.{0} C) G] (l : IsInitial (G.obj X)) :
    IsInitial X :=
  isColimitOfReflects G ((isColimitMapCoconeEmptyCoconeEquiv G X).symm l)

/--
Definition of `IsInitial.isInitialIffObj` / `IsInitial.isInitialIffObj` 的定义

English:
definition IsInitial.isInitialIffObj
  signature: [PreservesColimit (Functor.empty.{0} C) G]
  body: IsInitial.isInitialObj G X
  invFun := IsInitial.isInitialOfObj G X
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 IsInitial.isInitialIffObj
  签名: [保持余极限 (函子.empty.{0} C) G]
  定义体: IsInitial.isInitialObj G X
  invFun := IsInitial.isInitialOfObj G X
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: IsInitial, IsInitial.isInitialObj, isInitialObj
-/
def IsInitial.isInitialIffObj [PreservesColimit (Functor.empty.{0} C) G]
    [ReflectsColimit (Functor.empty.{0} C) G] (X : C) :
    IsInitial X ≃ IsInitial (G.obj X) where
  toFun := IsInitial.isInitialObj G X
  invFun := IsInitial.isInitialOfObj G X
  left_inv := by cat_disch
  right_inv := by cat_disch

/--
lemma `preservesColimitsOfShape_pempty_of_preservesInitial` / 引理 `preservesColimitsOfShape_pempty_of_preservesInitial`

English:
lemma preservesColimitsOfShape_pempty_of_preservesInitial
  proof: preservesColimit_of_iso_diagram G (Functor.emptyExt (Functor.empty.{0} C) _)

中文:
引理 preservesColimitsOfShape_pempty_of_preservesInitial
  证明: preservesColimit_of_iso_diagram G (Functor.emptyExt (Functor.empty.{0} C) _)

Depends on / 依赖: Functor, Functor.empty, Functor.emptyExt, emptyExt, preservesColimit_of_iso_diagram
-/
lemma preservesColimitsOfShape_pempty_of_preservesInitial
    [PreservesColimit (Functor.empty.{0} C) G] :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) G where
  preservesColimit :=
    preservesColimit_of_iso_diagram G (Functor.emptyExt (Functor.empty.{0} C) _)

variable [HasInitial C]

/--
Definition of `isColimitOfHasInitialOfPreservesColimit` / `isColimitOfHasInitialOfPreservesColimit` 的定义

English:
definition isColimitOfHasInitialOfPreservesColimit
  signature: [PreservesColimit (Functor.empty.{0} C) G]
  body: initialIsInitial.isInitialObj G (⊥_ C)

中文:
定义 isColimitOfHasInitialOfPreservesColimit
  签名: [保持余极限 (函子.empty.{0} C) G]
  定义体: initialIsInitial.isInitialObj G (⊥_ C)

Depends on / 依赖: initialIsInitial, initialIsInitial.isInitialObj, isInitialObj
-/
def isColimitOfHasInitialOfPreservesColimit [PreservesColimit (Functor.empty.{0} C) G] :
    IsInitial (G.obj (⊥_ C)) :=
  initialIsInitial.isInitialObj G (⊥_ C)

/--
theorem `hasInitial_of_hasInitial_of_preservesColimit` / 定理 `hasInitial_of_hasInitial_of_preservesColimit`

English:
theorem hasInitial_of_hasInitial_of_preservesColimit
  given: [PreservesColimit (Functor.empty.{0} C) G]
  proof: ⟨fun F => by
    have := HasColimit.mk ⟨_, isColimitOfHasInitialOfPreservesColimit G⟩
    apply hasColimit_of_iso F.uniqueFromEmpty⟩

中文:
定理 hasInitial_of_hasInitial_of_preservesColimit
  条件: [保持余极限 (函子.empty.{0} C) G]
  证明: ⟨fun F => by
    have := HasColimit.mk ⟨_, isColimitOfHasInitialOfPreservesColimit G⟩
    apply hasColimit_of_iso F.uniqueFromEmpty⟩

Depends on / 依赖: F.uniqueFromEmpty, HasColimit, HasColimit.mk, hasColimit_of_iso, isColimitOfHasInitialOfPreservesColimit, uniqueFromEmpty
-/
theorem hasInitial_of_hasInitial_of_preservesColimit [PreservesColimit (Functor.empty.{0} C) G] :
    HasInitial D :=
  ⟨fun F => by
    have := HasColimit.mk ⟨_, isColimitOfHasInitialOfPreservesColimit G⟩
    apply hasColimit_of_iso F.uniqueFromEmpty⟩

variable [HasInitial D]

/--
lemma `PreservesInitial.of_iso_comparison` / 引理 `PreservesInitial.of_iso_comparison`

English:
lemma PreservesInitial.of_iso_comparison
  given: [i : IsIso (initialComparison G)]
  proof: by
  apply preservesColimit_of_preserves_colimit_cocone initialIsInitial
  apply (isColimitMapCoconeEmptyCoconeEquiv _ _).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (Functor.empty.{0} D)) i

中文:
引理 PreservesInitial.of_iso_comparison
  条件: [i : 是同构 (initialComparison G)]
  证明: by
  apply preservesColimit_of_preserves_colimit_cocone initialIsInitial
  apply (isColimitMapCoconeEmptyCoconeEquiv _ _).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (Functor.empty.{0} D)) i

Depends on / 依赖: Functor, Functor.empty, IsColimit, IsColimit.ofPointIso, colimit, colimit.isColimit, initialIsInitial, isColimit, isColimitMapCoconeEmptyCoconeEquiv, ofPointIso, preservesColimit_of_preserves_colimit_cocone
-/
lemma PreservesInitial.of_iso_comparison [i : IsIso (initialComparison G)] :
    PreservesColimit (Functor.empty.{0} C) G := by
  apply preservesColimit_of_preserves_colimit_cocone initialIsInitial
  apply (isColimitMapCoconeEmptyCoconeEquiv _ _).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (Functor.empty.{0} D)) i

/--
lemma `preservesInitial_of_isIso` / 引理 `preservesInitial_of_isIso`

English:
lemma preservesInitial_of_isIso
  given: (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : IsIso f]
  proof: by
  rw [Subsingleton.elim f (initialComparison G)] at i
  exact PreservesInitial.of_iso_comparison G

中文:
引理 preservesInitial_of_isIso
  条件: (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : 是同构 f]
  证明: by
  rw [Subsingleton.elim f (initialComparison G)] at i
  exact PreservesInitial.of_iso_comparison G

Depends on / 依赖: PreservesInitial, PreservesInitial.of_iso_comparison, Subsingleton, Subsingleton.elim, initialComparison, of_iso_comparison
-/
lemma preservesInitial_of_isIso (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : IsIso f] :
    PreservesColimit (Functor.empty.{0} C) G := by
  rw [Subsingleton.elim f (initialComparison G)] at i
  exact PreservesInitial.of_iso_comparison G

/--
lemma `preservesInitial_of_iso` / 引理 `preservesInitial_of_iso`

English:
lemma preservesInitial_of_iso
  given: (f : ⊥_ D ≅ G.obj (⊥_ C))
  proof: preservesInitial_of_isIso G f.hom

中文:
引理 preservesInitial_of_iso
  条件: (f : ⊥_ D ≅ G.obj (⊥_ C))
  证明: preservesInitial_of_isIso G f.hom

Depends on / 依赖: f.hom, preservesInitial_of_isIso
-/
lemma preservesInitial_of_iso (f : ⊥_ D ≅ G.obj (⊥_ C)) :
    PreservesColimit (Functor.empty.{0} C) G :=
  preservesInitial_of_isIso G f.hom

variable [PreservesColimit (Functor.empty.{0} C) G]

/--
Definition of `PreservesInitial.iso` / `PreservesInitial.iso` 的定义

English:
definition PreservesInitial.iso
  signature: : G.obj (⊥_ C) ≅ ⊥_ D
  body: (isColimitOfHasInitialOfPreservesColimit G).coconePointUniqueUpToIso (colimit.isColimit _)

@[simp]

中文:
定义 PreservesInitial.iso
  签名: : G.obj (⊥_ C) ≅ ⊥_ D
  定义体: (isColimitOfHasInitialOfPreservesColimit G).coconePointUniqueUpToIso (colimit.isColimit _)

@[simp]

Depends on / 依赖: coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, isColimitOfHasInitialOfPreservesColimit
-/
def PreservesInitial.iso : G.obj (⊥_ C) ≅ ⊥_ D :=
  (isColimitOfHasInitialOfPreservesColimit G).coconePointUniqueUpToIso (colimit.isColimit _)

@[simp]
/--
theorem `PreservesInitial.iso_hom` / 定理 `PreservesInitial.iso_hom`

English:
theorem PreservesInitial.iso_hom
  statement: (PreservesInitial.iso G).inv = initialComparison G
  proof: rfl

中文:
定理 PreservesInitial.iso_hom
  结论: (PreservesInitial.iso G).inv = initialComparison G
  证明: rfl
-/
theorem PreservesInitial.iso_hom : (PreservesInitial.iso G).inv = initialComparison G :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (initialComparison G)
  body: by
  rw [← PreservesInitial.iso_hom]
  infer_instance

中文:
实例 :
  签名: 是同构 (initialComparison G)
  定义体: by
  rw [← PreservesInitial.iso_hom]
  infer_instance

Depends on / 依赖: PreservesInitial, PreservesInitial.iso_hom, infer_instance, iso_hom
-/
instance : IsIso (initialComparison G) := by
  rw [← PreservesInitial.iso_hom]
  infer_instance

end Initial

end CategoryTheory.Limits
