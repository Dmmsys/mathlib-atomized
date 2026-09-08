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

/-- The map of an empty cone is a limit iff the mapped object is terminal.
-/
/-
**CategoryTheory.Limits.isLimitMapConeEmptyConeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：isLimitMapConeEmptyConeEquiv : IsLimit (G.mapCone (asEmptyCone X)) ≃ IsTer
minal (G.obj X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map of an empty cone is a limit iff the mapped object is terminal.
-/
def isLimitMapConeEmptyConeEquiv :
    IsLimit (G.mapCone (asEmptyCone X)) ≃ IsTerminal (G.obj X) :=
  isLimitEmptyConeEquiv D _ _ (eqToIso rfl)

/-- The property of preserving terminal objects expressed in terms of `IsTerminal`. -/
/-
**CategoryTheory.Limits.IsTerminal.isTerminalObj** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.IsTerminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           (X : C) →             [CategoryTheory.Limit
s.PreservesLimit (CategoryTheory.Functor.empty C) G] →               CategoryThe
ory.Limits.IsTerminal X → CategoryTheory.Limits.IsTerminal (G.obj X)
参数：G : CategoryTheory.Functor C D；X : C；CategoryTheory.Functor.empty C；G.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving terminal objects expressed in terms of `IsTerminal`.
-/
def IsTerminal.isTerminalObj [PreservesLimit (Functor.empty.{0} C) G] (l : IsTerminal X) :
    IsTerminal (G.obj X) :=
  isLimitMapConeEmptyConeEquiv G X (isLimitOfPreserves G l)

/-- The property of reflecting terminal objects expressed in terms of `IsTerminal`. -/
/-
**CategoryTheory.Limits.IsTerminal.isTerminalOfObj** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.IsTerminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           (X : C) →             [CategoryTheory.Limit
s.ReflectsLimit (CategoryTheory.Functor.empty C) G] →               CategoryTheo
ry.Limits.IsTerminal (G.obj X) → CategoryTheory.Limits.IsTerminal X
参数：G : CategoryTheory.Functor C D；X : C；CategoryTheory.Functor.empty C；G.obj X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The property of reflecting terminal objects expressed in terms of `IsTerminal`.
-/
def IsTerminal.isTerminalOfObj [ReflectsLimit (Functor.empty.{0} C) G] (l : IsTerminal (G.obj X)) :
    IsTerminal X :=
  isLimitOfReflects G ((isLimitMapConeEmptyConeEquiv G X).symm l)

/-- A functor that preserves and reflects terminal objects induces an equivalence on
`IsTerminal`. -/
/-
**CategoryTheory.Limits.IsTerminal.isTerminalIffObj** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.IsTerminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           [CategoryTheory.Limits.PreservesLimit (Cate
goryTheory.Functor.empty C) G] →             [CategoryTheory.Limits.ReflectsLimi
t (CategoryTheory.Functor.empty C) G] →               (X : C) → CategoryTheory.L
imits.IsTerminal X ≃ CategoryTheory.Limits.IsTerminal (G.obj X)
参数：G : CategoryTheory.Functor C D；CategoryTheory.Functor.empty C；CategoryTheory.
Functor.empty C；X : C；G.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor that preserves and reflects terminal objects induces an equivalence on
`IsTerminal`.
-/
def IsTerminal.isTerminalIffObj [PreservesLimit (Functor.empty.{0} C) G]
    [ReflectsLimit (Functor.empty.{0} C) G] (X : C) :
    IsTerminal X ≃ IsTerminal (G.obj X) where
  toFun := IsTerminal.isTerminalObj G X
  invFun := IsTerminal.isTerminalOfObj G X
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Preserving the terminal object implies preserving all limits of the empty diagram. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_pempty_of_preservesTerminal** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_pempty_of_preservesTerminal [PreservesLimit (Functo
r.empty.{0} C) G] : PreservesLimitsOfShape (Discrete PEmpty.{1}) G where preserv
esLimit
参数：Functor.empty.{0} C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t

--- 原说明 ---
Preserving the terminal object implies preserving all limits of the empty diagra
m.
-/
lemma preservesLimitsOfShape_pempty_of_preservesTerminal [PreservesLimit (Functor.empty.{0} C) G] :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) G where
  preservesLimit := preservesLimit_of_iso_diagram G (Functor.emptyExt (Functor.empty.{0} C) _)

variable [HasTerminal C]

/--
If `G` preserves the terminal object and `C` has a terminal object, then the image of the terminal
object is terminal.
-/
/-
**CategoryTheory.Limits.isLimitOfHasTerminalOfPreservesLimit** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isLimitOfHasTerminalOfPreservesLimit [PreservesLimit (Functor.empty.{0} C)
 G] : IsTerminal (G.obj (⊤_ C))
参数：Functor.empty.{0} C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves the terminal object and `C` has a terminal object, then the ima
ge of the terminal
object is terminal.
-/
def isLimitOfHasTerminalOfPreservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    IsTerminal (G.obj (⊤_ C)) :=
  terminalIsTerminal.isTerminalObj G (⊤_ C)

/-- If `C` has a terminal object and `G` preserves terminal objects, then `D` has a terminal object
also.
Note this property is somewhat unique to (co)limits of the empty diagram: for general `J`, if `C`
has limits of shape `J` and `G` preserves them, then `D` does not necessarily have limits of shape
`J`.
-/
/-
**CategoryTheory.Limits.hasTerminal_of_hasTerminal_of_preservesLimit** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasTerminal_of_hasTerminal_of_preservesLimit [PreservesLimit (Functor.empt
y.{0} C) G] : HasTerminal D
参数：Functor.empty.{0} C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G

--- 原说明 ---
If `C` has a terminal object and `G` preserves terminal objects, then `D` has a 
terminal object
also.
Note this property is somewhat unique to (co)limits of the empty diagram: for ge
neral `J`, if `C`
has limits of shape `J` and `G` preserves them, then `D` does not necessarily ha
ve limits of shape
`J`.
-/
theorem hasTerminal_of_hasTerminal_of_preservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    HasTerminal D := ⟨fun F => by
  have := HasLimit.mk ⟨_, isLimitOfHasTerminalOfPreservesLimit G⟩
  apply hasLimit_of_iso F.uniqueFromEmpty.symm⟩

variable [HasTerminal D]

/-- If the terminal comparison map for `G` is an isomorphism, then `G` preserves terminal objects.
-/
/-
**CategoryTheory.Limits.PreservesTerminal.of_iso_comparison** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.PreservesTerminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 [inst_2 : CategoryTheory.Limits.HasTerminal C]   [inst_3 : CategoryTheory.Limit
s.HasTerminal D]   [i : CategoryTheory.IsIso (CategoryTheory.Limits.terminalComp
arison G)],   CategoryTheory.Limits.PreservesLimit (CategoryTheory.Functor.empty
 C) G
参数：G : CategoryTheory.Functor C D；CategoryTheory.Limits.terminalComparison G；Cat
egoryTheory.Functor.empty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If the terminal comparison map for `G` is an isomorphism, then `G` preserves ter
minal objects.
-/
lemma PreservesTerminal.of_iso_comparison [i : IsIso (terminalComparison G)] :
    PreservesLimit (Functor.empty.{0} C) G := by
  apply preservesLimit_of_preserves_limit_cone terminalIsTerminal
  apply (isLimitMapConeEmptyConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (Functor.empty.{0} D)) i

/-- If there is any isomorphism `G.obj ⊤ ⟶ ⊤`, then `G` preserves terminal objects. -/
/-
**CategoryTheory.Limits.preservesTerminal_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：preservesTerminal_of_isIso (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : IsIso f] : Prese
rvesLimit (Functor.empty.{0} C) G
参数：f : G.obj (⊤_ C) ⟶ ⊤_ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesTerminal.of_iso_comparison`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
If there is any isomorphism `G.obj ⊤ ⟶ ⊤`, then `G` preserves terminal objects.
-/
lemma preservesTerminal_of_isIso (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : IsIso f] :
    PreservesLimit (Functor.empty.{0} C) G := by
  rw [Subsingleton.elim f (terminalComparison G)] at i
  exact PreservesTerminal.of_iso_comparison G

/-- If there is any isomorphism `G.obj ⊤ ≅ ⊤`, then `G` preserves terminal objects. -/
/-
**CategoryTheory.Limits.preservesTerminal_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：preservesTerminal_of_iso (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Funct
or.empty.{0} C) G
参数：f : G.obj (⊤_ C) ≅ ⊤_ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesTerminal_of_isIso`：preservesTerminal_of_i
sIso (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : IsIso f] : PreservesLimit (Functor.empty.{0}
 C) G
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
If there is any isomorphism `G.obj ⊤ ≅ ⊤`, then `G` preserves terminal objects.
-/
lemma preservesTerminal_of_iso (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty.{0} C) G :=
  preservesTerminal_of_isIso G f.hom

variable [PreservesLimit (Functor.empty.{0} C) G]

/-- If `G` preserves terminal objects, then the terminal comparison map for `G` is an isomorphism.
-/
/-
**CategoryTheory.Limits.PreservesTerminal.iso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.PreservesTerminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           [inst_2 : CategoryTheory.Limits.HasTerminal
 C] →             [inst_3 : CategoryTheory.Limits.HasTerminal D] →              
 [CategoryTheory.Limits.PreservesLimit (CategoryTheory.Functor.empty C) G] → G.o
bj (⊤_ C) ≅ ⊤_ D
参数：G : CategoryTheory.Functor C D；CategoryTheory.Functor.empty C；⊤_ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves terminal objects, then the terminal comparison map for `G` is a
n isomorphism.
-/
def PreservesTerminal.iso : G.obj (⊤_ C) ≅ ⊤_ D :=
  (isLimitOfHasTerminalOfPreservesLimit G).conePointUniqueUpToIso (limit.isLimit _)

@[simp]
/-
**CategoryTheory.Limits.PreservesTerminal.iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.PreservesTerminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 [inst_2 : CategoryTheory.Limits.HasTerminal C]   [inst_3 : CategoryTheory.Limit
s.HasTerminal D]   [inst_4 : CategoryTheory.Limits.PreservesLimit (CategoryTheor
y.Functor.empty C) G],   (CategoryTheory.Limits.PreservesTerminal.iso G).hom = C
ategoryTheory.Limits.terminalComparison G
参数：G : CategoryTheory.Functor C D；CategoryTheory.Functor.empty C；CategoryTheory.
Limits.PreservesTerminal.iso G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesTerminal.iso_hom : (PreservesTerminal.iso G).hom = terminalComparison G :=
  rfl
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (terminalComparison G) := by
  rw [← PreservesTerminal.iso_hom]
  infer_instance

end Terminal

section Initial

/-- The map of an empty cocone is a colimit iff the mapped object is initial.
-/
/-
**CategoryTheory.Limits.isColimitMapCoconeEmptyCoconeEquiv** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitMapCoconeEmptyCoconeEquiv : IsColimit (G.mapCocone (asEmptyCocone
.{v₁} X)) ≃ IsInitial (G.obj X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map of an empty cocone is a colimit iff the mapped object is initial.
-/
def isColimitMapCoconeEmptyCoconeEquiv :
    IsColimit (G.mapCocone (asEmptyCocone.{v₁} X)) ≃ IsInitial (G.obj X) :=
  isColimitEmptyCoconeEquiv D _ _ (eqToIso rfl)

/-- The property of preserving initial objects expressed in terms of `IsInitial`. -/
/-
**CategoryTheory.Limits.IsInitial.isInitialObj** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.IsInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           (X : C) →             [CategoryTheory.Limit
s.PreservesColimit (CategoryTheory.Functor.empty C) G] →               CategoryT
heory.Limits.IsInitial X → CategoryTheory.Limits.IsInitial (G.obj X)
参数：G : CategoryTheory.Functor C D；X : C；CategoryTheory.Functor.empty C；G.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving initial objects expressed in terms of `IsInitial`.
-/
def IsInitial.isInitialObj [PreservesColimit (Functor.empty.{0} C) G] (l : IsInitial X) :
    IsInitial (G.obj X) :=
  isColimitMapCoconeEmptyCoconeEquiv G X (isColimitOfPreserves G l)

/-- The property of reflecting initial objects expressed in terms of `IsInitial`. -/
/-
**CategoryTheory.Limits.IsInitial.isInitialOfObj** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.IsInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           (X : C) →             [CategoryTheory.Limit
s.ReflectsColimit (CategoryTheory.Functor.empty C) G] →               CategoryTh
eory.Limits.IsInitial (G.obj X) → CategoryTheory.Limits.IsInitial X
参数：G : CategoryTheory.Functor C D；X : C；CategoryTheory.Functor.empty C；G.obj X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The property of reflecting initial objects expressed in terms of `IsInitial`.
-/
def IsInitial.isInitialOfObj [ReflectsColimit (Functor.empty.{0} C) G] (l : IsInitial (G.obj X)) :
    IsInitial X :=
  isColimitOfReflects G ((isColimitMapCoconeEmptyCoconeEquiv G X).symm l)

/-- A functor that preserves and reflects initial objects induces an equivalence on `IsInitial`. -/
/-
**CategoryTheory.Limits.IsInitial.isInitialIffObj** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.IsInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           [CategoryTheory.Limits.PreservesColimit (Ca
tegoryTheory.Functor.empty C) G] →             [CategoryTheory.Limits.ReflectsCo
limit (CategoryTheory.Functor.empty C) G] →               (X : C) → CategoryTheo
ry.Limits.IsInitial X ≃ CategoryTheory.Limits.IsInitial (G.obj X)
参数：G : CategoryTheory.Functor C D；CategoryTheory.Functor.empty C；CategoryTheory.
Functor.empty C；X : C；G.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor that preserves and reflects initial objects induces an equivalence on 
`IsInitial`.
-/
def IsInitial.isInitialIffObj [PreservesColimit (Functor.empty.{0} C) G]
    [ReflectsColimit (Functor.empty.{0} C) G] (X : C) :
    IsInitial X ≃ IsInitial (G.obj X) where
  toFun := IsInitial.isInitialObj G X
  invFun := IsInitial.isInitialOfObj G X
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Preserving the initial object implies preserving all colimits of the empty diagram. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_pempty_of_preservesInitial** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_pempty_of_preservesInitial [PreservesColimit (Fun
ctor.empty.{0} C) G] : PreservesColimitsOfShape (Discrete PEmpty.{1}) G where pr
eservesColimit
参数：Functor.empty.{0} C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…

--- 原说明 ---
Preserving the initial object implies preserving all colimits of the empty diagr
am.
-/
lemma preservesColimitsOfShape_pempty_of_preservesInitial
    [PreservesColimit (Functor.empty.{0} C) G] :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) G where
  preservesColimit :=
    preservesColimit_of_iso_diagram G (Functor.emptyExt (Functor.empty.{0} C) _)

variable [HasInitial C]

/-- If `G` preserves the initial object and `C` has an initial object, then the image of the initial
object is initial.
-/
/-
**CategoryTheory.Limits.isColimitOfHasInitialOfPreservesColimit** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitOfHasInitialOfPreservesColimit [PreservesColimit (Functor.empty.{
0} C) G] : IsInitial (G.obj (⊥_ C))
参数：Functor.empty.{0} C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves the initial object and `C` has an initial object, then the imag
e of the initial
object is initial.
-/
def isColimitOfHasInitialOfPreservesColimit [PreservesColimit (Functor.empty.{0} C) G] :
    IsInitial (G.obj (⊥_ C)) :=
  initialIsInitial.isInitialObj G (⊥_ C)

/-- If `C` has an initial object and `G` preserves initial objects, then `D` has an initial object
also.
Note this property is somewhat unique to colimits of the empty diagram: for general `J`, if `C`
has colimits of shape `J` and `G` preserves them, then `D` does not necessarily have colimits of
shape `J`.
-/
/-
**CategoryTheory.Limits.hasInitial_of_hasInitial_of_preservesColimit** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasInitial_of_hasInitial_of_preservesColimit [PreservesColimit (Functor.em
pty.{0} C) G] : HasInitial D
参数：Functor.empty.{0} C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G

--- 原说明 ---
If `C` has an initial object and `G` preserves initial objects, then `D` has an 
initial object
also.
Note this property is somewhat unique to colimits of the empty diagram: for gene
ral `J`, if `C`
has colimits of shape `J` and `G` preserves them, then `D` does not necessarily 
have colimits of
shape `J`.
-/
theorem hasInitial_of_hasInitial_of_preservesColimit [PreservesColimit (Functor.empty.{0} C) G] :
    HasInitial D :=
  ⟨fun F => by
    have := HasColimit.mk ⟨_, isColimitOfHasInitialOfPreservesColimit G⟩
    apply hasColimit_of_iso F.uniqueFromEmpty⟩

variable [HasInitial D]

/-- If the initial comparison map for `G` is an isomorphism, then `G` preserves initial objects.
-/
/-
**CategoryTheory.Limits.PreservesInitial.of_iso_comparison** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.PreservesInitial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 [inst_2 : CategoryTheory.Limits.HasInitial C]   [inst_3 : CategoryTheory.Limits
.HasInitial D] [i : CategoryTheory.IsIso (CategoryTheory.Limits.initialCompariso
n G)],   CategoryTheory.Limits.PreservesColimit (CategoryTheory.Functor.empty C)
 G
参数：G : CategoryTheory.Functor C D；CategoryTheory.Limits.initialComparison G；Cate
goryTheory.Functor.empty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
If the initial comparison map for `G` is an isomorphism, then `G` preserves init
ial objects.
-/
lemma PreservesInitial.of_iso_comparison [i : IsIso (initialComparison G)] :
    PreservesColimit (Functor.empty.{0} C) G := by
  apply preservesColimit_of_preserves_colimit_cocone initialIsInitial
  apply (isColimitMapCoconeEmptyCoconeEquiv _ _).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (Functor.empty.{0} D)) i

/-- If there is any isomorphism `⊥ ⟶ G.obj ⊥`, then `G` preserves initial objects. -/
/-
**CategoryTheory.Limits.preservesInitial_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：preservesInitial_of_isIso (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : IsIso f] : Preser
vesColimit (Functor.empty.{0} C) G
参数：f : ⊥_ D ⟶ G.obj (⊥_ C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesInitial.of_iso_comparison`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
If there is any isomorphism `⊥ ⟶ G.obj ⊥`, then `G` preserves initial objects.
-/
lemma preservesInitial_of_isIso (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : IsIso f] :
    PreservesColimit (Functor.empty.{0} C) G := by
  rw [Subsingleton.elim f (initialComparison G)] at i
  exact PreservesInitial.of_iso_comparison G

/-- If there is any isomorphism `⊥ ≅ G.obj ⊥`, then `G` preserves initial objects. -/
/-
**CategoryTheory.Limits.preservesInitial_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：preservesInitial_of_iso (f : ⊥_ D ≅ G.obj (⊥_ C)) : PreservesColimit (Func
tor.empty.{0} C) G
参数：f : ⊥_ D ≅ G.obj (⊥_ C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesInitial_of_isIso`：preservesInitial_of_isI
so (f : ⊥_ D ⟶ G.obj (⊥_ C)) [i : IsIso f] : PreservesColimit (Functor.empty.{0}
 C) G
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
If there is any isomorphism `⊥ ≅ G.obj ⊥`, then `G` preserves initial objects.
-/
lemma preservesInitial_of_iso (f : ⊥_ D ≅ G.obj (⊥_ C)) :
    PreservesColimit (Functor.empty.{0} C) G :=
  preservesInitial_of_isIso G f.hom

variable [PreservesColimit (Functor.empty.{0} C) G]

/-- If `G` preserves initial objects, then the initial comparison map for `G` is an isomorphism. -/
/-
**CategoryTheory.Limits.PreservesInitial.iso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.PreservesInitial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           [inst_2 : CategoryTheory.Limits.HasInitial 
C] →             [inst_3 : CategoryTheory.Limits.HasInitial D] →               [
CategoryTheory.Limits.PreservesColimit (CategoryTheory.Functor.empty C) G] → G.o
bj (⊥_ C) ≅ ⊥_ D
参数：G : CategoryTheory.Functor C D；CategoryTheory.Functor.empty C；⊥_ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves initial objects, then the initial comparison map for `G` is an 
isomorphism.
-/
def PreservesInitial.iso : G.obj (⊥_ C) ≅ ⊥_ D :=
  (isColimitOfHasInitialOfPreservesColimit G).coconePointUniqueUpToIso (colimit.isColimit _)

@[simp]
/-
**CategoryTheory.Limits.PreservesInitial.iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.PreservesInitial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 [inst_2 : CategoryTheory.Limits.HasInitial C]   [inst_3 : CategoryTheory.Limits
.HasInitial D]   [inst_4 : CategoryTheory.Limits.PreservesColimit (CategoryTheor
y.Functor.empty C) G],   (CategoryTheory.Limits.PreservesInitial.iso G).inv = Ca
tegoryTheory.Limits.initialComparison G
参数：G : CategoryTheory.Functor C D；CategoryTheory.Functor.empty C；CategoryTheory.
Limits.PreservesInitial.iso G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesInitial.iso_hom : (PreservesInitial.iso G).inv = initialComparison G :=
  rfl
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (initialComparison G) := by
  rw [← PreservesInitial.iso_hom]
  infer_instance

end Initial

end CategoryTheory.Limits

