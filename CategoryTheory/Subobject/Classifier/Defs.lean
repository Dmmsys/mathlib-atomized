/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen, Pablo Donato, Klaus Gy
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Subobject.Presheaf

/-!

# Subobject Classifier

We define a structure containing the data of a subobject classifier in a category `C` as
`CategoryTheory.Subobject.Classifier C`.

c.f. the following Lean 3 code, where similar work was done:
https://github.com/b-mehta/topos/blob/master/src/subobject_classifier.lean

## Main definitions

Let `C` refer to a category with a terminal object.

* `CategoryTheory.Subobject.Classifier C` is the data of a subobject classifier in `C`.

* `CategoryTheory.HasSubobjectClassifier C` says that there is at least one subobject classifier.
  `Ω C` denotes a choice of subobject classifier.

## Main results

* It is a theorem that the truth morphism `⊤_ C ⟶ Ω C` is a (split, and therefore regular)
  monomorphism, simply because its source is the terminal object.

* An instance of `IsRegularMonoCategory C` is exhibited for any category with a subobject
  classifier.

* `CategoryTheory.Subobject.Classifier.representableBy`: any subobject classifier `Ω` in `C`
  represents the subobjects functor `CategoryTheory.Subobject.presheaf C`, assuming `C` has
  pullbacks.

* `CategoryTheory.SubobjectRepresentableBy.classifier`: any representation `Ω` of
  `CategoryTheory.Subobject.presheaf C` is a subobject classifier in `C`.

* `CategoryTheory.hasClassifier_isRepresentable_iff`: from the two above mappings, we get that a
  category `C` with pullbacks has a subobject classifier if and only if the subobjects presheaf
  `CategoryTheory.Subobject.presheaf C` is representable (Proposition 1 in Section I.3 of [MM92]).

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

-/

@[expose] public section

universe v v₀ u u₀

namespace CategoryTheory

open Category Limits CategoryTheory.Functor IsPullback

variable {C : Type u} [Category.{v} C]

namespace Subobject

/-- A monomorphism `truth : Ω₀ ⟶ Ω` is a subobject classifier if, for every monomorphism
`m : U ⟶ X` in `C`, there is a unique map `χ : X ⟶ Ω` such that for some (necessarily unique)
`χ₀ : U ⟶ Ω₀` the following square is a pullback square:
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
An equivalent formulation replaces `Ω₀` with the terminal object.
-/
/-
**CategoryTheory.Subobject.Classifier** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.
Subobject`。
形式化陈述：Classifier (C : Type u) [Category.{v} C] where /-- The domain of the truth
 morphism -/ Ω₀ : C /-- The codomain of the truth morphism -/ Ω : C /-- The trut
h morphism of the subobject classifier -/ truth : Ω₀ ⟶ Ω /-- The truth morphism 
is a monomorphism -/ mono_truth : Mono truth
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monomorphism `truth : Ω₀ ⟶ Ω` is a subobject classifier if, for every monomorp
hism
`m : U ⟶ X` in `C`, there is a unique map `χ : X ⟶ Ω` such that for some (necess
arily unique)
`χ₀ : U ⟶ Ω₀` the following square is a pullback square:
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
An equivalent formulation replaces `Ω₀` with the terminal object.
-/
structure Classifier (C : Type u) [Category.{v} C] where
  /-- The domain of the truth morphism -/
  Ω₀ : C
  /-- The codomain of the truth morphism -/
  Ω : C
  /-- The truth morphism of the subobject classifier -/
  truth : Ω₀ ⟶ Ω
  /-- The truth morphism is a monomorphism -/
  mono_truth : Mono truth := by infer_instance
  /-- The top arrow in the pullback square -/
  χ₀ (U : C) : U ⟶ Ω₀
  /-- For any monomorphism `U ⟶ X`, there is an associated characteristic map `X ⟶ Ω`. -/
  χ {U X : C} (m : U ⟶ X) [Mono m] : X ⟶ Ω
  /-- `χ₀ U` and `χ m` form the appropriate pullback square. -/
  isPullback {U X : C} (m : U ⟶ X) [Mono m] : IsPullback m (χ₀ U) (χ m) truth
  /-- `χ m` is the only map `X ⟶ Ω` which forms the appropriate pullback square for any `χ₀'`. -/
  uniq {U X : C} (m : U ⟶ X) [Mono m] {χ₀' : U ⟶ Ω₀} {χ' : X ⟶ Ω}
    (hχ' : IsPullback m χ₀' χ' truth) : χ' = χ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier := Classifier

namespace Classifier

attribute [instance] mono_truth

/-- More explicit constructor in case `Ω₀` is already known to be a terminal object. -/
@[simps]
/-
**CategoryTheory.Subobject.Classifier.mkOfTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Subobject.Classifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
More explicit constructor in case `Ω₀` is already known to be a terminal object.
-/
def mkOfTerminalΩ₀
    (Ω₀ : C)
    (t : IsTerminal Ω₀)
    (Ω : C)
    (truth : Ω₀ ⟶ Ω)
    (χ : ∀ {U X : C} (m : U ⟶ X) [Mono m], X ⟶ Ω)
    (isPullback : ∀ {U X : C} (m : U ⟶ X) [Mono m],
      IsPullback m (t.from U) (χ m) truth)
    (uniq : ∀ {U X : C} (m : U ⟶ X) [Mono m] (χ' : X ⟶ Ω)
      (_ : IsPullback m (t.from U) χ' truth), χ' = χ m) : Classifier C where
  Ω₀ := Ω₀
  Ω := Ω
  truth := truth
  mono_truth := t.mono_from _
  χ₀ := t.from
  χ m _ := χ m
  isPullback m _ := isPullback m
  uniq m _ χ₀' χ' hχ' := uniq m χ' ((t.hom_ext χ₀' (t.from _)) ▸ hχ')

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.mkOfTerminalΩ₀ := mkOfTerminalΩ₀
/-
**CategoryTheory.Subobject.Classifier.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Subobject.Classifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {c : Classifier C} : ∀ Y : C, Unique (Y ⟶ c.Ω₀) := fun Y =>
  { default := c.χ₀ Y,
    uniq f :=
      have : f ≫ c.truth = c.χ₀ Y ≫ c.truth := calc
          _ = c.χ (𝟙 Y) := c.uniq (𝟙 Y) (of_horiz_isIso_mono { })
          _ = c.χ₀ Y ≫ c.truth := by simp [← (c.isPullback (𝟙 Y)).w]
      Mono.right_cancellation _ _ this }

/-- Given `c : Classifier C`, `c.Ω₀` is a terminal object.
Prefer `c.χ₀` over `c.isTerminalΩ₀.from`. -/
/-
**CategoryTheory.Subobject.Classifier.isTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Subobject.Classifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `c : Classifier C`, `c.Ω₀` is a terminal object.
Prefer `c.χ₀` over `c.isTerminalΩ₀.from`.
-/
def isTerminalΩ₀ {c : Classifier C} : IsTerminal c.Ω₀ := IsTerminal.ofUnique c.Ω₀

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.isTerminalΩ₀ := isTerminalΩ₀

@[simp]
/-
**CategoryTheory.Subobject.Classifier.isTerminalFrom_eq_** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Subobject.Classifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isTerminalFrom_eq_χ₀ (c : Classifier C) : c.isTerminalΩ₀.from = c.χ₀ := rfl

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.isTerminalFrom_eq_χ₀ := isTerminalFrom_eq_χ₀

end Subobject.Classifier

open CategoryTheory.Subobject
/-- A category `C` has a subobject classifier if there is at least one subobject classifier. -/
/-
**CategoryTheory.HasSubobjectClassifier** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` has a subobject classifier if there is at least one subobject cla
ssifier.
-/
class HasSubobjectClassifier (C : Type u) [Category.{v} C] : Prop where
  /-- There is some classifier. -/
  exists_classifier : Nonempty (Subobject.Classifier C)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier := HasSubobjectClassifier

namespace HasSubobjectClassifier

variable [HasSubobjectClassifier C]

noncomputable section
variable (C)

/-- Notation for the `Ω₀` in an arbitrary choice of a subobject classifier -/
/-
**CategoryTheory.HasSubobjectClassifier.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.HasSubobjectClassifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Notation for the `Ω₀` in an arbitrary choice of a subobject classifier
-/
abbrev Ω₀ : C := HasSubobjectClassifier.exists_classifier.some.Ω₀

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.Ω₀ := Ω₀

/-- Notation for the `Ω` in an arbitrary choice of a subobject classifier -/
/-
**CategoryTheory.HasSubobjectClassifier.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.HasSubobjectClassifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Notation for the `Ω` in an arbitrary choice of a subobject classifier
-/
abbrev Ω : C := HasSubobjectClassifier.exists_classifier.some.Ω

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.Ω := Ω

/-- Notation for the "truth arrow" in an arbitrary choice of a subobject classifier -/
/-
**CategoryTheory.HasSubobjectClassifier.truth** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.HasSubobjectClassifier`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.HasSubobjectClassifier C] →       CategoryTheory.HasSubobjectCla
ssifier.Ω₀ C ⟶ CategoryTheory.HasSubobjectClassifier.Ω C
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasSubobjectClassifier.exists_classifier`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.HasSubobjectCla
ssifier C],   Nonempty (CategoryTheory.Subobj…

--- 原说明 ---
Notation for the "truth arrow" in an arbitrary choice of a subobject classifier
-/
abbrev truth : Ω₀ C ⟶ Ω C := HasSubobjectClassifier.exists_classifier.some.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truth := truth

variable {C} {U X : C} (m : U ⟶ X) [Mono m]

/-- returns the characteristic morphism of the subobject `(m : U ⟶ X) [Mono m]` -/
/-
**CategoryTheory.HasSubobjectClassifier.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.HasSubobjectClassifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
returns the characteristic morphism of the subobject `(m : U ⟶ X) [Mono m]`
-/
def χ : X ⟶ Ω C :=
  HasSubobjectClassifier.exists_classifier.some.χ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.χ := χ

/-- The diagram
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
is a pullback square.
-/
/-
**CategoryTheory.HasSubobjectClassifier.isPullback_** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.HasSubobjectClassifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
is a pullback square.
-/
lemma isPullback_χ : IsPullback m (Classifier.χ₀ _ U) (χ m) (truth C) :=
  Classifier.isPullback _ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.isPullback_χ := isPullback_χ

/-- The diagram
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
commutes.
-/
@[reassoc]
/-
**CategoryTheory.HasSubobjectClassifier.comm** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.HasSubobjectClassifier`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.HasSubobjectClassifier C] {U X : C}   (m : U ⟶ X) [inst_2 : CategoryTheo
ry.Mono m],   CategoryTheory.CategoryStruct.comp m (CategoryTheory.HasSubobjectC
lassifier.χ m) =     CategoryTheory.CategoryStruct.comp (⋯.some.χ₀ U) (CategoryT
heory.HasSubobjectClassifier.truth C)
参数：m : U ⟶ X；CategoryTheory.HasSubobjectClassifier.χ m；⋯.some.χ₀ U；CategoryTheor
y.HasSubobjectClassifier.truth C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.HasSubobjectClassifier.exists_classifier`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.HasSubobjectCla
ssifier C],   Nonempty (CategoryTheory.Subobj…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.HasSubobjectClassifier.isPullback_χ`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasSubobjectClassi
fier C] {U X : C}   (m : U ⟶ X) [inst_2 …

--- 原说明 ---
The diagram
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
commutes.
-/
lemma comm : m ≫ χ m = Classifier.χ₀ _ U ≫ truth C := (isPullback_χ m).w

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.comm := comm

/-- `χ m` is the only map for which the associated square
is a pullback square.
-/
/-
**CategoryTheory.HasSubobjectClassifier.unique** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.HasSubobjectClassifier`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.HasSubobjectClassifier C] {U X : C}   (m : U ⟶ X) [inst_2 : CategoryTheo
ry.Mono m] (χ' : X ⟶ CategoryTheory.HasSubobjectClassifier.Ω C),   CategoryTheor
y.IsPullback m (⋯.some.χ₀ U) χ' (CategoryTheory.HasSubobjectClassifier.truth C) 
→     χ' = CategoryTheory.HasSubobjectClassifier.χ m
参数：m : U ⟶ X；χ' : X ⟶ CategoryTheory.HasSubobjectClassifier.Ω C；⋯.some.χ₀ U；Cate
goryTheory.HasSubobjectClassifier.truth C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasSubobjectClassifier.exists_classifier`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.HasSubobjectCla
ssifier C],   Nonempty (CategoryTheory.Subobj…
· 使用定理 `CategoryTheory.Subobject.Classifier.uniq`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] (self : CategoryTheory.Subobject.Classifier C) {U X :
 C}   (m : U ⟶ X) [inst_1 : Ca…

--- 原说明 ---
`χ m` is the only map for which the associated square
is a pullback square.
-/
lemma unique (χ' : X ⟶ Ω C) (hχ' : IsPullback m (Classifier.χ₀ _ U) χ' (truth C)) : χ' = χ m :=
  Classifier.uniq _ m hχ'

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.unique := unique
/-
**CategoryTheory.HasSubobjectClassifier.truthIsSplitMono** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.HasSubobjectClassifier`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.HasSubobjectClassifier C],   CategoryTheory.IsSplitMono (CategoryTheory.
HasSubobjectClassifier.truth C)
参数：CategoryTheory.HasSubobjectClassifier.truth C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.isSplitMono_from`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTe
rminal X)   (f : X ⟶ Y), CategoryTheory…
· 使用定理 `CategoryTheory.HasSubobjectClassifier.exists_classifier`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.HasSubobjectCla
ssifier C],   Nonempty (CategoryTheory.Subobj…
-/
instance truthIsSplitMono : IsSplitMono (truth C) :=
  Subobject.Classifier.isTerminalΩ₀.isSplitMono_from _

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truthIsSplitMono := truthIsSplitMono

/-- `truth C` is a regular monomorphism (because it is split). -/
/-
**CategoryTheory.HasSubobjectClassifier.truthIsRegularMono** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.HasSubobjectClassifier`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.HasSubobjectClassifier C] →       CategoryTheory.RegularMono (Ca
tegoryTheory.HasSubobjectClassifier.truth C)
参数：CategoryTheory.HasSubobjectClassifier.truth C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasSubobjectClassifier.truthIsSplitMono`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasSubobjectCl
assifier C],   CategoryTheory.IsSplitMono (C…

--- 原说明 ---
`truth C` is a regular monomorphism (because it is split).
-/
noncomputable def truthIsRegularMono : RegularMono (truth C) :=
  RegularMono.ofIsSplitMono (truth C)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truthIsRegularMono := truthIsRegularMono
/-
**CategoryTheory.HasSubobjectClassifier.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.HasSubobjectClassifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsRegularMono (truth C) := ⟨⟨truthIsRegularMono⟩⟩

/-- The following diagram
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
being a pullback for any monic `m` means that every monomorphism
in `C` is the pullback of a regular monomorphism; since regularity
is stable under base change, every monomorphism is regular.
Hence, `C` is a regular mono category.
It also follows that `C` is a balanced category.
-/
/-
**CategoryTheory.HasSubobjectClassifier.isRegularMonoCategory** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.HasSubobjectClassifier`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.H
asSubobjectClassifier C],   CategoryTheory.IsRegularMonoCategory C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasSubobjectClassifier.exists_classifier`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.HasSubobjectCla
ssifier C],   Nonempty (CategoryTheory.Subobj…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.HasSubobjectClassifier.isPullback_χ`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasSubobjectClassi
fier C] {U X : C}   (m : U ⟶ X) [inst_2 …

--- 原说明 ---
The following diagram
```
      U ---------m----------> X
      |                       |
    χ₀ U                     χ m
      |                       |
      v                       v
      Ω₀ ------truth--------> Ω
```
being a pullback for any monic `m` means that every monomorphism
in `C` is the pullback of a regular monomorphism; since regularity
is stable under base change, every monomorphism is regular.
Hence, `C` is a regular mono category.
It also follows that `C` is a balanced category.
-/
instance isRegularMonoCategory : IsRegularMonoCategory C where
  regularMonoOfMono :=
    fun m => ⟨⟨regularOfIsPullbackFstOfRegular truthIsRegularMono
      (isPullback_χ m).w (isPullback_χ m).isLimit⟩⟩

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.isRegularMonoCategory := isRegularMonoCategory

/-- If the source of a faithful functor has a subobject classifier, the functor reflects
  isomorphisms. This holds for any balanced category.
-/
/-
**CategoryTheory.HasSubobjectClassifier.reflectsIsomorphisms** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.HasSubobjectClassifier`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.H
asSubobjectClassifier C] (D : Type u₀)   [inst_2 : CategoryTheory.Category.{v₀, 
u₀} D] (F : CategoryTheory.Functor C D) [F.Faithful], F.ReflectsIsomorphisms
参数：D : Type u₀；F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflects
Epimorphisms`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D 
: Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [CategoryThe…
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.HasSubobjectClassifier.isRegularMonoCategory`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.HasSubobjectClassi
fier C],   CategoryTheory.IsRegularMonoCategory C
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If the source of a faithful functor has a subobject classifier, the functor refl
ects
  isomorphisms. This holds for any balanced category.
-/
instance reflectsIsomorphisms (D : Type u₀) [Category.{v₀} D] (F : C ⥤ D) [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.reflectsIsomorphisms := reflectsIsomorphisms

/-- If the source of a faithful functor is the opposite category of one with a subobject classifier,
  the same holds -- the functor reflects isomorphisms.
-/
/-
**CategoryTheory.HasSubobjectClassifier.reflectsIsomorphismsOp** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.HasSubobjectClassifier`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.H
asSubobjectClassifier C] (D : Type u₀)   [inst_2 : CategoryTheory.Category.{v₀, 
u₀} D] (F : CategoryTheory.Functor Cᵒᵖ D) [F.Faithful], F.ReflectsIsomorphisms
参数：D : Type u₀；F : CategoryTheory.Functor Cᵒᵖ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflects
Epimorphisms`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D 
: Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [CategoryThe…
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.HasSubobjectClassifier.isRegularMonoCategory`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.HasSubobjectClassi
fier C],   CategoryTheory.IsRegularMonoCategory C
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If the source of a faithful functor is the opposite category of one with a subob
ject classifier,
  the same holds -- the functor reflects isomorphisms.
-/
instance reflectsIsomorphismsOp (D : Type u₀) [Category.{v₀} D] (F : Cᵒᵖ ⥤ D)
    [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.reflectsIsomorphismsOp := reflectsIsomorphismsOp

end
end HasSubobjectClassifier

/-! ### The representability theorem of subobject classifiers -/

section Representability

namespace Subobject.Classifier

/-! #### From classifiers to representations -/

section RepresentableBy

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (𝒞 : Classifier C)

/-- The subobject of `𝒞.Ω` corresponding to the `truth` morphism. -/
/-
**CategoryTheory.Subobject.Classifier.truth_as_subobject** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Subobject.Classifier`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → (𝒞 : Category
Theory.Subobject.Classifier C) → CategoryTheory.Subobject 𝒞.Ω
参数：𝒞 : CategoryTheory.Subobject.Classifier C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.Classifier.mono_truth`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (self : CategoryTheory.Subobject.Classifier C),
   CategoryTheory.Mono self.truth

--- 原说明 ---
The subobject of `𝒞.Ω` corresponding to the `truth` morphism.
-/
abbrev truth_as_subobject : Subobject 𝒞.Ω :=
  Subobject.mk 𝒞.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.truth_as_subobject := truth_as_subobject
/-
**CategoryTheory.Subobject.Classifier.surjective_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Subobject.Classifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma surjective_χ {X : C} (φ : X ⟶ 𝒞.Ω) :
    ∃ (Z : C) (i : Z ⟶ X) (_ : Mono i), φ = 𝒞.χ i :=
  ⟨Limits.pullback φ 𝒞.truth, pullback.fst _ _, inferInstance, 𝒞.uniq _ (by
    convert! IsPullback.of_hasPullback φ 𝒞.truth)⟩

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.surjective_χ := surjective_χ

@[simp]
/-
**CategoryTheory.Subobject.Classifier.pullback_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Subobject.Classifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback_χ_obj_mk_truth {Z X : C} (i : Z ⟶ X) [Mono i] :
    (Subobject.pullback (𝒞.χ i)).obj 𝒞.truth_as_subobject = .mk i :=
  Subobject.pullback_obj_mk (𝒞.isPullback i).flip

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.pullback_χ_obj_mk_truth := pullback_χ_obj_mk_truth

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Subobject.Classifier.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Subobject.Classifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma χ_pullback_obj_mk_truth_arrow {X : C} (φ : X ⟶ 𝒞.Ω) :
    𝒞.χ ((Subobject.pullback φ).obj 𝒞.truth_as_subobject).arrow = φ := by
  obtain ⟨Z, i, _, rfl⟩ := 𝒞.surjective_χ φ
  refine (𝒞.uniq _ (?_ : IsPullback _ (𝒞.χ₀ _) _ _)).symm
  refine (IsPullback.of_hasPullback 𝒞.truth (𝒞.χ i)).flip.of_iso
    (underlyingIso _).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ (𝒞.isTerminalΩ₀.hom_ext _ _) (by simp) (by simp)
  dsimp
  rw [Iso.eq_inv_comp, comp_id, underlyingIso_hom_comp_eq_mk]
  rfl

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.χ_pullback_obj_mk_truth_arrow :=
  χ_pullback_obj_mk_truth_arrow

set_option backward.isDefEq.respectTransparency false in
/-- Any subobject classifier `Ω` represents the subobjects functor `Subobject.presheaf`. -/
/-
**CategoryTheory.Subobject.Classifier.representableBy** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Subobject.Classifier`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasPullbacks C] →       (𝒞 : CategoryTheory.Subobject.Cla
ssifier C) → (Subobject.presheaf C).RepresentableBy 𝒞.Ω
参数：𝒞 : CategoryTheory.Subobject.Classifier C；Subobject.presheaf C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any subobject classifier `Ω` represents the subobjects functor `Subobject.preshe
af`.
-/
noncomputable def representableBy :
    (Subobject.presheaf C).RepresentableBy 𝒞.Ω where
  homEquiv := {
    toFun φ := (Subobject.pullback φ).obj 𝒞.truth_as_subobject
    invFun x := 𝒞.χ x.arrow
    left_inv φ := by simp
    right_inv x := by simp
  }
  homEquiv_comp _ _ := by simp [pullback_comp]

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.representableBy :=
  representableBy

end RepresentableBy
end Subobject.Classifier

/-! #### From representations to classifiers -/

section FromRepresentation

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (Ω : C)

/-- Abbreviation to enable dot notation on the hypothesis `h` stating that the subobjects presheaf
is representable by some object `Ω`. -/
/-
**CategoryTheory.SubobjectRepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheo
ry.Limits.HasPullbacks C] → C → Type (max (max u u v) v)
参数：max (max u u v) v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation to enable dot notation on the hypothesis `h` stating that the subob
jects presheaf
is representable by some object `Ω`.
-/
abbrev SubobjectRepresentableBy := (Subobject.presheaf C).RepresentableBy Ω

@[deprecated (since := "2026-03-06")]
alias Classifier.SubobjectRepresentableBy := SubobjectRepresentableBy

variable {Ω} (h : SubobjectRepresentableBy Ω)

namespace SubobjectRepresentableBy

/-- `h.Ω₀` is the subobject of `Ω` which corresponds to the identity `𝟙 Ω`,
given `h : SubobjectRepresentableBy Ω`. -/
/-
**CategoryTheory.SubobjectRepresentableBy.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.SubobjectRepresentableBy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`h.Ω₀` is the subobject of `Ω` which corresponds to the identity `𝟙 Ω`,
given `h : SubobjectRepresentableBy Ω`.
-/
def Ω₀ : Subobject Ω := h.homEquiv (𝟙 Ω)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.Ω₀ := Ω₀
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.Ω₀ := Ω₀

/-- `h.homEquiv` acts like an "object comprehension" operator: it maps any characteristic map
`f : X ⟶ Ω` to the associated subobject of `X`, obtained by pulling back `h.Ω₀` along `f`. -/
/-
**CategoryTheory.SubobjectRepresentableBy.homEquiv_eq** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.SubobjectRepresentableBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasPullbacks C] {Ω : C}   (h : CategoryTheory.SubobjectRepresenta
bleBy Ω) {X : C} (f : X ⟶ Ω),   h.homEquiv f = (CategoryTheory.Subobject.pullbac
k f).obj h.Ω₀
参数：h : CategoryTheory.SubobjectRepresentableBy Ω；f : X ⟶ Ω；CategoryTheory.Subobj
ect.pullback f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subobject.presheaf_map`：∀ (C : Type u) [inst : CategoryTheory.Category.{
v, u} C] [inst_1 : CategoryTheory.Limits.HasPullbacks C] {X Y : Cᵒᵖ}   (f : X ⟶ 
Y), (Subobje…
· 使用定理 `CategoryTheory.Functor.RepresentableBy.homEquiv_comp`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Type 
v)} {Y : C}   (self : F.RepresentableBy Y)…

--- 原说明 ---
`h.homEquiv` acts like an "object comprehension" operator: it maps any character
istic map
`f : X ⟶ Ω` to the associated subobject of `X`, obtained by pulling back `h.Ω₀` 
along `f`.
-/
lemma homEquiv_eq {X : C} (f : X ⟶ Ω) :
    h.homEquiv f = (Subobject.pullback f).obj h.Ω₀ := by
  simpa using! h.homEquiv_comp f (𝟙 _)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.homEquiv_eq := homEquiv_eq
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.homEquiv_eq := homEquiv_eq

set_option backward.isDefEq.respectTransparency.types false in
/-- For any subobject `x`, the pullback of `h.Ω₀` along the characteristic map of `x`
given by `h.homEquiv` is `x` itself. -/
/-
**CategoryTheory.SubobjectRepresentableBy.pullback_homEquiv_symm_obj_** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.SubobjectRepresentableBy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any subobject `x`, the pullback of `h.Ω₀` along the characteristic map of `x
`
given by `h.homEquiv` is `x` itself.
-/
lemma pullback_homEquiv_symm_obj_Ω₀ {X : C} (x : Subobject X) :
    (Subobject.pullback (h.homEquiv.symm x)).obj h.Ω₀ = x := by
  rw [← homEquiv_eq, Equiv.apply_symm_apply]

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.pullback_homEquiv_symm_obj_Ω₀ :=
  pullback_homEquiv_symm_obj_Ω₀
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.pullback_homEquiv_symm_obj_Ω₀ :=
  pullback_homEquiv_symm_obj_Ω₀

section

variable {U X : C} (m : U ⟶ X) [Mono m]

/-- `h.χ m` is the characteristic map of monomorphism `m` given by the bijection `h.homEquiv`. -/
/-
**CategoryTheory.SubobjectRepresentableBy.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.SubobjectRepresentableBy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`h.χ m` is the characteristic map of monomorphism `m` given by the bijection `h.
homEquiv`.
-/
def χ : X ⟶ Ω := h.homEquiv.symm (Subobject.mk m)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.χ := χ
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.χ := χ

/-- `h.iso m` is the isomorphism between `m` and the pullback of `Ω₀`
    along the characteristic map of `m`. -/
/-
**CategoryTheory.SubobjectRepresentableBy.iso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.SubobjectRepresentableBy`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasPullbacks C] →       {Ω : C} →         (h : CategoryTh
eory.SubobjectRepresentableBy Ω) →           {U X : C} →             (m : U ⟶ X)
 →               [inst_2 : CategoryTheory.Mono m] →                 CategoryTheo
ry.MonoOver.mk m ≅                   CategoryTheory.Subobject.representative.obj
 ((CategoryTheory.Subobject.pullback (h.χ m)).obj h.Ω₀)
参数：h : CategoryTheory.SubobjectRepresentableBy Ω；m : U ⟶ X；(CategoryTheory.Subob
ject.pullback (h.χ m)).obj h.Ω₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`h.iso m` is the isomorphism between `m` and the pullback of `Ω₀`
    along the characteristic map of `m`.
-/
noncomputable def iso : MonoOver.mk m ≅
    Subobject.representative.obj ((Subobject.pullback (h.χ m)).obj h.Ω₀) :=
  (Subobject.representativeIso (.mk m)).symm ≪≫ Subobject.representative.mapIso
    (eqToIso (h.pullback_homEquiv_symm_obj_Ω₀ (.mk m)).symm)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.iso := iso
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.iso := iso

/-- `h.π m` is the first projection in the following pullback square:

    ```
    U --h.π m--> (Ω₀ : C)
    |                |
    m             Ω₀.arrow
    |                |
    v                v
    X -----h.χ m---> Ω
    ```
-/
/-
**CategoryTheory.SubobjectRepresentableBy.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.SubobjectRepresentableBy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`h.π m` is the first projection in the following pullback square:

    ```
    U --h.π m--> (Ω₀ : C)
    |                |
    m             Ω₀.arrow
    |                |
    v                v
    X -----h.χ m---> Ω
    ```
-/
noncomputable def π : U ⟶ Subobject.underlying.obj h.Ω₀ :=
  (h.iso m).hom.hom.left ≫ Subobject.pullbackπ (h.χ m) h.Ω₀

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.π := π
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.π := π

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SubobjectRepresentableBy.iso_inv_left_** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.SubobjectRepresentableBy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iso_inv_left_π :
    (h.iso m).inv.hom.left ≫ h.π m = Subobject.pullbackπ (h.χ m) h.Ω₀ := by
  dsimp only [π]
  rw [← Over.comp_left_assoc]
  convert! Category.id_comp _ using 2
  exact (MonoOver.forget _ ⋙ Over.forget _).congr_map (h.iso m).inv_hom_id

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.iso_inv_left_π := iso_inv_left_π
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.iso_inv_left_π := iso_inv_left_π

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SubobjectRepresentableBy.iso_inv_hom_left_comp** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.SubobjectRepresentableBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasPullbacks C] {Ω : C}   (h : CategoryTheory.SubobjectRepresenta
bleBy Ω) {U X : C} (m : U ⟶ X) [inst_2 : CategoryTheory.Mono m],   CategoryTheor
y.CategoryStruct.comp (CategoryTheory.Over.Hom.left (h.iso m).inv.hom) m =     (
(CategoryTheory.Subobject.pullback (h.χ m)).obj h.Ω₀).arrow
参数：h : CategoryTheory.SubobjectRepresentableBy Ω；m : U ⟶ X；CategoryTheory.Over.H
om.left (h.iso m).inv.hom；(CategoryTheory.Subobject.pullback (h.χ m)).obj h.Ω₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoOver.w`：w {f g : MonoOver X} (k : f ⟶ g) : k.hom.left
 ≫ g.arrow = f.arrow

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma iso_inv_hom_left_comp :
    (h.iso m).inv.hom.left ≫ m =
      ((Subobject.pullback (h.χ m)).obj h.Ω₀).arrow :=
  MonoOver.w (h.iso m).inv

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.iso_inv_hom_left_comp :=
  iso_inv_hom_left_comp
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.iso_inv_hom_left_comp :=
  iso_inv_hom_left_comp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SubobjectRepresentableBy.isPullback** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.SubobjectRepresentableBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasPullbacks C] {Ω : C}   (h : CategoryTheory.SubobjectRepresenta
bleBy Ω) {U X : C} (m : U ⟶ X) [inst_2 : CategoryTheory.Mono m],   CategoryTheor
y.IsPullback m (h.π m) (h.χ m) h.Ω₀.arrow
参数：h : CategoryTheory.SubobjectRepresentableBy Ω；m : U ⟶ X；h.π m；h.χ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.Subobject.isPullback`：isPullback (f : X ⟶ Y) (y : Subobje
ct Y) : IsPullback (pullbackπ f y) ((pullback f).obj y).arrow y.arrow f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.SubobjectRepresentableBy.iso_inv_hom_left_comp`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.
HasPullbacks C] {Ω : C}   (h : CategoryTheory.Subob…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.SubobjectRepresentableBy.iso_inv_left_π`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasPull
backs C] {Ω : C}   (h : CategoryTheory.Subob…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma isPullback {U X : C} (m : U ⟶ X) [Mono m] :
    IsPullback m (h.π m) (h.χ m) h.Ω₀.arrow := by
  fapply (Subobject.isPullback (h.χ m) h.Ω₀).flip.of_iso
    (((MonoOver.forget _ ⋙ Over.forget _).mapIso (h.iso m)).symm) (Iso.refl _)
    (Iso.refl _) (Iso.refl _)
  all_goals simp [MonoOver.forget]

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.isPullback := isPullback
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.isPullback := isPullback

variable {m}
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.SubobjectRepresentableBy.uniq** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.SubobjectRepresentableBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasPullbacks C] {Ω : C}   (h : CategoryTheory.SubobjectRepresenta
bleBy Ω) {U X : C} {m : U ⟶ X} [inst_2 : CategoryTheory.Mono m] {χ' : X ⟶ Ω}   {
π : U ⟶ CategoryTheory.Subobject.underlying.obj h.Ω₀}, CategoryTheory.IsPullback
 m π χ' h.Ω₀.arrow → χ' = h.χ m
参数：h : CategoryTheory.SubobjectRepresentableBy Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SubobjectRepresentableBy.homEquiv_eq`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasPullbac
ks C] {Ω : C}   (h : CategoryTheory.Subob…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subobject.mk_arrow`：mk_arrow (P : Subobject X) : mk P.arr
ow = P
· 使用定理 `CategoryTheory.Subobject.pullback_obj_mk`：pullback_obj_mk {A B X Y : C} 
{f : Y ⟶ X} {i : A ⟶ X} [Mono i] {j : B ⟶ Y} [Mono j] {f' : B ⟶ A} (h : IsPullba
ck f' j i f) : (pullback f).ob…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
lemma uniq {χ' : X ⟶ Ω} {π : U ⟶ h.Ω₀}
    (sq : IsPullback m π χ' h.Ω₀.arrow) : χ' = h.χ m := by
  apply h.homEquiv.injective
  simp only [χ, Equiv.apply_symm_apply, homEquiv_eq]
  simpa using! Subobject.pullback_obj_mk sq.flip

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.uniq := uniq
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.uniq := uniq

end

/-- The main non-trivial result: `h.Ω₀` is actually a terminal object. -/
/-
**CategoryTheory.SubobjectRepresentableBy.isTerminal** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.SubobjectRepresentableBy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The main non-trivial result: `h.Ω₀` is actually a terminal object.
-/
noncomputable def isTerminalΩ₀ : IsTerminal (h.Ω₀ : C) :=
  IsTerminal.ofUniqueHom (fun X ↦ h.π (𝟙 X)) (fun X π' ↦ by
    have : IsPullback (𝟙 X) π' (π' ≫ h.Ω₀.arrow) h.Ω₀.arrow :=
      { isLimit' := ⟨PullbackCone.IsLimit.mk _ (fun s ↦ s.fst) (by simp)
          (fun s ↦ by rw [← cancel_mono h.Ω₀.arrow, ← s.condition, Category.assoc])
          (fun s m hm _ ↦ by simpa using hm) ⟩ }
    rw [← cancel_mono h.Ω₀.arrow, h.uniq this,
      ← (h.isPullback (𝟙 X)).w, Category.id_comp])

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.isTerminalΩ₀ := isTerminalΩ₀
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.isTerminalΩ₀ := isTerminalΩ₀

/-- The unique map to the terminal object. -/
/-
**CategoryTheory.SubobjectRepresentableBy.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.SubobjectRepresentableBy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique map to the terminal object.
-/
noncomputable def χ₀ (U : C) : U ⟶ h.Ω₀ := h.isTerminalΩ₀.from U

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.χ₀ := χ₀
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.χ₀ := χ₀

include h in
/-
**CategoryTheory.SubobjectRepresentableBy.hasTerminal** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.SubobjectRepresentableBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasPullbacks C] {Ω : C}   (h : CategoryTheory.SubobjectRepresenta
bleBy Ω), CategoryTheory.Limits.HasTerminal C
参数：h : CategoryTheory.SubobjectRepresentableBy Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hasTerminal`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsTerminal 
X),   CategoryTheory.Limits.HasTer…
-/
lemma hasTerminal : HasTerminal C := h.isTerminalΩ₀.hasTerminal

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.hasTerminal := hasTerminal
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.hasTerminal := hasTerminal

variable [HasTerminal C]

/-- `h.isoΩ₀` is the unique isomorphism from `h.Ω₀` to the canonical terminal object `⊤_ C`. -/
/-
**CategoryTheory.SubobjectRepresentableBy.iso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.SubobjectRepresentableBy`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasPullbacks C] →       {Ω : C} →         (h : CategoryTh
eory.SubobjectRepresentableBy Ω) →           {U X : C} →             (m : U ⟶ X)
 →               [inst_2 : CategoryTheory.Mono m] →                 CategoryTheo
ry.MonoOver.mk m ≅                   CategoryTheory.Subobject.representative.obj
 ((CategoryTheory.Subobject.pullback (h.χ m)).obj h.Ω₀)
参数：h : CategoryTheory.SubobjectRepresentableBy Ω；m : U ⟶ X；(CategoryTheory.Subob
ject.pullback (h.χ m)).obj h.Ω₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`h.isoΩ₀` is the unique isomorphism from `h.Ω₀` to the canonical terminal object
 `⊤_ C`.
-/
noncomputable def isoΩ₀ : (h.Ω₀ : C) ≅ ⊤_ C :=
  h.isTerminalΩ₀.conePointUniqueUpToIso (limit.isLimit _)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.isoΩ₀ := isoΩ₀
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.isoΩ₀ := isoΩ₀

/-- Any representation `Ω` of `Subobject.presheaf C` gives a subobject classifier with truth values
object `Ω`. -/
/-
**CategoryTheory.SubobjectRepresentableBy.classifier** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.SubobjectRepresentableBy`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasPullbacks C] →       {Ω : C} →         CategoryTheory.
SubobjectRepresentableBy Ω →           [CategoryTheory.Limits.HasTerminal C] → C
ategoryTheory.Subobject.Classifier C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any representation `Ω` of `Subobject.presheaf C` gives a subobject classifier wi
th truth values
object `Ω`.
-/
noncomputable def classifier : Subobject.Classifier C where
  Ω₀ := ⊤_ C
  Ω := Ω
  truth := h.isoΩ₀.inv ≫ h.Ω₀.arrow
  mono_truth := terminalIsTerminal.mono_from _
  χ₀ := terminalIsTerminal.from
  χ m _ := h.χ m
  isPullback m _ :=
    (h.isPullback m).of_iso (Iso.refl _) (Iso.refl _) h.isoΩ₀ (Iso.refl _)
      (by simp) (Subsingleton.elim _ _) (by simp) (by simp)
  uniq {U X} m _ χ₀ χ' sq := by
    have : IsPullback m (h.χ₀ U) χ' h.Ω₀.arrow :=
      sq.of_iso (Iso.refl _) (Iso.refl _) (h.isoΩ₀.symm) (Iso.refl _)
        (by simp) (h.isTerminalΩ₀.hom_ext _ _) (by simp) (by simp)
    exact h.uniq this

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.classifier := classifier
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.classifier := classifier

end SubobjectRepresentableBy
end FromRepresentation

variable [HasTerminal C]

/-- A category has a subobject classifier if and only if the subobjects functor is representable. -/
/-
**CategoryTheory.hasSubobjectClassifier_iff_isRepresentable** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasTerminal C]   [inst_2 : CategoryTheory.Limits.HasPullbacks C],   Catego
ryTheory.HasSubobjectClassifier C ↔ (Subobject.presheaf C).IsRepresentable
参数：Subobject.presheaf C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.isRepresentable`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Typ
e v)} {Y : C}   (e : F.RepresentableBy Y), F…

--- 原说明 ---
A category has a subobject classifier if and only if the subobjects functor is r
epresentable.
-/
theorem hasSubobjectClassifier_iff_isRepresentable [HasPullbacks C] :
    HasSubobjectClassifier C ↔ (Subobject.presheaf C).IsRepresentable := by
  constructor <;> intro h
  · obtain ⟨⟨𝒞⟩⟩ := h
    apply RepresentableBy.isRepresentable
    exact 𝒞.representableBy
  · obtain ⟨Ω, ⟨h⟩⟩ := h
    constructor; constructor
    exact SubobjectRepresentableBy.classifier h

@[deprecated (since := "2026-03-06")]
alias isRepresentable_hasClassifier_iff := hasSubobjectClassifier_iff_isRepresentable

end Representability

namespace Subobject.Classifier
section Iso

/-- The unique morphism between classifiers mapping each others characteristic maps -/
/-
**CategoryTheory.Subobject.Classifier.hom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Subobject.Classifier`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → (𝒞₁ 𝒞₂ : Catego
ryTheory.Subobject.Classifier C) → 𝒞₁.Ω ⟶ 𝒞₂.Ω
参数：𝒞₁ 𝒞₂ : CategoryTheory.Subobject.Classifier C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.Classifier.mono_truth`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (self : CategoryTheory.Subobject.Classifier C),
   CategoryTheory.Mono self.truth

--- 原说明 ---
The unique morphism between classifiers mapping each others characteristic maps
-/
def hom (𝒞₁ 𝒞₂ : Classifier C) : 𝒞₁.Ω ⟶ 𝒞₂.Ω := 𝒞₂.χ 𝒞₁.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom := hom

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.Classifier.hom_comp_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Subobject.Classifier`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (𝒞₁ 𝒞₂ 𝒞₃ : Categ
oryTheory.Subobject.Classifier C),   CategoryTheory.CategoryStruct.comp (𝒞₁.hom 
𝒞₂) (𝒞₂.hom 𝒞₃) = 𝒞₁.hom 𝒞₃
参数：𝒞₁ 𝒞₂ 𝒞₃ : CategoryTheory.Subobject.Classifier C；𝒞₁.hom 𝒞₂；𝒞₂.hom 𝒞₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.Classifier.uniq`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] (self : CategoryTheory.Subobject.Classifier C) {U X :
 C}   (m : U ⟶ X) [inst_1 : Ca…
· 使用定理 `CategoryTheory.Subobject.Classifier.mono_truth`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (self : CategoryTheory.Subobject.Classifier C),
   CategoryTheory.Mono self.truth
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用定理 `CategoryTheory.Subobject.Classifier.isPullback`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (self : CategoryTheory.Subobject.Classifier C) 
{U X : C}   (m : U ⟶ X) [inst_1 : Ca…
-/
lemma hom_comp_hom (𝒞₁ 𝒞₂ 𝒞₃ : Classifier C) : 𝒞₁.hom 𝒞₂ ≫ 𝒞₂.hom 𝒞₃ = 𝒞₁.hom 𝒞₃ :=
  𝒞₃.uniq _ <| (𝒞₂.isPullback _).paste_vert (𝒞₃.isPullback _)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom_comp_hom := hom_comp_hom

@[simp]
/-
**CategoryTheory.Subobject.Classifier.hom_refl** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Subobject.Classifier`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (𝒞₁ : CategoryThe
ory.Subobject.Classifier C),   𝒞₁.hom 𝒞₁ = CategoryTheory.CategoryStruct.id 𝒞₁.Ω
参数：𝒞₁ : CategoryTheory.Subobject.Classifier C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.Classifier.mono_truth`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (self : CategoryTheory.Subobject.Classifier C),
   CategoryTheory.Mono self.truth
· 使用定理 `CategoryTheory.Subobject.Classifier.uniq`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] (self : CategoryTheory.Subobject.Classifier C) {U X :
 C}   (m : U ⟶ X) [inst_1 : Ca…
· 使用引理 `CategoryTheory.IsPullback.of_id_snd`：of_id_snd : IsPullback f (𝟙 _) (𝟙 _
) f
-/
lemma hom_refl (𝒞₁ : Classifier C) : 𝒞₁.hom 𝒞₁ = 𝟙 _ :=
  (𝒞₁.uniq (χ₀' := 𝟙 _) 𝒞₁.truth IsPullback.of_id_snd).symm

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom_refl := hom_refl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.Classifier.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Subobject.Classifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma χ_comp_hom {𝒞₁ 𝒞₂ : Classifier C} {X Y : C} (m : X ⟶ Y) [Mono m] :
    𝒞₁.χ m ≫ 𝒞₁.hom 𝒞₂ = 𝒞₂.χ m :=
  𝒞₂.uniq m ((𝒞₁.isPullback m).paste_vert (𝒞₂.isPullback 𝒞₁.truth))

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.χ_comp_hom := χ_comp_hom

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.Classifier.truth_comp_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Subobject.Classifier`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {𝒞₁ 𝒞₂ : Category
Theory.Subobject.Classifier C},   CategoryTheory.CategoryStruct.comp 𝒞₁.truth (𝒞
₁.hom 𝒞₂) = CategoryTheory.CategoryStruct.comp (𝒞₂.χ₀ 𝒞₁.Ω₀) 𝒞₂.truth
参数：𝒞₁.hom 𝒞₂；𝒞₂.χ₀ 𝒞₁.Ω₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.Subobject.Classifier.mono_truth`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (self : CategoryTheory.Subobject.Classifier C),
   CategoryTheory.Mono self.truth
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Subobject.Classifier.isPullback`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (self : CategoryTheory.Subobject.Classifier C) 
{U X : C}   (m : U ⟶ X) [inst_1 : Ca…
-/
lemma truth_comp_hom {𝒞₁ 𝒞₂ : Classifier C} :
  𝒞₁.truth ≫ 𝒞₁.hom 𝒞₂ = 𝒞₂.χ₀ _ ≫ 𝒞₂.truth := (𝒞₂.isPullback _).w

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.truth_comp_hom := truth_comp_hom

/-- a concrete equivalence of any two subobject classifiers -/
@[simps]
/-
**CategoryTheory.Subobject.Classifier.uniqueUpToIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Subobject.Classifier`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → (𝒞₁ 𝒞₂ : Catego
ryTheory.Subobject.Classifier C) → 𝒞₁.Ω ≅ 𝒞₂.Ω
参数：𝒞₁ 𝒞₂ : CategoryTheory.Subobject.Classifier C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
a concrete equivalence of any two subobject classifiers
-/
def uniqueUpToIso (𝒞₁ 𝒞₂ : Classifier C) : 𝒞₁.Ω ≅ 𝒞₂.Ω where
  hom := 𝒞₁.hom 𝒞₂
  inv := 𝒞₂.hom 𝒞₁

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.uniqueUpToIso := uniqueUpToIso
/-
**CategoryTheory.Subobject.Classifier.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Subobject.Classifier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (𝒞₁ 𝒞₂ : Classifier C) : IsIso (𝒞₁.hom 𝒞₂) := (𝒞₁.uniqueUpToIso 𝒞₂).isIso_hom

/-- Being a subobject classifier is preserved under isomorphism. -/
@[simps]
/-
**CategoryTheory.Subobject.Classifier.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Subobject.Classifier`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (𝒞 : Cate
goryTheory.Subobject.Classifier C) →       {Ω₀ Ω : C} →         (eΩ : 𝒞.Ω ≅ Ω) →
           (eΩ₀ : 𝒞.Ω₀ ≅ Ω₀) →             ((C_1 : C) → C_1 ⟶ Ω₀) →             
  (t : Ω₀ ⟶ Ω) →                 autoParam                     (t = CategoryTheo
ry.CategoryStruct.comp eΩ₀.inv (CategoryTheory.CategoryStruct.comp 𝒞.truth eΩ.ho
m))                     CategoryTheory.Subobject.Classifier.ofIso._auto_1 →     
              CategoryTheory.Subobject.Classifier C
参数：𝒞 : CategoryTheory.Subobject.Classifier C；eΩ : 𝒞.Ω ≅ Ω；eΩ₀ : 𝒞.Ω₀ ≅ Ω₀；(C_1 :
 C) → C_1 ⟶ Ω₀；t : Ω₀ ⟶ Ω；t = CategoryTheory.CategoryStruct.comp eΩ₀.inv (Catego
ryTheory.CategoryStruct.comp 𝒞.truth eΩ.hom)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Being a subobject classifier is preserved under isomorphism.
-/
def ofIso (𝒞 : Classifier C) {Ω₀ Ω : C} (eΩ : 𝒞.Ω ≅ Ω) (eΩ₀ : 𝒞.Ω₀ ≅ Ω₀)
    (from' : ∀ C, C ⟶ Ω₀) (t : Ω₀ ⟶ Ω) (ht : t = eΩ₀.inv ≫ 𝒞.truth ≫ eΩ.hom := by cat_disch) :
    Classifier C where
  Ω₀ := Ω₀
  Ω := Ω
  truth := t
  mono_truth := ht ▸ inferInstance
  χ₀ := from'
  χ {F G} m _ := 𝒞.χ m ≫ eΩ.hom
  isPullback {F G} m _ := by
    rw [eΩ₀.comp_inv_eq.mp (Subsingleton.elim (from' F ≫ eΩ₀.inv) (𝒞.χ₀ F))]
    exact (𝒞.isPullback m).paste_vert (IsPullback.of_vert_isIso_mono (by simp [ht]))
  uniq {F G} m _ := by
    intro χ₀' χ' hχ'
    have : χ' ≫ eΩ.inv = 𝒞.χ m := by
      apply 𝒞.uniq m (χ₀' := χ₀' ≫ eΩ₀.inv)
      exact hχ'.paste_vert (IsPullback.of_vert_isIso_mono (by simp [ht]))
    simpa using this =≫ eΩ.hom

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.ofIso := ofIso

end Iso

section Equivalence

variable {D : Type*} [Category* D]

/--
The image of a subobject classifier under an equivalence of categories is a subobject classifier.
-/
@[simps]
/-
**CategoryTheory.Subobject.Classifier.ofEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Subobject.Classifier`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         Category
Theory.Subobject.Classifier C → (C ≌ D) → CategoryTheory.Subobject.Classifier D
参数：C ≌ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a subobject classifier under an equivalence of categories is a subo
bject classifier.
-/
def ofEquivalence (𝒞₁ : Classifier C) (e : C ≌ D) : Classifier D where
  Ω₀ := e.functor.obj 𝒞₁.Ω₀
  Ω := e.functor.obj 𝒞₁.Ω
  truth := e.functor.map 𝒞₁.truth
  χ₀ Y := e.counitInv.app Y ≫ e.functor.map (𝒞₁.χ₀ (e.inverse.obj Y))
  χ m := e.counitInv.app _ ≫ e.functor.map (𝒞₁.χ (e.inverse.map m))
  isPullback {F G} m _ := by
    apply ((𝒞₁.isPullback (e.inverse.map m)).map e.functor).of_iso (e.counitIso.app _)
      (e.counitIso.app _) (.refl _) (.refl _) <;> simp
  uniq {F G} m _ := by
    intro χ₀' χ' hχ'
    have : e.inverse.map χ' ≫ e.unitInv.app _ = 𝒞₁.χ (e.inverse.map m) := by
      apply 𝒞₁.uniq (e.inverse.map m) (χ₀' := e.inverse.map χ₀' ≫ e.unitInv.app _)
      exact (hχ'.map e.inverse).paste_vert <| IsPullback.of_vert_isIso_mono .mk
    simpa using congr(e.counitInv.app G ≫ e.functor.map $this)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.ofEquivalence := ofEquivalence

end Equivalence

end CategoryTheory.Subobject.Classifier

