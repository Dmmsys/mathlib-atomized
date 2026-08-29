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

/--
Definition of `Classifier` / `Classifier` 的定义

English:
structure Classifier
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (8):
    - Ω₀ : C
    - Ω : C
    - truth : Ω₀ ⟶ Ω
    - mono_truth : Mono truth  [default: by infer_instance]
    - χ₀((U : C)) : U ⟶ Ω₀
    - χ({U X : C} (m : U ⟶ X) [Mono m]) : X ⟶ Ω
    - isPullback({U X : C} (m : U ⟶ X) [Mono m]) : IsPullback m (χ₀ U) (χ m) truth
    - uniq({U X : C} (m : U ⟶ X) [Mono m] {χ₀' : U ⟶ Ω₀} {χ' : X ⟶ Ω} (hχ' : IsPullback m χ₀' χ' truth)) : χ' = χ m

中文:
结构 Classifier
  参数: (C : 类型u) [Category.{v} C]
  公理与运算 (8 个):
    - Ω₀ : C
    - Ω : C
    - truth : Ω₀ ⟶ Ω
    - mono_truth : Mono truth  [默认: by infer_instance]
    - χ₀((U : C)) : U ⟶ Ω₀
    - χ({U X : C} (m : U ⟶ X) [Mono m]) : X ⟶ Ω
    - isPullback({U X : C} (m : U ⟶ X) [Mono m]) : IsPullback m (χ₀ U) (χ m) truth
    - uniq({U X : C} (m : U ⟶ X) [Mono m] {χ₀' : U ⟶ Ω₀} {χ' : X ⟶ Ω} (hχ' : IsPullback m χ₀' χ' truth)) : χ' = χ m

Depends on / 依赖: infer_instance
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
/--
Definition of `mkOfTerminalΩ₀` / `mkOfTerminalΩ₀` 的定义

English:
definition mkOfTerminalΩ₀
  body: Ω₀
  Ω := Ω
  truth := truth
  mono_truth := t.mono_from _
  χ₀ := t.from
  χ m _ := χ m
  isPullback m _ := isPullback m
  uniq m _ χ₀' χ' hχ' := uniq m χ' ((t.hom_ext χ₀' (t.from _)) ▸ hχ')

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.mkOfTerminalΩ₀ := mkOfTerminal

中文:
定义 mkOfTerminalΩ₀
  定义体: Ω₀
  Ω := Ω
  truth := truth
  mono_truth := t.mono_from _
  χ₀ := t.from
  χ m _ := χ m
  isPullback m _ := isPullback m
  uniq m _ χ₀' χ' hχ' := uniq m χ' ((t.hom_ext χ₀' (t.from _)) ▸ hχ')

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.mkOfTerminalΩ₀ := mkOfTerminal
-/
def mkOfTerminalΩ₀
    (Ω₀ : C)
    (t : IsTerminal Ω₀)
    (Ω : C)
    (truth : Ω₀ ⟶ Ω)
    (χ : forall {U X : C} (m : U ⟶ X) [Mono m], X ⟶ Ω)
    (isPullback : forall {U X : C} (m : U ⟶ X) [Mono m],
      IsPullback m (t.from U) (χ m) truth)
    (uniq : forall {U X : C} (m : U ⟶ X) [Mono m] (χ' : X ⟶ Ω)
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

instance {c : Classifier C} : forall Y : C, Unique (Y ⟶ c.Ω₀) := fun Y =>
  { default := c.χ₀ Y,
    uniq f :=
      have : f ≫ c.truth = c.χ₀ Y ≫ c.truth := calc
          _ = c.χ (𝟙 Y) := c.uniq (𝟙 Y) (of_horiz_isIso_mono { })
          _ = c.χ₀ Y ≫ c.truth := by simp [← (c.isPullback (𝟙 Y)).w]
      Mono.right_cancellation _ _ this }

/--
Definition of `isTerminalΩ₀` / `isTerminalΩ₀` 的定义

English:
definition isTerminalΩ₀
  signature: {c : Classifier C}
  body: IsTerminal.ofUnique c.Ω₀

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.isTerminalΩ₀ := isTerminalΩ₀

@[simp]

中文:
定义 isTerminalΩ₀
  签名: {c : Classifier C}
  定义体: IsTerminal.ofUnique c.Ω₀

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.isTerminalΩ₀ := isTerminalΩ₀

@[simp]

Depends on / 依赖: IsTerminal, IsTerminal.ofUnique, ofUnique
-/
def isTerminalΩ₀ {c : Classifier C} : IsTerminal c.Ω₀ := IsTerminal.ofUnique c.Ω₀

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.isTerminalΩ₀ := isTerminalΩ₀

@[simp]
/--
lemma `isTerminalFrom_eq_χ₀` / 引理 `isTerminalFrom_eq_χ₀`

English:
lemma isTerminalFrom_eq_χ₀
  given: (c : Classifier C)
  statement: c.isTerminalΩ₀.from = c.χ₀
  proof: rfl

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.isTerminalFrom_eq_χ₀ := isTerminalFrom_eq_χ₀

中文:
引理 isTerminalFrom_eq_χ₀
  条件: (c : Classifier C)
  结论: c.isTerminalΩ₀.from = c.χ₀
  证明: rfl

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.isTerminalFrom_eq_χ₀ := isTerminalFrom_eq_χ₀
-/
lemma isTerminalFrom_eq_χ₀ (c : Classifier C) : c.isTerminalΩ₀.from = c.χ₀ := rfl

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.isTerminalFrom_eq_χ₀ := isTerminalFrom_eq_χ₀

end Subobject.Classifier

open CategoryTheory.Subobject
/--
Definition of `HasSubobjectClassifier` / `HasSubobjectClassifier` 的定义

English:
class HasSubobjectClassifier
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (1):
    - exists_classifier : Nonempty (Subobject.Classifier C)

中文:
类 HasSubobjectClassifier
  参数: (C : 类型u) [Category.{v} C]
  公理与运算 (1 个):
    - exists_classifier : Nonempty (Subobject.Classifier C)
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

/--
Definition of `Ω₀` / `Ω₀` 的定义

English:
abbreviation Ω₀
  signature: : C
  body: HasSubobjectClassifier.exists_classifier.some.Ω₀

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.Ω₀ := Ω₀

中文:
缩写 Ω₀
  签名: : C
  定义体: HasSubobjectClassifier.exists_classifier.some.Ω₀

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.Ω₀ := Ω₀

Depends on / 依赖: HasSubobjectClassifier, HasSubobjectClassifier.exists_classifier.some, exists_classifier
-/
abbrev Ω₀ : C := HasSubobjectClassifier.exists_classifier.some.Ω₀

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.Ω₀ := Ω₀

/--
Definition of `Ω` / `Ω` 的定义

English:
abbreviation Ω
  signature: : C
  body: HasSubobjectClassifier.exists_classifier.some.Ω

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.Ω := Ω

中文:
缩写 Ω
  签名: : C
  定义体: HasSubobjectClassifier.exists_classifier.some.Ω

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.Ω := Ω

Depends on / 依赖: HasSubobjectClassifier, HasSubobjectClassifier.exists_classifier.some, exists_classifier
-/
abbrev Ω : C := HasSubobjectClassifier.exists_classifier.some.Ω

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.Ω := Ω

/--
Definition of `truth` / `truth` 的定义

English:
abbreviation truth
  signature: : Ω₀ C ⟶ Ω C
  body: HasSubobjectClassifier.exists_classifier.some.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truth := truth

中文:
缩写 truth
  签名: : Ω₀ C ⟶ Ω C
  定义体: HasSubobjectClassifier.exists_classifier.some.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truth := truth

Depends on / 依赖: HasSubobjectClassifier, HasSubobjectClassifier.exists_classifier.some.truth, exists_classifier
-/
abbrev truth : Ω₀ C ⟶ Ω C := HasSubobjectClassifier.exists_classifier.some.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truth := truth

variable {C} {U X : C} (m : U ⟶ X) [Mono m]

/--
Definition of `χ` / `χ` 的定义

English:
definition χ
  signature: : X ⟶ Ω C
  body: HasSubobjectClassifier.exists_classifier.some.χ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.χ := χ

中文:
定义 χ
  签名: : X ⟶ Ω C
  定义体: HasSubobjectClassifier.exists_classifier.some.χ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.χ := χ

Depends on / 依赖: HasSubobjectClassifier, HasSubobjectClassifier.exists_classifier.some, exists_classifier
-/
def χ : X ⟶ Ω C :=
  HasSubobjectClassifier.exists_classifier.some.χ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.χ := χ

/--
lemma `isPullback_χ` / 引理 `isPullback_χ`

English:
lemma isPullback_χ
  statement: IsPullback m (Classifier.χ₀ _ U) (χ m) (truth C)
  proof: Classifier.isPullback _ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.isPullback_χ := isPullback_χ

中文:
引理 isPullback_χ
  结论: IsPullback m (Classifier.χ₀ _ U) (χ m) (truth C)
  证明: Classifier.isPullback _ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.isPullback_χ := isPullback_χ

Depends on / 依赖: Classifier, Classifier.isPullback, isPullback
-/
lemma isPullback_χ : IsPullback m (Classifier.χ₀ _ U) (χ m) (truth C) :=
  Classifier.isPullback _ m

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.isPullback_χ := isPullback_χ

/-- The diagram
```
      U ---------m----------> X
      | |
    χ₀ U χ m
      | |
      v v
      Ω₀ ------truth--------> Ω
```
commutes.
-/
@[reassoc]
/--
lemma `comm` / 引理 `comm`

English:
lemma comm
  statement: m ≫ χ m = Classifier.χ₀ _ U ≫ truth C
  proof: (isPullback_χ m).w

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.comm := comm

中文:
引理 comm
  结论: m ≫ χ m = Classifier.χ₀ _ U ≫ truth C
  证明: (isPullback_χ m).w

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.comm := comm
-/
lemma comm : m ≫ χ m = Classifier.χ₀ _ U ≫ truth C := (isPullback_χ m).w

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.comm := comm

/--
lemma `unique` / 引理 `unique`

English:
lemma unique
  given: (χ' : X ⟶ Ω C) (hχ' : IsPullback m (Classifier.χ₀ _ U) χ' (truth C))
  statement: χ' = χ m
  proof: Classifier.uniq _ m hχ'

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.unique := unique

中文:
引理 unique
  条件: (χ' : X ⟶ Ω C) (hχ' : IsPullback m (Classifier.χ₀ _ U) χ' (truth C))
  结论: χ' = χ m
  证明: Classifier.uniq _ m hχ'

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.unique := unique

Depends on / 依赖: Classifier, Classifier.uniq
-/
lemma unique (χ' : X ⟶ Ω C) (hχ' : IsPullback m (Classifier.χ₀ _ U) χ' (truth C)) : χ' = χ m :=
  Classifier.uniq _ m hχ'

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.unique := unique

/--
Instance `truthIsSplitMono` / 实例 `truthIsSplitMono`

English:
instance truthIsSplitMono
  signature: : IsSplitMono (truth C)
  body: Subobject.Classifier.isTerminalΩ₀.isSplitMono_from _

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truthIsSplitMono := truthIsSplitMono

中文:
实例 truthIsSplitMono
  签名: : IsSplitMono (truth C)
  定义体: Subobject.Classifier.isTerminalΩ₀.isSplitMono_from _

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truthIsSplitMono := truthIsSplitMono

Depends on / 依赖: Classifier, Subobject, Subobject.Classifier.isTerminal, isSplitMono_from
-/
instance truthIsSplitMono : IsSplitMono (truth C) :=
  Subobject.Classifier.isTerminalΩ₀.isSplitMono_from _

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truthIsSplitMono := truthIsSplitMono

/--
Definition of `truthIsRegularMono` / `truthIsRegularMono` 的定义

English:
definition truthIsRegularMono
  signature: : RegularMono (truth C)
  body: RegularMono.ofIsSplitMono (truth C)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truthIsRegularMono := truthIsRegularMono

中文:
定义 truthIsRegularMono
  签名: : RegularMono (truth C)
  定义体: RegularMono.ofIsSplitMono (truth C)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truthIsRegularMono := truthIsRegularMono

Depends on / 依赖: RegularMono, RegularMono.ofIsSplitMono, ofIsSplitMono
-/
noncomputable def truthIsRegularMono : RegularMono (truth C) :=
  RegularMono.ofIsSplitMono (truth C)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.truthIsRegularMono := truthIsRegularMono

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsRegularMono (truth C)
  body: ⟨⟨truthIsRegularMono⟩⟩

中文:
实例 :
  签名: IsRegularMono (truth C)
  定义体: ⟨⟨truthIsRegularMono⟩⟩

Depends on / 依赖: truthIsRegularMono
-/
instance : IsRegularMono (truth C) := ⟨⟨truthIsRegularMono⟩⟩

/--
Instance `isRegularMonoCategory` / 实例 `isRegularMonoCategory`

English:
instance isRegularMonoCategory
  signature: : IsRegularMonoCategory C where
  body: fun m => ⟨⟨regularOfIsPullbackFstOfRegular truthIsRegularMono
      (isPullback_χ m).w (isPullback_χ m).isLimit⟩⟩

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.isRegularMonoCategory := isRegularMonoCategory

中文:
实例 isRegularMonoCategory
  签名: : IsRegularMonoCategory C where
  定义体: fun m => ⟨⟨regularOfIsPullbackFstOfRegular truthIsRegularMono
      (isPullback_χ m).w (isPullback_χ m).isLimit⟩⟩

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.isRegularMonoCategory := isRegularMonoCategory

Depends on / 依赖: isLimit, regularOfIsPullbackFstOfRegular, truthIsRegularMono
-/
instance isRegularMonoCategory : IsRegularMonoCategory C where
  regularMonoOfMono :=
    fun m => ⟨⟨regularOfIsPullbackFstOfRegular truthIsRegularMono
      (isPullback_χ m).w (isPullback_χ m).isLimit⟩⟩

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.isRegularMonoCategory := isRegularMonoCategory

/--
Instance `reflectsIsomorphisms` / 实例 `reflectsIsomorphisms`

English:
instance reflectsIsomorphisms
  signature: (D : Type u₀) [Category.{v₀} D] (F : C ⥤ D) [Functor.Faithful F]
  body: reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.reflectsIsomorphisms := reflectsIsomorphisms

中文:
实例 reflectsIsomorphisms
  签名: (D : 类型u₀) [Category.{v₀} D] (F : C ⥤ D) [Functor.Faithful F]
  定义体: reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.reflectsIsomorphisms := reflectsIsomorphisms

Depends on / 依赖: reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms
-/
instance reflectsIsomorphisms (D : Type u₀) [Category.{v₀} D] (F : C ⥤ D) [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.reflectsIsomorphisms := reflectsIsomorphisms

/--
Instance `reflectsIsomorphismsOp` / 实例 `reflectsIsomorphismsOp`

English:
instance reflectsIsomorphismsOp
  signature: (D : Type u₀) [Category.{v₀} D] (F : Cᵒᵖ ⥤ D)
  body: reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.reflectsIsomorphismsOp := reflectsIsomorphismsOp

中文:
实例 reflectsIsomorphismsOp
  签名: (D : 类型u₀) [Category.{v₀} D] (F : Cᵒᵖ ⥤ D)
  定义体: reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.HasClassifier.reflectsIsomorphismsOp := reflectsIsomorphismsOp

Depends on / 依赖: reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms
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

/--
Definition of `truth_as_subobject` / `truth_as_subobject` 的定义

English:
abbreviation truth_as_subobject
  signature: : Subobject 𝒞.Ω
  body: Subobject.mk 𝒞.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.truth_as_subobject := truth_as_subobject

中文:
缩写 truth_as_subobject
  签名: : Subobject 𝒞.Ω
  定义体: Subobject.mk 𝒞.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.truth_as_subobject := truth_as_subobject

Depends on / 依赖: Subobject, Subobject.mk
-/
abbrev truth_as_subobject : Subobject 𝒞.Ω :=
  Subobject.mk 𝒞.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.truth_as_subobject := truth_as_subobject

/--
lemma `surjective_χ` / 引理 `surjective_χ`

English:
lemma surjective_χ
  given: {X : C} (φ : X ⟶ 𝒞.Ω)
  proof: ⟨Limits.pullback φ 𝒞.truth, pullback.fst _ _, inferInstance, 𝒞.uniq _ (by
    convert! IsPullback.of_hasPullback φ 𝒞.truth)⟩

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.surjective_χ := surjective_χ

@[simp]

中文:
引理 surjective_χ
  条件: {X : C} (φ : X ⟶ 𝒞.Ω)
  证明: ⟨Limits.pullback φ 𝒞.truth, pullback.fst _ _, inferInstance, 𝒞.uniq _ (by
    convert! IsPullback.of_hasPullback φ 𝒞.truth)⟩

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.surjective_χ := surjective_χ

@[simp]

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, Limits, Limits.pullback, convert, of_hasPullback, pullback, pullback.fst
-/
lemma surjective_χ {X : C} (φ : X ⟶ 𝒞.Ω) :
    exists (Z : C) (i : Z ⟶ X) (_ : Mono i), φ = 𝒞.χ i :=
  ⟨Limits.pullback φ 𝒞.truth, pullback.fst _ _, inferInstance, 𝒞.uniq _ (by
    convert! IsPullback.of_hasPullback φ 𝒞.truth)⟩

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.surjective_χ := surjective_χ

@[simp]
/--
lemma `pullback_χ_obj_mk_truth` / 引理 `pullback_χ_obj_mk_truth`

English:
lemma pullback_χ_obj_mk_truth
  given: {Z X : C} (i : Z ⟶ X) [Mono i]
  proof: Subobject.pullback_obj_mk (𝒞.isPullback i).flip

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.pullback_χ_obj_mk_truth := pullback_χ_obj_mk_truth

中文:
引理 pullback_χ_obj_mk_truth
  条件: {Z X : C} (i : Z ⟶ X) [Mono i]
  证明: Subobject.pullback_obj_mk (𝒞.isPullback i).flip

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.pullback_χ_obj_mk_truth := pullback_χ_obj_mk_truth

Depends on / 依赖: Subobject, Subobject.pullback_obj_mk, isPullback, pullback_obj_mk
-/
lemma pullback_χ_obj_mk_truth {Z X : C} (i : Z ⟶ X) [Mono i] :
    (Subobject.pullback (𝒞.χ i)).obj 𝒞.truth_as_subobject = .mk i :=
  Subobject.pullback_obj_mk (𝒞.isPullback i).flip

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.pullback_χ_obj_mk_truth := pullback_χ_obj_mk_truth

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `χ_pullback_obj_mk_truth_arrow` / 引理 `χ_pullback_obj_mk_truth_arrow`

English:
lemma χ_pullback_obj_mk_truth_arrow
  given: {X : C} (φ : X ⟶ 𝒞.Ω)
  proof: by
  obtain ⟨Z, i, _, rfl⟩ := 𝒞.surjective_χ φ
  refine (𝒞.uniq _ (?_ : IsPullback _ (𝒞.χ₀ _) _ _)).symm
  refine (IsPullback.of_hasPullback 𝒞.truth (𝒞.χ i)).flip.of_iso
    (underlyingIso _).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ (𝒞.isTerminalΩ₀.hom_ext _ _) (by simp) (by simp)
  dsimp


中文:
引理 χ_pullback_obj_mk_truth_arrow
  条件: {X : C} (φ : X ⟶ 𝒞.Ω)
  证明: by
  obtain ⟨Z, i, _, rfl⟩ := 𝒞.surjective_χ φ
  refine (𝒞.uniq _ (?_ : IsPullback _ (𝒞.χ₀ _) _ _)).symm
  refine (IsPullback.of_hasPullback 𝒞.truth (𝒞.χ i)).flip.of_iso
    (underlyingIso _).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ (𝒞.isTerminalΩ₀.hom_ext _ _) (by simp) (by simp)
  dsimp


Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, Iso.eq_inv_comp, Iso.refl, comp_id, eq_inv_comp, flip.of_iso, hom_ext, of_hasPullback, of_iso, underlyingIso, underlyingIso_hom_comp_eq_mk
-/
lemma χ_pullback_obj_mk_truth_arrow {X : C} (φ : X ⟶ 𝒞.Ω) :
    𝒞.χ ((Subobject.pullback φ).obj 𝒞.truth_as_subobject).arrow = φ := by
  obtain ⟨Z, i, _, rfl⟩ := 𝒞.surjective_χ φ
  refine (𝒞.uniq _ (?_ : IsPullback _ (𝒞.χ₀ _) _ _)).symm
  refine (IsPullback.of_hasPullback 𝒞.truth (𝒞.χ i)).flip.of_iso
    (underlyingIso _).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ (𝒞.isTerminalΩ₀.hom_ext _ _) (by simp) (by simp)
  dsimp
  rw [Iso.eq_inv_comp]; rw [comp_id]; rw [underlyingIso_hom_comp_eq_mk]
  rfl

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.χ_pullback_obj_mk_truth_arrow :=
  χ_pullback_obj_mk_truth_arrow

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `representableBy` / `representableBy` 的定义

English:
definition representableBy
  signature: :
  body: {
    toFun φ := (Subobject.pullback φ).obj 𝒞.truth_as_subobject
    invFun x := 𝒞.χ x.arrow
    left_inv φ := by simp
    right_inv x := by simp
  }
  homEquiv_comp _ _ := by simp [pullback_comp]

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.representableBy :=
  repr

中文:
定义 representableBy
  签名: :
  定义体: {
    toFun φ := (Subobject.pullback φ).obj 𝒞.truth_as_subobject
    invFun x := 𝒞.χ x.arrow
    left_inv φ := by simp
    right_inv x := by simp
  }
  homEquiv_comp _ _ := by simp [pullback_comp]

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.representableBy :=
  repr
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

/--
Definition of `SubobjectRepresentableBy` / `SubobjectRepresentableBy` 的定义

English:
abbreviation SubobjectRepresentableBy
  body: (Subobject.presheaf C).RepresentableBy Ω

@[deprecated (since := "2026-03-06")]
alias Classifier.SubobjectRepresentableBy := SubobjectRepresentableBy

中文:
缩写 SubobjectRepresentableBy
  定义体: (Subobject.presheaf C).RepresentableBy Ω

@[deprecated (since := "2026-03-06")]
alias Classifier.SubobjectRepresentableBy := SubobjectRepresentableBy

Depends on / 依赖: RepresentableBy, Subobject, Subobject.presheaf, presheaf
-/
abbrev SubobjectRepresentableBy := (Subobject.presheaf C).RepresentableBy Ω

@[deprecated (since := "2026-03-06")]
alias Classifier.SubobjectRepresentableBy := SubobjectRepresentableBy

variable {Ω} (h : SubobjectRepresentableBy Ω)

namespace SubobjectRepresentableBy

/--
Definition of `Ω₀` / `Ω₀` 的定义

English:
definition Ω₀
  signature: : Subobject Ω
  body: h.homEquiv (𝟙 Ω)

中文:
定义 Ω₀
  签名: : Subobject Ω
  定义体: h.homEquiv (𝟙 Ω)

Depends on / 依赖: h.homEquiv, homEquiv
-/
def Ω₀ : Subobject Ω := h.homEquiv (𝟙 Ω)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.Ω₀ := Ω₀
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.Ω₀ := Ω₀

/--
lemma `homEquiv_eq` / 引理 `homEquiv_eq`

English:
lemma homEquiv_eq
  given: {X : C} (f : X ⟶ Ω)
  proof: by
  simpa using! h.homEquiv_comp f (𝟙 _)

中文:
引理 homEquiv_eq
  条件: {X : C} (f : X ⟶ Ω)
  证明: by
  simpa using! h.homEquiv_comp f (𝟙 _)

Depends on / 依赖: h.homEquiv_comp, homEquiv_comp
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
/--
lemma `pullback_homEquiv_symm_obj_Ω₀` / 引理 `pullback_homEquiv_symm_obj_Ω₀`

English:
lemma pullback_homEquiv_symm_obj_Ω₀
  given: {X : C} (x : Subobject X)
  proof: by
  rw [← homEquiv_eq]; rw [Equiv.apply_symm_apply]

中文:
引理 pullback_homEquiv_symm_obj_Ω₀
  条件: {X : C} (x : Subobject X)
  证明: by
  rw [← homEquiv_eq]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, homEquiv_eq
-/
lemma pullback_homEquiv_symm_obj_Ω₀ {X : C} (x : Subobject X) :
    (Subobject.pullback (h.homEquiv.symm x)).obj h.Ω₀ = x := by
  rw [← homEquiv_eq]; rw [Equiv.apply_symm_apply]

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.pullback_homEquiv_symm_obj_Ω₀ :=
  pullback_homEquiv_symm_obj_Ω₀
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.pullback_homEquiv_symm_obj_Ω₀ :=
  pullback_homEquiv_symm_obj_Ω₀

section

variable {U X : C} (m : U ⟶ X) [Mono m]

/--
Definition of `χ` / `χ` 的定义

English:
definition χ
  signature: : X ⟶ Ω
  body: h.homEquiv.symm (Subobject.mk m)

中文:
定义 χ
  签名: : X ⟶ Ω
  定义体: h.homEquiv.symm (Subobject.mk m)

Depends on / 依赖: Subobject, Subobject.mk, h.homEquiv.symm, homEquiv
-/
def χ : X ⟶ Ω := h.homEquiv.symm (Subobject.mk m)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.χ := χ
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.χ := χ

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: : MonoOver.mk m ≅
  body: (Subobject.representativeIso (.mk m)).symm ≪≫ Subobject.representative.mapIso
    (eqToIso (h.pullback_homEquiv_symm_obj_Ω₀ (.mk m)).symm)

中文:
定义 iso
  签名: : MonoOver.mk m ≅
  定义体: (Subobject.representativeIso (.mk m)).symm ≪≫ Subobject.representative.mapIso
    (eqToIso (h.pullback_homEquiv_symm_obj_Ω₀ (.mk m)).symm)

Depends on / 依赖: Subobject, Subobject.representative.mapIso, Subobject.representativeIso, eqToIso, h.pullback_homEquiv_symm_obj_, mapIso, representative, representativeIso
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

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : U ⟶ Subobject.underlying.obj h.Ω₀
  body: (h.iso m).hom.hom.left ≫ Subobject.pullbackπ (h.χ m) h.Ω₀

中文:
定义 π
  签名: : U ⟶ Subobject.underlying.obj h.Ω₀
  定义体: (h.iso m).hom.hom.left ≫ Subobject.pullbackπ (h.χ m) h.Ω₀

Depends on / 依赖: Subobject, Subobject.pullback, h.iso, hom.hom.left
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
/--
lemma `iso_inv_left_π` / 引理 `iso_inv_left_π`

English:
lemma iso_inv_left_π
  proof: by
  dsimp only [π]
  rw [← Over.comp_left_assoc]
  convert! Category.id_comp _ using 2
  exact (MonoOver.forget _ ⋙ Over.forget _).congr_map (h.iso m).inv_hom_id

中文:
引理 iso_inv_left_π
  证明: by
  dsimp only [π]
  rw [← Over.comp_left_assoc]
  convert! Category.id_comp _ using 2
  exact (MonoOver.forget _ ⋙ Over.forget _).congr_map (h.iso m).inv_hom_id

Depends on / 依赖: Category, Category.id_comp, MonoOver, MonoOver.forget, Over.comp_left_assoc, Over.forget, comp_left_assoc, congr_map, convert, forget, h.iso, id_comp, inv_hom_id
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
/--
lemma `iso_inv_hom_left_comp` / 引理 `iso_inv_hom_left_comp`

English:
lemma iso_inv_hom_left_comp
  proof: MonoOver.w (h.iso m).inv

中文:
引理 iso_inv_hom_left_comp
  证明: MonoOver.w (h.iso m).inv

Depends on / 依赖: MonoOver, MonoOver.w, h.iso
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
/--
lemma `isPullback` / 引理 `isPullback`

English:
lemma isPullback
  given: {U X : C} (m : U ⟶ X) [Mono m]
  proof: by
  fapply (Subobject.isPullback (h.χ m) h.Ω₀).flip.of_iso
    (((MonoOver.forget _ ⋙ Over.forget _).mapIso (h.iso m)).symm) (Iso.refl _)
    (Iso.refl _) (Iso.refl _)
  all_goals simp [MonoOver.forget]

中文:
引理 isPullback
  条件: {U X : C} (m : U ⟶ X) [Mono m]
  证明: by
  fapply (Subobject.isPullback (h.χ m) h.Ω₀).flip.of_iso
    (((MonoOver.forget _ ⋙ Over.forget _).mapIso (h.iso m)).symm) (Iso.refl _)
    (Iso.refl _) (Iso.refl _)
  all_goals simp [MonoOver.forget]

Depends on / 依赖: Iso.refl, MonoOver, MonoOver.forget, Over.forget, Subobject, Subobject.isPullback, all_goals, fapply, flip.of_iso, forget, h.iso, isPullback, mapIso, of_iso
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
/--
lemma `uniq` / 引理 `uniq`

English:
lemma uniq
  statement: {χ' : X ⟶ Ω} {π : U ⟶ h.Ω₀}
  proof: by
  apply h.homEquiv.injective
  simp only [χ, Equiv.apply_symm_apply, homEquiv_eq]
  simpa using! Subobject.pullback_obj_mk sq.flip

中文:
引理 uniq
  结论: {χ' : X ⟶ Ω} {π : U ⟶ h.Ω₀}
  证明: by
  apply h.homEquiv.injective
  simp only [χ, Equiv.apply_symm_apply, homEquiv_eq]
  simpa using! Subobject.pullback_obj_mk sq.flip

Depends on / 依赖: Equiv.apply_symm_apply, Subobject, Subobject.pullback_obj_mk, apply_symm_apply, h.homEquiv.injective, homEquiv, homEquiv_eq, injective, pullback_obj_mk, sq.flip
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

/--
Definition of `isTerminalΩ₀` / `isTerminalΩ₀` 的定义

English:
definition isTerminalΩ₀
  signature: : IsTerminal (h.Ω₀ : C)
  body: IsTerminal.ofUniqueHom (fun X => h.π (𝟙 X)) (fun X π' => by
    have : IsPullback (𝟙 X) π' (π' ≫ h.Ω₀.arrow) h.Ω₀.arrow :=
      { isLimit' := ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst) (by simp)
          (fun s => by rw [← cancel_mono h.Ω₀.arrow, ← s.condition, Category.assoc])
          (fun s m

中文:
定义 isTerminalΩ₀
  签名: : IsTerminal (h.Ω₀ : C)
  定义体: IsTerminal.ofUniqueHom (fun X => h.π (𝟙 X)) (fun X π' => by
    have : IsPullback (𝟙 X) π' (π' ≫ h.Ω₀.arrow) h.Ω₀.arrow :=
      { isLimit' := ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst) (by simp)
          (fun s => by rw [← cancel_mono h.Ω₀.arrow, ← s.condition, Category.assoc])
          (fun s m

Depends on / 依赖: Category, Category.assoc, Category.id_comp, IsLimit, IsPullback, IsTerminal, IsTerminal.ofUniqueHom, PullbackCone, PullbackCone.IsLimit.mk, cancel_mono, condition, h.isPullback, h.uniq, id_comp, isLimit, isPullback, ofUniqueHom, s.condition, s.fst
-/
noncomputable def isTerminalΩ₀ : IsTerminal (h.Ω₀ : C) :=
  IsTerminal.ofUniqueHom (fun X => h.π (𝟙 X)) (fun X π' => by
    have : IsPullback (𝟙 X) π' (π' ≫ h.Ω₀.arrow) h.Ω₀.arrow :=
      { isLimit' := ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst) (by simp)
          (fun s => by rw [← cancel_mono h.Ω₀.arrow, ← s.condition, Category.assoc])
          (fun s m hm _ => by simpa using hm) ⟩ }
    rw [← cancel_mono h.Ω₀.arrow]; rw [h.uniq this]; rw [← (h.isPullback (𝟙 X)).w]; rw [Category.id_comp])

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.isTerminalΩ₀ := isTerminalΩ₀
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.isTerminalΩ₀ := isTerminalΩ₀

/--
Definition of `χ₀` / `χ₀` 的定义

English:
definition χ₀
  signature: (U : C)
  body: h.isTerminalΩ₀.from U

中文:
定义 χ₀
  签名: (U : C)
  定义体: h.isTerminalΩ₀.from U

Depends on / 依赖: h.isTerminal
-/
noncomputable def χ₀ (U : C) : U ⟶ h.Ω₀ := h.isTerminalΩ₀.from U

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.χ₀ := χ₀
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.χ₀ := χ₀

include h in
/--
lemma `hasTerminal` / 引理 `hasTerminal`

English:
lemma hasTerminal
  statement: HasTerminal C
  proof: h.isTerminalΩ₀.hasTerminal

中文:
引理 hasTerminal
  结论: HasTerminal C
  证明: h.isTerminalΩ₀.hasTerminal

Depends on / 依赖: h.isTerminal, hasTerminal
-/
lemma hasTerminal : HasTerminal C := h.isTerminalΩ₀.hasTerminal

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.hasTerminal := hasTerminal
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.hasTerminal := hasTerminal

variable [HasTerminal C]

/--
Definition of `isoΩ₀` / `isoΩ₀` 的定义

English:
definition isoΩ₀
  signature: : (h.Ω₀ : C) ≅ ⊤_ C
  body: h.isTerminalΩ₀.conePointUniqueUpToIso (limit.isLimit _)

中文:
定义 isoΩ₀
  签名: : (h.Ω₀ : C) ≅ ⊤_ C
  定义体: h.isTerminalΩ₀.conePointUniqueUpToIso (limit.isLimit _)

Depends on / 依赖: conePointUniqueUpToIso, h.isTerminal, isLimit, limit.isLimit
-/
noncomputable def isoΩ₀ : (h.Ω₀ : C) ≅ ⊤_ C :=
  h.isTerminalΩ₀.conePointUniqueUpToIso (limit.isLimit _)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-06")]
alias _root.CategoryTheory.Classifier.SubobjectRepresentableBy.isoΩ₀ := isoΩ₀
@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.SubobjectRepresentableBy.isoΩ₀ := isoΩ₀

/--
Definition of `classifier` / `classifier` 的定义

English:
definition classifier
  signature: : Subobject.Classifier C where
  body: ⊤_ C
  Ω := Ω
  truth := h.isoΩ₀.inv ≫ h.Ω₀.arrow
  mono_truth := terminalIsTerminal.mono_from _
  χ₀ := terminalIsTerminal.from
  χ m _ := h.χ m
  isPullback m _ :=
    (h.isPullback m).of_iso (Iso.refl _) (Iso.refl _) h.isoΩ₀ (Iso.refl _)
      (by simp) (Subsingleton.elim _ _) (by simp) (by simp)

中文:
定义 classifier
  签名: : Subobject.Classifier C where
  定义体: ⊤_ C
  Ω := Ω
  truth := h.isoΩ₀.inv ≫ h.Ω₀.arrow
  mono_truth := terminalIsTerminal.mono_from _
  χ₀ := terminalIsTerminal.from
  χ m _ := h.χ m
  isPullback m _ :=
    (h.isPullback m).of_iso (Iso.refl _) (Iso.refl _) h.isoΩ₀ (Iso.refl _)
      (by simp) (Subsingleton.elim _ _) (by simp) (by simp)
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

/--
theorem `hasSubobjectClassifier_iff_isRepresentable` / 定理 `hasSubobjectClassifier_iff_isRepresentable`

English:
theorem hasSubobjectClassifier_iff_isRepresentable
  given: [HasPullbacks C]
  proof: by
  constructor <;> intro h
  · obtain ⟨⟨𝒞⟩⟩ := h
    apply RepresentableBy.isRepresentable
    exact 𝒞.representableBy
  · obtain ⟨Ω, ⟨h⟩⟩ := h
    constructor; constructor
    exact SubobjectRepresentableBy.classifier h

@[deprecated (since := "2026-03-06")]
alias isRepresentable_hasClassifier_if

中文:
定理 hasSubobjectClassifier_iff_isRepresentable
  条件: [HasPullbacks C]
  证明: by
  constructor <;> intro h
  · obtain ⟨⟨𝒞⟩⟩ := h
    apply RepresentableBy.isRepresentable
    exact 𝒞.representableBy
  · obtain ⟨Ω, ⟨h⟩⟩ := h
    constructor; constructor
    exact SubobjectRepresentableBy.classifier h

@[deprecated (since := "2026-03-06")]
alias isRepresentable_hasClassifier_if

Depends on / 依赖: RepresentableBy, RepresentableBy.isRepresentable, SubobjectRepresentableBy, SubobjectRepresentableBy.classifier, classifier, isRepresentable, representableBy
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

/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: (𝒞₁ 𝒞₂ : Classifier C)
  body: 𝒞₂.χ 𝒞₁.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom := hom

@[reassoc (attr := simp)]

中文:
定义 hom
  签名: (𝒞₁ 𝒞₂ : Classifier C)
  定义体: 𝒞₂.χ 𝒞₁.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom := hom

@[reassoc (attr := simp)]
-/
def hom (𝒞₁ 𝒞₂ : Classifier C) : 𝒞₁.Ω ⟶ 𝒞₂.Ω := 𝒞₂.χ 𝒞₁.truth

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom := hom

@[reassoc (attr := simp)]
/--
lemma `hom_comp_hom` / 引理 `hom_comp_hom`

English:
lemma hom_comp_hom
  given: (𝒞₁ 𝒞₂ 𝒞₃ : Classifier C)
  statement: 𝒞₁.hom 𝒞₂ ≫ 𝒞₂.hom 𝒞₃ = 𝒞₁.hom 𝒞₃
  proof: 𝒞₃.uniq _ (𝒞₂.isPullback _).paste_vert (𝒞₃.isPullback _)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom_comp_hom := hom_comp_hom

@[simp]

中文:
引理 hom_comp_hom
  条件: (𝒞₁ 𝒞₂ 𝒞₃ : Classifier C)
  结论: 𝒞₁.hom 𝒞₂ ≫ 𝒞₂.hom 𝒞₃ = 𝒞₁.hom 𝒞₃
  证明: 𝒞₃.uniq _ (𝒞₂.isPullback _).paste_vert (𝒞₃.isPullback _)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom_comp_hom := hom_comp_hom

@[simp]

Depends on / 依赖: isPullback, paste_vert
-/
lemma hom_comp_hom (𝒞₁ 𝒞₂ 𝒞₃ : Classifier C) : 𝒞₁.hom 𝒞₂ ≫ 𝒞₂.hom 𝒞₃ = 𝒞₁.hom 𝒞₃ :=
𝒞₃.uniq _ (𝒞₂.isPullback _).paste_vert (𝒞₃.isPullback _)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom_comp_hom := hom_comp_hom

@[simp]
/--
lemma `hom_refl` / 引理 `hom_refl`

English:
lemma hom_refl
  given: (𝒞₁ : Classifier C)
  statement: 𝒞₁.hom 𝒞₁ = 𝟙 _
  proof: (𝒞₁.uniq (χ₀' := 𝟙 _) 𝒞₁.truth IsPullback.of_id_snd).symm

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom_refl := hom_refl

@[reassoc (attr := simp)]

中文:
引理 hom_refl
  条件: (𝒞₁ : Classifier C)
  结论: 𝒞₁.hom 𝒞₁ = 𝟙 _
  证明: (𝒞₁.uniq (χ₀' := 𝟙 _) 𝒞₁.truth IsPullback.of_id_snd).symm

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom_refl := hom_refl

@[reassoc (attr := simp)]

Depends on / 依赖: IsPullback, IsPullback.of_id_snd, of_id_snd
-/
lemma hom_refl (𝒞₁ : Classifier C) : 𝒞₁.hom 𝒞₁ = 𝟙 _ :=
  (𝒞₁.uniq (χ₀' := 𝟙 _) 𝒞₁.truth IsPullback.of_id_snd).symm

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.hom_refl := hom_refl

@[reassoc (attr := simp)]
/--
lemma `χ_comp_hom` / 引理 `χ_comp_hom`

English:
lemma χ_comp_hom
  given: {𝒞₁ 𝒞₂ : Classifier C} {X Y : C} (m : X ⟶ Y) [Mono m]
  proof: 𝒞₂.uniq m ((𝒞₁.isPullback m).paste_vert (𝒞₂.isPullback 𝒞₁.truth))

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.χ_comp_hom := χ_comp_hom

@[reassoc (attr := simp)]

中文:
引理 χ_comp_hom
  条件: {𝒞₁ 𝒞₂ : Classifier C} {X Y : C} (m : X ⟶ Y) [Mono m]
  证明: 𝒞₂.uniq m ((𝒞₁.isPullback m).paste_vert (𝒞₂.isPullback 𝒞₁.truth))

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.χ_comp_hom := χ_comp_hom

@[reassoc (attr := simp)]

Depends on / 依赖: isPullback, paste_vert
-/
lemma χ_comp_hom {𝒞₁ 𝒞₂ : Classifier C} {X Y : C} (m : X ⟶ Y) [Mono m] :
    𝒞₁.χ m ≫ 𝒞₁.hom 𝒞₂ = 𝒞₂.χ m :=
  𝒞₂.uniq m ((𝒞₁.isPullback m).paste_vert (𝒞₂.isPullback 𝒞₁.truth))

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.χ_comp_hom := χ_comp_hom

@[reassoc (attr := simp)]
/--
lemma `truth_comp_hom` / 引理 `truth_comp_hom`

English:
lemma truth_comp_hom
  given: {𝒞₁ 𝒞₂ : Classifier C}
  proof: (𝒞₂.isPullback _).w

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.truth_comp_hom := truth_comp_hom

中文:
引理 truth_comp_hom
  条件: {𝒞₁ 𝒞₂ : Classifier C}
  证明: (𝒞₂.isPullback _).w

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.truth_comp_hom := truth_comp_hom

Depends on / 依赖: isPullback
-/
lemma truth_comp_hom {𝒞₁ 𝒞₂ : Classifier C} :
  𝒞₁.truth ≫ 𝒞₁.hom 𝒞₂ = 𝒞₂.χ₀ _ ≫ 𝒞₂.truth := (𝒞₂.isPullback _).w

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.truth_comp_hom := truth_comp_hom

/-- a concrete equivalence of any two subobject classifiers -/
@[simps]
/--
Definition of `uniqueUpToIso` / `uniqueUpToIso` 的定义

English:
definition uniqueUpToIso
  signature: (𝒞₁ 𝒞₂ : Classifier C)
  body: 𝒞₁.hom 𝒞₂
  inv := 𝒞₂.hom 𝒞₁

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.uniqueUpToIso := uniqueUpToIso

中文:
定义 uniqueUpToIso
  签名: (𝒞₁ 𝒞₂ : Classifier C)
  定义体: 𝒞₁.hom 𝒞₂
  inv := 𝒞₂.hom 𝒞₁

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.uniqueUpToIso := uniqueUpToIso
-/
def uniqueUpToIso (𝒞₁ 𝒞₂ : Classifier C) : 𝒞₁.Ω ≅ 𝒞₂.Ω where
  hom := 𝒞₁.hom 𝒞₂
  inv := 𝒞₂.hom 𝒞₁

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.uniqueUpToIso := uniqueUpToIso

instance (𝒞₁ 𝒞₂ : Classifier C) : IsIso (𝒞₁.hom 𝒞₂) := (𝒞₁.uniqueUpToIso 𝒞₂).isIso_hom

/-- Being a subobject classifier is preserved under isomorphism. -/
@[simps]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (𝒞 : Classifier C) {Ω₀ Ω : C} (eΩ : 𝒞.Ω ≅ Ω) (eΩ₀ : 𝒞.Ω₀ ≅ Ω₀)
  body: Ω₀
  Ω := Ω
  truth := t
  mono_truth := ht ▸ inferInstance
  χ₀ := from'
  χ {F G} m _ := 𝒞.χ m ≫ eΩ.hom
  isPullback {F G} m _ := by
    rw [eΩ₀.comp_inv_eq.mp (Subsingleton.elim (from' F ≫ eΩ₀.inv) (𝒞.χ₀ F))]
    exact (𝒞.isPullback m).paste_vert (IsPullback.of_vert_isIso_mono (by simp [ht]))
  u

中文:
定义 ofIso
  签名: (𝒞 : Classifier C) {Ω₀ Ω : C} (eΩ : 𝒞.Ω ≅ Ω) (eΩ₀ : 𝒞.Ω₀ ≅ Ω₀)
  定义体: Ω₀
  Ω := Ω
  truth := t
  mono_truth := ht ▸ inferInstance
  χ₀ := from'
  χ {F G} m _ := 𝒞.χ m ≫ eΩ.hom
  isPullback {F G} m _ := by
    rw [eΩ₀.comp_inv_eq.mp (Subsingleton.elim (from' F ≫ eΩ₀.inv) (𝒞.χ₀ F))]
    exact (𝒞.isPullback m).paste_vert (IsPullback.of_vert_isIso_mono (by simp [ht]))
  u

Depends on / 依赖: Classifier, IsPullback, IsPullback.of_vert_isIso_mono, Subsingleton, Subsingleton.elim, cat_disch, comp_inv_eq, comp_inv_eq.mp, isPullback, mono_truth, of_vert_isIso_mono, paste_vert
-/
def ofIso (𝒞 : Classifier C) {Ω₀ Ω : C} (eΩ : 𝒞.Ω ≅ Ω) (eΩ₀ : 𝒞.Ω₀ ≅ Ω₀)
    (from' : forall C, C ⟶ Ω₀) (t : Ω₀ ⟶ Ω) (ht : t = eΩ₀.inv ≫ 𝒞.truth ≫ eΩ.hom := by cat_disch) :
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
/--
Definition of `ofEquivalence` / `ofEquivalence` 的定义

English:
definition ofEquivalence
  signature: (𝒞₁ : Classifier C) (e : C ≌ D)
  body: e.functor.obj 𝒞₁.Ω₀
  Ω := e.functor.obj 𝒞₁.Ω
  truth := e.functor.map 𝒞₁.truth
  χ₀ Y := e.counitInv.app Y ≫ e.functor.map (𝒞₁.χ₀ (e.inverse.obj Y))
  χ m := e.counitInv.app _ ≫ e.functor.map (𝒞₁.χ (e.inverse.map m))
  isPullback {F G} m _ := by
    apply ((𝒞₁.isPullback (e.inverse.map m)).map e.fu

中文:
定义 ofEquivalence
  签名: (𝒞₁ : Classifier C) (e : C ≌ D)
  定义体: e.functor.obj 𝒞₁.Ω₀
  Ω := e.functor.obj 𝒞₁.Ω
  truth := e.functor.map 𝒞₁.truth
  χ₀ Y := e.counitInv.app Y ≫ e.functor.map (𝒞₁.χ₀ (e.inverse.obj Y))
  χ m := e.counitInv.app _ ≫ e.functor.map (𝒞₁.χ (e.inverse.map m))
  isPullback {F G} m _ := by
    apply ((𝒞₁.isPullback (e.inverse.map m)).map e.fu

Depends on / 依赖: e.functor.obj, functor
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
exact (hχ'.map e.inverse).paste_vert IsPullback.of_vert_isIso_mono .mk
    simpa using congr(e.counitInv.app G ≫ e.functor.map $this)

@[deprecated (since := "2026-03-06")]
alias _root_.CategoryTheory.Classifier.ofEquivalence := ofEquivalence

end Equivalence

end CategoryTheory.Subobject.Classifier
