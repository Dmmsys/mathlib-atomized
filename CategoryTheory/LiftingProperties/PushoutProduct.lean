/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Lifting properties and pushout-products / pullback-homs

Various equivalent lifting properties involving pushout-products and pullback-homs. For
`f : A ⟶ B`, `g : K ⟶ L`, `h : X ⟶ Y` in a monoidal closed category with pushouts and pullbacks,
`f □ g` lifts against `h` if and only if `g` lifts against `f ⋔ h`.

Special cases are considered when any of `A = ∅`, `K = ∅`, or `Y = ⋆` are true.

## References

* [Charles Rezk, *Introduction to Quasi-categories*, Proposition 21.5][Rezk2022]
-/

public section

universe v u

namespace CategoryTheory

open Limits MonoidalCategory CategoryTheory.Functor PushoutObjObj

variable {C : Type u} [Category.{v} C]

namespace MonoidalCategory.Arrow

namespace PushoutProduct

/-- `X □ Y` lifts against `Z` if and only if `Y` lifts against `X ⋔ Z`. -/
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_iff** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
形式化陈述：hasLiftingProperty_iff [HasPushouts C] [HasPullbacks C] [MonoidalCategory 
C] [MonoidalClosed C] {X Y Z : Arrow C} : HasLiftingProperty (X □ Y).hom Z.hom ↔
 HasLiftingProperty Y.hom ((.op X) ⋔ Z).hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ParametrizedAdjunction.hasLiftingProperty_iff`：hasLifting
Property_iff : HasLiftingProperty sq₁₂.ι f₃ ↔ HasLiftingProperty f₂ sq₁₃.π

--- 原说明 ---
`X □ Y` lifts against `Z` if and only if `Y` lifts against `X ⋔ Z`.
-/
lemma hasLiftingProperty_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C] {X Y Z : Arrow C} :
    HasLiftingProperty (X □ Y).hom Z.hom ↔ HasLiftingProperty Y.hom ((.op X) ⋔ Z).hom :=
  ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)

/-- `X □ Y` lifts against `Z` if and only if `X` lifts against `Y ⋔ Z`. -/
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_iff'**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct`。
形式化陈述：hasLiftingProperty_iff' [HasPushouts C] [HasPullbacks C] [MonoidalCategory
 C] [MonoidalClosed C] [BraidedCategory C] {X Y Z : Arrow C} : HasLiftingPropert
y (X □ Y).hom Z.hom ↔ HasLiftingProperty X.hom ((.op Y) ⋔ Z).hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_
iff`：hasLiftingProperty_iff [HasPushouts C] [HasPullbacks C] [MonoidalCategory C
] [MonoidalClosed C] {X Y Z : Arrow C} : HasLiftingProperty (X □ …
· 使用定理 `CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_left`：iff_of_arrow_is
o_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'} (e : Arrow.mk i ≅ Arrow.mk
 i') (p : X ⟶ Y) : HasLiftingProperty i p ↔ H…

--- 原说明 ---
`X □ Y` lifts against `Z` if and only if `X` lifts against `Y ⋔ Z`.
-/
lemma hasLiftingProperty_iff' [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] {X Y Z : Arrow C} :
    HasLiftingProperty (X □ Y).hom Z.hom ↔ HasLiftingProperty X.hom ((.op Y) ⋔ Z).hom := by
  rw [← hasLiftingProperty_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) _

/-- `f □ g` lifts against `h` if and only if `g` lifts against `f ⋔ h`. -/
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct
`。
形式化陈述：hasLiftingProperty_mk_iff [HasPushouts C] [HasPullbacks C] [MonoidalCatego
ry C] [MonoidalClosed C] {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L} {h : X ⟶ Y} :
 HasLiftingProperty (f □ g).hom h ↔ HasLiftingProperty g ((.op f) ⋔ h).hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ParametrizedAdjunction.hasLiftingProperty_iff`：hasLifting
Property_iff : HasLiftingProperty sq₁₂.ι f₃ ↔ HasLiftingProperty f₂ sq₁₃.π

--- 原说明 ---
`f □ g` lifts against `h` if and only if `g` lifts against `f ⋔ h`.
-/
lemma hasLiftingProperty_mk_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L} {h : X ⟶ Y} :
    HasLiftingProperty (f □ g).hom h ↔ HasLiftingProperty g ((.op f) ⋔ h).hom :=
  ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)

/-- `f □ g` lifts against `h` if and only if `f` lifts against `g ⋔ h`. -/
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff
'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduc
t`。
形式化陈述：hasLiftingProperty_mk_iff' [HasPushouts C] [HasPullbacks C] [MonoidalCateg
ory C] [MonoidalClosed C] [BraidedCategory C] {A B K L X Y : C} {f : A ⟶ B} {g :
 K ⟶ L} {h : X ⟶ Y} : HasLiftingProperty (f □ g).hom h ↔ HasLiftingProperty f ((
.op g) ⋔ h).hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_
mk_iff`：hasLiftingProperty_mk_iff [HasPushouts C] [HasPullbacks C] [MonoidalCate
gory C] [MonoidalClosed C] {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L}…
· 使用定理 `CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_left`：iff_of_arrow_is
o_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'} (e : Arrow.mk i ≅ Arrow.mk
 i') (p : X ⟶ Y) : HasLiftingProperty i p ↔ H…

--- 原说明 ---
`f □ g` lifts against `h` if and only if `f` lifts against `g ⋔ h`.
-/
lemma hasLiftingProperty_mk_iff' [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L} {h : X ⟶ Y} :
    HasLiftingProperty (f □ g).hom h ↔ HasLiftingProperty f ((.op g) ⋔ h).hom := by
  rw [← hasLiftingProperty_mk_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) h

set_option backward.defeqAttrib.useBackward true in
/-- `(∅ ⟶ B) □ g` lifts against `X ⟶ Y` if and only if `g` lifts against `B ⟹ X ⟶ B ⟹ Y`. -/
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_isI
nitial_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.Push
outProduct`。
形式化陈述：hasLiftingProperty_mk_isInitial_iff [HasPushouts C] [CartesianMonoidalCate
gory C] [MonoidalClosed C] [BraidedCategory C] {A B K L X Y : C} {g : K ⟶ L} {h 
: X ⟶ Y} (i : IsInitial A) : HasLiftingProperty (i.to B □ g).hom h ↔ HasLiftingP
roperty g ((ihom B).map h)
参数：i : IsInitial A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_left`：iff_of_arrow_is
o_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'} (e : Arrow.mk i ≅ Arrow.mk
 i') (p : X ⟶ Y) : HasLiftingProperty i p ↔ H…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.hasLiftingProperty_iff`：hasLiftingProperty_iff
 (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y) : HasLiftingProperty 
(G.map i) p ↔ HasLiftingProperty i (F.…

--- 原说明 ---
`(∅ ⟶ B) □ g` lifts against `X ⟶ Y` if and only if `g` lifts against `B ⟹ X ⟶ B 
⟹ Y`.
-/
lemma hasLiftingProperty_mk_isInitial_iff [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {g : K ⟶ L} {h : X ⟶ Y}
    (i : IsInitial A) :
    HasLiftingProperty (i.to B □ g).hom h ↔
      HasLiftingProperty g ((ihom B).map h) := by
  dsimp
  have := HasLiftingProperty.iff_of_arrow_iso_left (isInitialIso' g i (W := B)) h
  rw [dsimp% this]
  exact Adjunction.hasLiftingProperty_iff (ihom.adjunction B) g h

/-- `f □ (∅ ⟶ L)` lifts against `X ⟶ Y` if and only if `f` lifts against `L ⟹ X ⟶ L ⟹ Y`. -/
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_isI
nitial_iff'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.Pus
houtProduct`。
形式化陈述：hasLiftingProperty_mk_isInitial_iff' [HasPushouts C] [CartesianMonoidalCat
egory C] [MonoidalClosed C] [BraidedCategory C] {A B K L X Y : C} {f : A ⟶ B} {h
 : X ⟶ Y} (i : IsInitial K) : HasLiftingProperty (f □ i.to L).hom h ↔ HasLifting
Property f ((ihom L).map h)
参数：i : IsInitial K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_
mk_isInitial_iff`：hasLiftingProperty_mk_isInitial_iff [HasPushouts C] [Cartesian
MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] {A B K L X Y : C} {…
· 使用定理 `CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_left`：iff_of_arrow_is
o_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'} (e : Arrow.mk i ≅ Arrow.mk
 i') (p : X ⟶ Y) : HasLiftingProperty i p ↔ H…

--- 原说明 ---
`f □ (∅ ⟶ L)` lifts against `X ⟶ Y` if and only if `f` lifts against `L ⟹ X ⟶ L 
⟹ Y`.
-/
lemma hasLiftingProperty_mk_isInitial_iff' [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {f : A ⟶ B} {h : X ⟶ Y}
    (i : IsInitial K) :
    HasLiftingProperty (f □ i.to L).hom h ↔
      HasLiftingProperty f ((ihom L).map h) := by
  rw [← hasLiftingProperty_mk_isInitial_iff i]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) h

/-- `f □ g` lifts against `X ⟶ ⋆` if and only if `g` lifts against `B ⟹ X ⟶ A ⟹ X`. -/
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_isT
erminal_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.Arrow.Pus
houtProduct`。
形式化陈述：hasLiftingProperty_mk_isTerminal_iff [HasPushouts C] [HasPullbacks C] [Mon
oidalCategory C] [MonoidalClosed C] {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L} (t
 : IsTerminal Y) : HasLiftingProperty (f □ g).hom (t.from X) ↔ HasLiftingPropert
y g ((MonoidalClosed.pre f).app X)
参数：t : IsTerminal Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_
mk_iff`：hasLiftingProperty_mk_iff [HasPushouts C] [HasPullbacks C] [MonoidalCate
gory C] [MonoidalClosed C] {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L}…
· 使用定理 `CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_right`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {Y X Y' X' B A : C} (i : A ⟶ B)
 {p : X ⟶ Y}   {p' : X' ⟶ Y'} (e : CategoryThe…

--- 原说明 ---
`f □ g` lifts against `X ⟶ ⋆` if and only if `g` lifts against `B ⟹ X ⟶ A ⟹ X`.
-/
lemma hasLiftingProperty_mk_isTerminal_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L}
    (t : IsTerminal Y) :
    HasLiftingProperty (f □ g).hom (t.from X) ↔
      HasLiftingProperty g ((MonoidalClosed.pre f).app X) := by
  rw [hasLiftingProperty_mk_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right g (PullbackHom.isTerminalIso _ t)

/-- `(∅ ⟶ B) □ g` lifts against `X ⟶ ⋆` if and only if `g` lifts against `(B ⟹ X) ⟶ ⋆`. -/
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_isI
nitial_isTerminal_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory
.Arrow.PushoutProduct`。
形式化陈述：hasLiftingProperty_mk_isInitial_isTerminal_iff [HasPushouts C] [CartesianM
onoidalCategory C] [MonoidalClosed C] [BraidedCategory C] {A B K L X Y : C} {g :
 K ⟶ L} (i : IsInitial A) (t : IsTerminal Y) : HasLiftingProperty (i.to B □ g).h
om (t.from X) ↔ HasLiftingProperty g (t.from ((ihom B).obj X))
参数：i : IsInitial A；t : IsTerminal Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_
mk_isInitial_iff`：hasLiftingProperty_mk_isInitial_iff [HasPushouts C] [Cartesian
MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] {A B K L X Y : C} {…
· 使用定理 `CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_right`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {Y X Y' X' B A : C} (i : A ⟶ B)
 {p : X ⟶ Y}   {p' : X' ⟶ Y'} (e : CategoryThe…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.ihom.instIsRightAdjoint`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] (A : C)   
[inst_2 : CategoryTheory.Clo…
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g

--- 原说明 ---
`(∅ ⟶ B) □ g` lifts against `X ⟶ ⋆` if and only if `g` lifts against `(B ⟹ X) ⟶ 
⋆`.
-/
lemma hasLiftingProperty_mk_isInitial_isTerminal_iff [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {g : K ⟶ L}
    (i : IsInitial A) (t : IsTerminal Y) :
    HasLiftingProperty (i.to B □ g).hom (t.from X) ↔
      HasLiftingProperty g (t.from ((ihom B).obj X)) := by
  rw [hasLiftingProperty_mk_isInitial_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right g
    (Arrow.isoMk' _ _ (Iso.refl _) ((IsTerminal.isTerminalObj (ihom B) _ t).uniqueUpToIso t)
      (t.hom_ext _ _))

/-- `f □ (∅ ⟶ L)` lifts against `X ⟶ ⋆` if and only if `f` lifts against `(L ⟹ X) ⟶ ⋆`. -/
/-
**CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_isI
nitial_isTerminal_iff'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategor
y.Arrow.PushoutProduct`。
形式化陈述：hasLiftingProperty_mk_isInitial_isTerminal_iff' [HasPushouts C] [Cartesian
MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] {A B K L X Y : C} {f 
: A ⟶ B} (i : IsInitial K) (t : IsTerminal Y) : HasLiftingProperty (f □ i.to L).
hom (t.from X) ↔ HasLiftingProperty f (t.from ((ihom L).obj X))
参数：i : IsInitial K；t : IsTerminal Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_
mk_isInitial_iff'`：hasLiftingProperty_mk_isInitial_iff' [HasPushouts C] [Cartesi
anMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] {A B K L X Y : C} …
· 使用定理 `CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_right`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {Y X Y' X' B A : C} (i : A ⟶ B)
 {p : X ⟶ Y}   {p' : X' ⟶ Y'} (e : CategoryThe…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.ihom.instIsRightAdjoint`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] (A : C)   
[inst_2 : CategoryTheory.Clo…
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g

--- 原说明 ---
`f □ (∅ ⟶ L)` lifts against `X ⟶ ⋆` if and only if `f` lifts against `(L ⟹ X) ⟶ 
⋆`.
-/
lemma hasLiftingProperty_mk_isInitial_isTerminal_iff' [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {f : A ⟶ B}
    (i : IsInitial K) (t : IsTerminal Y) :
    HasLiftingProperty (f □ i.to L).hom (t.from X) ↔
      HasLiftingProperty f (t.from ((ihom L).obj X)) := by
  rw [hasLiftingProperty_mk_isInitial_iff']
  exact HasLiftingProperty.iff_of_arrow_iso_right f
    (Arrow.isoMk' _ _ (Iso.refl _) ((IsTerminal.isTerminalObj (ihom L) _ t).uniqueUpToIso t)
      (t.hom_ext _ _))

end PushoutProduct

end MonoidalCategory.Arrow

end CategoryTheory

