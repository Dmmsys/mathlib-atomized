/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Sieves

/-!
# The sheaf condition for a presieve

We define what it means for a presheaf `P : Cᵒᵖ ⥤ Type v` to be a sheaf *for* a particular
presieve `R` on `X`:
* A *family of elements* `x` for `P` at `R` is an element `x_f` of `P Y` for every `f : Y ⟶ X` in
  `R`. See `FamilyOfElements`.
* The family `x` is *compatible* if, for any `f₁ : Y₁ ⟶ X` and `f₂ : Y₂ ⟶ X` both in `R`,
  and any `g₁ : Z ⟶ Y₁` and `g₂ : Z ⟶ Y₂` such that `g₁ ≫ f₁ = g₂ ≫ f₂`, the restriction of
  `x_f₁` along `g₁` agrees with the restriction of `x_f₂` along `g₂`.
  See `FamilyOfElements.Compatible`.
* An *amalgamation* `t` for the family is an element of `P X` such that for every `f : Y ⟶ X` in
  `R`, the restriction of `t` on `f` is `x_f`.
  See `FamilyOfElements.IsAmalgamation`.

We then say `P` is *separated* for `R` if every compatible family has at most one amalgamation,
and it is a *sheaf* for `R` if every compatible family has a unique amalgamation.
See `IsSeparatedFor` and `IsSheafFor`.

In the special case where `R` is a sieve, the compatibility condition can be simplified:
* The family `x` is *compatible* if, for any `f : Y ⟶ X` in `R` and `g : Z ⟶ Y`, the restriction of
  `x_f` along `g` agrees with `x_(g ≫ f)` (which is well defined since `g ≫ f` is in `R`).
  See `FamilyOfElements.SieveCompatible` and `compatible_iff_sieveCompatible`.

In the special case where `C` has pullbacks, the compatibility condition can be simplified:
* The family `x` is *compatible* if, for any `f : Y ⟶ X` and `g : Z ⟶ X` both in `R`,
  the restriction of `x_f` along `π₁ : pullback f g ⟶ Y` agrees with the restriction of `x_g`
  along `π₂ : pullback f g ⟶ Z`.
  See `FamilyOfElements.PullbackCompatible` and `pullbackCompatible_iff`.

We also provide equivalent conditions to satisfy alternate definitions given in the literature.

* Stacks: The condition of https://stacks.math.columbia.edu/tag/00Z8 is virtually identical to the
  statement of `isSheafFor_iff_yonedaSheafCondition` (since the bijection described there carries
  the same information as the unique existence.)

* Maclane-Moerdijk [MM92]: Using `compatible_iff_sieveCompatible`, the definitions of `IsSheaf`
  are equivalent. There are also alternate definitions given:
  - Yoneda condition: Defined in `yonedaSheafCondition` and equivalence in
    `isSheafFor_iff_yonedaSheafCondition`.
  - Matching family for presieves with pullback: `pullbackCompatible_iff`.

## Implementation

The sheaf condition is given as a proposition, rather than a subsingleton in `Type (max u₁ v)`.
This doesn't seem to make a big difference, other than making a couple of definitions noncomputable,
but it means that equivalent conditions can be given as `↔` statements rather than `≃` statements,
which can be convenient.

## References

* [MM92]: *Sheaves in geometry and logic*, Saunders MacLane, and Ieke Moerdijk:
  Chapter III, Section 4.
* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1.
* https://stacks.math.columbia.edu/tag/00VL (sheaves on a pretopology or site)
* https://stacks.math.columbia.edu/tag/00ZB (sheaves on a topology)

-/

@[expose] public section


universe w w' v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presieve

variable {C : Type u₁} [Category.{v₁} C]
variable {P Q U : Cᵒᵖ ⥤ Type w}
variable {X Y : C} {S : Sieve X} {R : Presieve X}

/-- A family of elements for a presheaf `P` given a collection of arrows `R` with fixed codomain `X`
consists of an element of `P Y` for every `f : Y ⟶ X` in `R`.
A presheaf is a sheaf (resp, separated) if every *compatible* family of elements has exactly one
(resp, at most one) amalgamation.

This data is referred to as a `family` in [MM92], Chapter III, Section 4. It is also a concrete
version of the elements of the middle object in the Stacks entry which is
more useful for direct calculations. It is also used implicitly in Definition C2.1.2 in [Elephant].
-/
@[stacks 00VM "This is a concrete version of the elements of the middle object there."]
/-
**CategoryTheory.Presieve.FamilyOfElements** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Presieve`。
形式化陈述：FamilyOfElements (P : Cᵒᵖ ⥤ Type w) (R : Presieve X)
参数：P : Cᵒᵖ ⥤ Type w；R : Presieve X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of elements for a presheaf `P` given a collection of arrows `R` with fi
xed codomain `X`
consists of an element of `P Y` for every `f : Y ⟶ X` in `R`.
A presheaf is a sheaf (resp, separated) if every *compatible* family of elements
 has exactly one
(resp, at most one) amalgamation.

This data is referred to as a `family` in [MM92], Chapter III, Section 4. It is 
also a concrete
version of the elements of the middle object in the Stacks entry which is
more useful for direct calculations. It is also used implicitly in Definition C2
.1.2 in [Elephant].
-/
def FamilyOfElements (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) :=
  ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → P.obj (op Y)
/-
**CategoryTheory.Presieve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (FamilyOfElements P (⊥ : Presieve X)) :=
  ⟨fun _ _ => False.elim⟩

@[ext]
/-
**CategoryTheory.Presieve.FamilyOfElements.ext** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Presieve.FamilyOfElements`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} {x y : Cat
egoryTheory.Presieve.FamilyOfElements P R},   (∀ {Y : C} (f : Y ⟶ X) (hf : R f),
 x f hf = y f hf) → x = y
参数：Type w；∀ {Y : C} (f : Y ⟶ X) (hf : R f), x f hf = y f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma FamilyOfElements.ext {R : Presieve X} {x y : R.FamilyOfElements P}
    (H : ∀ {Y : C} (f : Y ⟶ X) (hf : R f), x f hf = y f hf) :
    x = y := by
  funext Z f hf
  exact H f hf

/-- A family of elements for a presheaf on the presieve `R₂` can be restricted to a smaller presieve
`R₁`.
-/
/-
**CategoryTheory.Presieve.FamilyOfElements.restrict** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P : C
ategoryTheory.Functor Cᵒᵖ (Type w)} →       {X : C} →         {R₁ R₂ : CategoryT
heory.Presieve X} →           R₁ ≤ R₂ → CategoryTheory.Presieve.FamilyOfElements
 P R₂ → CategoryTheory.Presieve.FamilyOfElements P R₁
参数：Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of elements for a presheaf on the presieve `R₂` can be restricted to a 
smaller presieve
`R₁`.
-/
def FamilyOfElements.restrict {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂) :
    FamilyOfElements P R₂ → FamilyOfElements P R₁ := fun x _ f hf => x f (h _ _ hf)

/-- The image of a family of elements by a morphism of presheaves. -/
/-
**CategoryTheory.Presieve.FamilyOfElements.map** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Presieve.FamilyOfElements`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P Q :
 CategoryTheory.Functor Cᵒᵖ (Type w)} →       {X : C} →         {R : CategoryThe
ory.Presieve X} →           CategoryTheory.Presieve.FamilyOfElements P R → (P ⟶ 
Q) → CategoryTheory.Presieve.FamilyOfElements Q R
参数：Type w；P ⟶ Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a family of elements by a morphism of presheaves.
-/
def FamilyOfElements.map (p : FamilyOfElements P R) (φ : P ⟶ Q) :
    FamilyOfElements Q R :=
  fun _ f hf => φ.app _ (p f hf)

@[simp]
/-
**CategoryTheory.Presieve.FamilyOfElements.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : Categor
yTheory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} (p : Cat
egoryTheory.Presieve.FamilyOfElements P R) (φ : P ⟶ Q) {Y : C} (f : Y ⟶ X)   (hf
 : R f), p.map φ f hf = (CategoryTheory.ConcreteCategory.hom (φ.app (Opposite.op
 Y))) (p f hf)
参数：Type w；p : CategoryTheory.Presieve.FamilyOfElements P R；φ : P ⟶ Q；f : Y ⟶ X；h
f : R f；CategoryTheory.ConcreteCategory.hom (φ.app (Opposite.op Y))；p f hf。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FamilyOfElements.map_apply
    (p : FamilyOfElements P R) (φ : P ⟶ Q) {Y : C} (f : Y ⟶ X) (hf : R f) :
    p.map φ f hf = φ.app _ (p f hf) := rfl
/-
**CategoryTheory.Presieve.FamilyOfElements.restrict_map** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : Categor
yTheory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} (p : Cat
egoryTheory.Presieve.FamilyOfElements P R) (φ : P ⟶ Q)   {R' : CategoryTheory.Pr
esieve X} (h : R' ≤ R),   (CategoryTheory.Presieve.FamilyOfElements.restrict h p
).map φ =     CategoryTheory.Presieve.FamilyOfElements.restrict h (p.map φ)
参数：Type w；p : CategoryTheory.Presieve.FamilyOfElements P R；φ : P ⟶ Q；h : R' ≤ R；
CategoryTheory.Presieve.FamilyOfElements.restrict h p；p.map φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FamilyOfElements.restrict_map
    (p : FamilyOfElements P R) (φ : P ⟶ Q) {R' : Presieve X} (h : R' ≤ R) :
    (p.restrict h).map φ = (p.map φ).restrict h := rfl

variable (P) in
/-- A family of elements on `{ f : X ⟶ Y }` is an element of `F(X)`. -/
@[simps apply, simps -isSimp symm_apply]
/-
**CategoryTheory.Presieve.FamilyOfElements.singletonEquiv** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (P : C
ategoryTheory.Functor Cᵒᵖ (Type w)) →       {X Y : C} →         (f : X ⟶ Y) →   
        CategoryTheory.Presieve.FamilyOfElements P (CategoryTheory.Presieve.sing
leton f) ≃ P.obj (Opposite.op X)
参数：P : CategoryTheory.Functor Cᵒᵖ (Type w)；f : X ⟶ Y；CategoryTheory.Presieve.sin
gleton f；Opposite.op X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of elements on `{ f : X ⟶ Y }` is an element of `F(X)`.
-/
def FamilyOfElements.singletonEquiv {X Y : C} (f : X ⟶ Y) :
    (singleton f).FamilyOfElements P ≃ P.obj (op X) where
  toFun x := x f (by simp)
  invFun x Z g hg := P.map (eqToHom <| by cases hg; rfl).op x
  left_inv x := by ext _ _ ⟨rfl⟩; simp
  right_inv x := by simp

@[simp]
/-
**CategoryTheory.Presieve.FamilyOfElements.singletonEquiv_symm_apply_self** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X Y : C}   (f : X ⟶ Y) (x : P.obj (Opposite.op X)),
 (CategoryTheory.Presieve.FamilyOfElements.singletonEquiv P f).symm x f ⋯ = x
参数：Type w；f : X ⟶ Y；x : P.obj (Opposite.op X)；CategoryTheory.Presieve.FamilyOfEl
ements.singletonEquiv P f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.singletonEquiv_symm_apply`：∀ {C
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (P : CategoryTheory.Func
tor Cᵒᵖ (Type w)) {X Y : C}   (f : X ⟶ Y) (x : P.obj (Op…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma FamilyOfElements.singletonEquiv_symm_apply_self {X Y : C} (f : X ⟶ Y) (x : P.obj (op X)) :
    (singletonEquiv P f).symm x f ⟨⟩ = x := by
  simp [singletonEquiv_symm_apply]

/-- A family of elements for the arrow set `R` is *compatible* if for any `f₁ : Y₁ ⟶ X` and
`f₂ : Y₂ ⟶ X` in `R`, and any `g₁ : Z ⟶ Y₁` and `g₂ : Z ⟶ Y₂`, if the square `g₁ ≫ f₁ = g₂ ≫ f₂`
commutes then the elements of `P Z` obtained by restricting the element of `P Y₁` along `g₁` and
restricting the element of `P Y₂` along `g₂` are the same.

In special cases, this condition can be simplified, see `pullbackCompatible_iff` and
`compatible_iff_sieveCompatible`.

This is referred to as a "compatible family" in Definition C2.1.2 of [Elephant], and on nlab:
https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents

For a more explicit version in the case where `R` is of the form `Presieve.ofArrows`, see
`CategoryTheory.Presieve.Arrows.Compatible`.
-/
/-
**CategoryTheory.Presieve.FamilyOfElements.Compatible** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P : C
ategoryTheory.Functor Cᵒᵖ (Type w)} →       {X : C} → {R : CategoryTheory.Presie
ve X} → CategoryTheory.Presieve.FamilyOfElements P R → Prop
参数：Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of elements for the arrow set `R` is *compatible* if for any `f₁ : Y₁ ⟶
 X` and
`f₂ : Y₂ ⟶ X` in `R`, and any `g₁ : Z ⟶ Y₁` and `g₂ : Z ⟶ Y₂`, if the square `g₁
 ≫ f₁ = g₂ ≫ f₂`
commutes then the elements of `P Z` obtained by restricting the element of `P Y₁
` along `g₁` and
restricting the element of `P Y₂` along `g₂` are the same.

In special cases, this condition can be simplified, see `pullbackCompatible_iff`
 and
`compatible_iff_sieveCompatible`.

This is referred to as a "compatible family" in Definition C2.1.2 of [Elephant],
 and on nlab:
https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents

For a more explicit version in the case where `R` is of the form `Presieve.ofArr
ows`, see
`CategoryTheory.Presieve.Arrows.Compatible`.
-/
def FamilyOfElements.Compatible (x : FamilyOfElements P R) : Prop :=
  ∀ ⦃Y₁ Y₂ Z⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    g₁ ≫ f₁ = g₂ ≫ f₂ → P.map g₁.op (x f₁ h₁) = P.map g₂.op (x f₂ h₂)

/--
If the category `C` has pullbacks, this is an alternative condition for a family of elements to be
compatible: For any `f : Y ⟶ X` and `g : Z ⟶ X` in the presieve `R`, the restriction of the
given elements for `f` and `g` to the pullback agree.
This is equivalent to being compatible (provided `C` has pullbacks), shown in
`pullbackCompatible_iff`.

This is the definition for a "matching" family given in [MM92], Chapter III, Section 4,
Equation (5). Viewing the type `FamilyOfElements` as the middle object of the fork in
https://stacks.math.columbia.edu/tag/00VM, this condition expresses that `pr₀* (x) = pr₁* (x)`,
using the notation defined there.

For a more explicit version in the case where `R` is of the form `Presieve.ofArrows`, see
`CategoryTheory.Presieve.Arrows.PullbackCompatible`.
-/
/-
**CategoryTheory.Presieve.FamilyOfElements.PullbackCompatible** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P : C
ategoryTheory.Functor Cᵒᵖ (Type w)} →       {X : C} →         {R : CategoryTheor
y.Presieve X} → CategoryTheory.Presieve.FamilyOfElements P R → [R.HasPairwisePul
lbacks] → Prop
参数：Type w。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.HasPairwisePullbacks.has_pullbacks`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Pres
ieve X}   [self : R.HasPairwisePullbacks] {Y Z :…

--- 原说明 ---
If the category `C` has pullbacks, this is an alternative condition for a family
 of elements to be
compatible: For any `f : Y ⟶ X` and `g : Z ⟶ X` in the presieve `R`, the restric
tion of the
given elements for `f` and `g` to the pullback agree.
This is equivalent to being compatible (provided `C` has pullbacks), shown in
`pullbackCompatible_iff`.

This is the definition for a "matching" family given in [MM92], Chapter III, Sec
tion 4,
Equation (5). Viewing the type `FamilyOfElements` as the middle object of the fo
rk in
https://stacks.math.columbia.edu/tag/00VM, this condition expresses that `pr₀* (
x) = pr₁* (x)`,
using the notation defined there.

For a more explicit version in the case where `R` is of the form `Presieve.ofArr
ows`, see
`CategoryTheory.Presieve.Arrows.PullbackCompatible`.
-/
def FamilyOfElements.PullbackCompatible (x : FamilyOfElements P R) [R.HasPairwisePullbacks] :
    Prop :=
  ∀ ⦃Y₁ Y₂⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    haveI := HasPairwisePullbacks.has_pullbacks h₁ h₂
    P.map (pullback.fst f₁ f₂).op (x f₁ h₁) = P.map (pullback.snd f₁ f₂).op (x f₂ h₂)
/-
**CategoryTheory.Presieve.pullbackCompatible_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Presieve`。
形式化陈述：pullbackCompatible_iff (x : FamilyOfElements P R) [R.HasPairwisePullbacks]
 : x.Compatible ↔ x.PullbackCompatible
参数：x : FamilyOfElements P R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.HasPairwisePullbacks.has_pullbacks`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Pres
ieve X}   [self : R.HasPairwisePullbacks] {Y Z :…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem pullbackCompatible_iff (x : FamilyOfElements P R) [R.HasPairwisePullbacks] :
    x.Compatible ↔ x.PullbackCompatible := by
  constructor
  · intro t Y₁ Y₂ f₁ f₂ hf₁ hf₂
    apply t
    have := HasPairwisePullbacks.has_pullbacks hf₁ hf₂
    apply pullback.condition
  · intro t Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    have := HasPairwisePullbacks.has_pullbacks hf₁ hf₂
    rw [← pullback.lift_fst _ _ comm, op_comp, Functor.map_comp, comp_apply,
      t hf₁ hf₂, ← comp_apply, ← Functor.map_comp, ← op_comp, pullback.lift_snd]

/-- The restriction of a compatible family is compatible. -/
/-
**CategoryTheory.Presieve.FamilyOfElements.Compatible.restrict** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements.Compatible`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X : C}   {R₁ R₂ : CategoryTheory.Presieve X} (h : R
₁ ≤ R₂) {x : CategoryTheory.Presieve.FamilyOfElements P R₂},   x.Compatible → (C
ategoryTheory.Presieve.FamilyOfElements.restrict h x).Compatible
参数：Type w；h : R₁ ≤ R₂；CategoryTheory.Presieve.FamilyOfElements.restrict h x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a compatible family is compatible.
-/
theorem FamilyOfElements.Compatible.restrict {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂)
    {x : FamilyOfElements P R₂} : x.Compatible → (x.restrict h).Compatible :=
  fun q _ _ _ g₁ g₂ _ _ h₁ h₂ comm => q g₁ g₂ (h _ _ h₁) (h _ _ h₂) comm

/-- Extend a family of elements to the sieve generated by an arrow set.
This is the construction described as "easy" in Lemma C2.1.3 of [Elephant].
-/
/-
**CategoryTheory.Presieve.FamilyOfElements.sieveExtend** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P : C
ategoryTheory.Functor Cᵒᵖ (Type w)} →       {X : C} →         {R : CategoryTheor
y.Presieve X} →           CategoryTheory.Presieve.FamilyOfElements P R →        
     CategoryTheory.Presieve.FamilyOfElements P (CategoryTheory.Sieve.generate R
).arrows
参数：Type w；CategoryTheory.Sieve.generate R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a family of elements to the sieve generated by an arrow set.
This is the construction described as "easy" in Lemma C2.1.3 of [Elephant].
-/
noncomputable def FamilyOfElements.sieveExtend (x : FamilyOfElements P R) :
    FamilyOfElements P (generate R : Presieve X) := fun _ _ hf =>
  P.map hf.choose_spec.choose.op (x _ hf.choose_spec.choose_spec.choose_spec.1)

/-- The extension of a compatible family to the generated sieve is compatible. -/
/-
**CategoryTheory.Presieve.FamilyOfElements.Compatible.sieveExtend** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements.Compatible`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} {x : Categ
oryTheory.Presieve.FamilyOfElements P R},   x.Compatible → x.sieveExtend.Compati
ble
参数：Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The extension of a compatible family to the generated sieve is compatible.
-/
theorem FamilyOfElements.Compatible.sieveExtend {x : FamilyOfElements P R} (hx : x.Compatible) :
    x.sieveExtend.Compatible := by
  intro _ _ _ _ _ _ _ h₁ h₂ comm
  simp only [FamilyOfElements.sieveExtend, ← comp_apply, ← Functor.map_comp, ← op_comp]
  apply hx
  simp [comm, h₁.choose_spec.choose_spec.choose_spec.2, h₂.choose_spec.choose_spec.choose_spec.2]

/-- The extension of a family agrees with the original family. -/
/-
**CategoryTheory.Presieve.extend_agrees** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Presieve`。
形式化陈述：extend_agrees {x : FamilyOfElements P R} (t : x.Compatible) {f : Y ⟶ X} (h
f : R f) : x.sieveExtend f (le_generate R Y _ hf) = x f hf
参数：t : x.Compatible；hf : R f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The extension of a family agrees with the original family.
-/
theorem extend_agrees {x : FamilyOfElements P R} (t : x.Compatible) {f : Y ⟶ X} (hf : R f) :
    x.sieveExtend f (le_generate R Y _ hf) = x f hf := by
  have h := (le_generate R Y _ hf).choose_spec
  unfold FamilyOfElements.sieveExtend
  rw [t h.choose (𝟙 _) _ hf _]
  · simp
  · rw [id_comp]
    exact h.choose_spec.choose_spec.2

/-- The restriction of an extension is the original. -/
@[simp]
/-
**CategoryTheory.Presieve.restrict_extend** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Presieve`。
形式化陈述：restrict_extend {x : FamilyOfElements P R} (t : x.Compatible) : x.sieveExt
end.restrict (le_generate R) = x
参数：t : x.Compatible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
· 使用定理 `CategoryTheory.Presieve.extend_agrees`：extend_agrees {x : FamilyOfElemen
ts P R} (t : x.Compatible) {f : Y ⟶ X} (hf : R f) : x.sieveExtend f (le_generate
 R Y _ hf) = x f hf

--- 原说明 ---
The restriction of an extension is the original.
-/
theorem restrict_extend {x : FamilyOfElements P R} (t : x.Compatible) :
    x.sieveExtend.restrict (le_generate R) = x := by
  funext Y f hf
  exact extend_agrees t hf
/-
**CategoryTheory.Presieve.FamilyOfElements.Compatible.of_mono** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements.Compatible`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : Categor
yTheory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} (f : P ⟶
 Q) [CategoryTheory.Mono f]   {x : CategoryTheory.Presieve.FamilyOfElements P R}
, (x.map f).Compatible → x.Compatible
参数：Type w；f : P ⟶ Q；x.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.injective_of_mono`：injective_of_mono {X Y : Type u} (f : 
X ⟶ Y) [hf : Mono f] : Function.Injective f
· 使用定理 `CategoryTheory.instMonoAppOfFunctor`：∀ {K : Type u} [inst : CategoryTheo
ry.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C
]   {F G : CategoryTheory…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
lemma FamilyOfElements.Compatible.of_mono (f : P ⟶ Q) [Mono f] {x : R.FamilyOfElements P}
    (hx : (x.map f).Compatible) :
    x.Compatible := by
  intro Y Z W g₁ g₂ f₁ f₂ hf₁ hf₂ heq
  refine injective_of_mono (f.app _) ?_
  simpa using hx _ _ hf₁ hf₂ heq

/--
If the arrow set for a family of elements is actually a sieve (i.e. it is downward closed) then the
consistency condition can be simplified.
This is an equivalent condition, see `compatible_iff_sieveCompatible`.

This is the notion of "matching" given for families on sieves given in [MM92], Chapter III,
Section 4, Equation 1, and nlab: https://ncatlab.org/nlab/show/matching+family.
See also the discussion before Lemma C2.1.4 of [Elephant].
-/
/-
**CategoryTheory.Presieve.FamilyOfElements.SieveCompatible** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P : C
ategoryTheory.Functor Cᵒᵖ (Type w)} →       {X : C} → {S : CategoryTheory.Sieve 
X} → CategoryTheory.Presieve.FamilyOfElements P S.arrows → Prop
参数：Type w。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…

--- 原说明 ---
If the arrow set for a family of elements is actually a sieve (i.e. it is downwa
rd closed) then the
consistency condition can be simplified.
This is an equivalent condition, see `compatible_iff_sieveCompatible`.

This is the notion of "matching" given for families on sieves given in [MM92], C
hapter III,
Section 4, Equation 1, and nlab: https://ncatlab.org/nlab/show/matching+family.
See also the discussion before Lemma C2.1.4 of [Elephant].
-/
def FamilyOfElements.SieveCompatible (x : FamilyOfElements P (S : Presieve X)) : Prop :=
  ∀ ⦃Y Z⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (hf), x (g ≫ f) (S.downward_closed hf g) = P.map g.op (x f hf)
/-
**CategoryTheory.Presieve.compatible_iff_sieveCompatible** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Presieve`。
形式化陈述：compatible_iff_sieveCompatible (x : FamilyOfElements P (S : Presieve X)) :
 x.Compatible ↔ x.SieveCompatible
参数：x : FamilyOfElements P (S : Presieve X)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem compatible_iff_sieveCompatible (x : FamilyOfElements P (S : Presieve X)) :
    x.Compatible ↔ x.SieveCompatible := by
  constructor
  · intro h Y Z f g hf
    simpa using h (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)
  · intro h Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ k
    simp_rw [← h f₁ g₁ h₁, ← h f₂ g₂ h₂]
    congr
/-
**CategoryTheory.Presieve.FamilyOfElements.Compatible.to_sieveCompatible** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements.Compatible`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X : C}   {S : CategoryTheory.Sieve X} {x : Category
Theory.Presieve.FamilyOfElements P S.arrows},   x.Compatible → x.SieveCompatible
参数：Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Presieve.compatible_iff_sieveCompatible`：compatible_iff_s
ieveCompatible (x : FamilyOfElements P (S : Presieve X)) : x.Compatible ↔ x.Siev
eCompatible
-/
theorem FamilyOfElements.Compatible.to_sieveCompatible {x : FamilyOfElements P (S : Presieve X)}
    (t : x.Compatible) : x.SieveCompatible :=
  (compatible_iff_sieveCompatible x).1 t

/--
Given a family of elements `x` for the sieve `S` generated by a presieve `R`, if `x` is restricted
to `R` and then extended back up to `S`, the resulting extension equals `x`.
-/
@[simp]
/-
**CategoryTheory.Presieve.extend_restrict** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Presieve`。
形式化陈述：extend_restrict {x : FamilyOfElements P (generate R).arrows} (t : x.Compat
ible) : (x.restrict (le_generate R)).sieveExtend = x
参数：generate R；t : x.Compatible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.compatible_iff_sieveCompatible`：compatible_iff_s
ieveCompatible (x : FamilyOfElements P (S : Presieve X)) : x.Compatible ↔ x.Siev
eCompatible
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
Given a family of elements `x` for the sieve `S` generated by a presieve `R`, if
 `x` is restricted
to `R` and then extended back up to `S`, the resulting extension equals `x`.
-/
theorem extend_restrict {x : FamilyOfElements P (generate R).arrows} (t : x.Compatible) :
    (x.restrict (le_generate R)).sieveExtend = x := by
  rw [compatible_iff_sieveCompatible] at t
  funext _ _ h
  apply (t _ _ _).symm.trans
  congr
  exact h.choose_spec.choose_spec.choose_spec.2

/--
Two compatible families on the sieve generated by a presieve `R` are equal if and only if they are
equal when restricted to `R`.
-/
/-
**CategoryTheory.Presieve.restrict_inj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Presieve`。
形式化陈述：restrict_inj {x₁ x₂ : FamilyOfElements P (generate R).arrows} (t₁ : x₁.Com
patible) (t₂ : x₂.Compatible) : x₁.restrict (le_generate R) = x₂.restrict (le_ge
nerate R) -> x₁ = x₂
参数：generate R；t₁ : x₁.Compatible；t₂ : x₂.Compatible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.extend_restrict`：extend_restrict {x : FamilyOfEl
ements P (generate R).arrows} (t : x.Compatible) : (x.restrict (le_generate R)).
sieveExtend = x

--- 原说明 ---
Two compatible families on the sieve generated by a presieve `R` are equal if an
d only if they are
equal when restricted to `R`.
-/
theorem restrict_inj {x₁ x₂ : FamilyOfElements P (generate R).arrows} (t₁ : x₁.Compatible)
    (t₂ : x₂.Compatible) : x₁.restrict (le_generate R) = x₂.restrict (le_generate R) → x₁ = x₂ :=
  fun h => by
  rw [← extend_restrict t₁, ← extend_restrict t₂]
  congr

/-- Compatible families of elements for a presheaf of types `P` and a presieve `R`
are in 1-1 correspondence with compatible families for the same presheaf and
the sieve generated by `R`, through extension and restriction. -/
@[simps]
/-
**CategoryTheory.Presieve.compatibleEquivGenerateSieveCompatible** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：compatibleEquivGenerateSieveCompatible : { x : FamilyOfElements P R // x.C
ompatible } ≃ { x : FamilyOfElements P (generate R : Presieve X) // x.Compatible
 } where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R

--- 原说明 ---
Compatible families of elements for a presheaf of types `P` and a presieve `R`
are in 1-1 correspondence with compatible families for the same presheaf and
the sieve generated by `R`, through extension and restriction.
-/
noncomputable def compatibleEquivGenerateSieveCompatible :
    { x : FamilyOfElements P R // x.Compatible } ≃
      { x : FamilyOfElements P (generate R : Presieve X) // x.Compatible } where
  toFun x := ⟨x.1.sieveExtend, x.2.sieveExtend⟩
  invFun x := ⟨x.1.restrict (le_generate R), x.2.restrict _⟩
  left_inv x := Subtype.ext (restrict_extend x.2)
  right_inv x := Subtype.ext (extend_restrict x.2)
/-
**CategoryTheory.Presieve.FamilyOfElements.comp_of_compatible** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X Y : C}   (S : CategoryTheory.Sieve X) {x : Catego
ryTheory.Presieve.FamilyOfElements P S.arrows},   x.Compatible →     ∀ {f : Y ⟶ 
X} (hf : S.arrows f) {Z : C} (g : Z ⟶ Y),       x (CategoryTheory.CategoryStruct
.comp g f) ⋯ = (CategoryTheory.ConcreteCategory.hom (P.map g.op)) (x f hf)
参数：Type w；S : CategoryTheory.Sieve X；hf : S.arrows f；g : Z ⟶ Y；CategoryTheory.Ca
tegoryStruct.comp g f；CategoryTheory.ConcreteCategory.hom (P.map g.op)；x f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem FamilyOfElements.comp_of_compatible (S : Sieve X) {x : FamilyOfElements P S}
    (t : x.Compatible) {f : Y ⟶ X} (hf : S f) {Z} (g : Z ⟶ Y) :
    x (g ≫ f) (S.downward_closed hf g) = P.map g.op (x f hf) := by
  simpa using t (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)
/-
**CategoryTheory.Presieve.FamilyOfElements.compatible_singleton_iff** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X Y : C}   (f : X ⟶ Y) (x : CategoryTheory.Presieve
.FamilyOfElements P (CategoryTheory.Presieve.singleton f)),   x.Compatible ↔    
 ∀ {Z : C} (p₁ p₂ : Z ⟶ X),       CategoryTheory.CategoryStruct.comp p₁ f = Cate
goryTheory.CategoryStruct.comp p₂ f →         (CategoryTheory.ConcreteCategory.h
om (P.map p₁.op)) (x f ⋯) =           (CategoryTheory.ConcreteCategory.hom (P.ma
p p₂.op)) (x f ⋯)
参数：Type w；f : X ⟶ Y；x : CategoryTheory.Presieve.FamilyOfElements P (CategoryTheo
ry.Presieve.singleton f)；p₁ p₂ : Z ⟶ X；CategoryTheory.ConcreteCategory.hom (P.ma
p p₁.op)；x f ⋯；CategoryTheory.ConcreteCategory.hom (P.map p₂.op)；x f ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma FamilyOfElements.compatible_singleton_iff
    {X Y : C} (f : X ⟶ Y) (x : (singleton f).FamilyOfElements P) :
    x.Compatible ↔ ∀ {Z : C} (p₁ p₂ : Z ⟶ X), p₁ ≫ f = p₂ ≫ f →
      P.map p₁.op (x f ⟨⟩) = P.map p₂.op (x f ⟨⟩) := by
  refine ⟨fun H Z p₁ p₂ h ↦ H _ _ _ _ h, fun H Y₁ Y₂ Z g₁ g₂ f₁ f₂ ↦ ?_⟩
  rintro ⟨rfl⟩ ⟨rfl⟩ h
  exact H _ _ h

section FunctorPullback

variable {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C) {Z : D}
variable {T : Presieve (F.obj Z)} {x : FamilyOfElements P T}

/--
Given a family of elements of a sieve `S` on `F(X)`, we can realize it as a family of elements of
`S.functorPullback F`.
-/
/-
**CategoryTheory.Presieve.FamilyOfElements.functorPullback** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P : C
ategoryTheory.Functor Cᵒᵖ (Type w)} →       {D : Type u₂} →         [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D] →           (F : CategoryTheory.Functor D C) →
             {Z : D} →               {T : CategoryTheory.Presieve (F.obj Z)} →  
               CategoryTheory.Presieve.FamilyOfElements P T →                   
CategoryTheory.Presieve.FamilyOfElements (F.op.comp P) (CategoryTheory.Presieve.
functorPullback F T)
参数：Type w；F : CategoryTheory.Functor D C；F.obj Z；F.op.comp P；CategoryTheory.Pres
ieve.functorPullback F T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of elements of a sieve `S` on `F(X)`, we can realize it as a fami
ly of elements of
`S.functorPullback F`.
-/
def FamilyOfElements.functorPullback (x : FamilyOfElements P T) :
    FamilyOfElements (F.op ⋙ P) (T.functorPullback F) := fun _ f hf => x (F.map f) hf
/-
**CategoryTheory.Presieve.FamilyOfElements.Compatible.functorPullback** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements.Compatible`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
₂, u₂} D] (F : CategoryTheory.Functor D C) {Z : D}   {T : CategoryTheory.Presiev
e (F.obj Z)} {x : CategoryTheory.Presieve.FamilyOfElements P T},   x.Compatible 
→ (CategoryTheory.Presieve.FamilyOfElements.functorPullback F x).Compatible
参数：Type w；F : CategoryTheory.Functor D C；F.obj Z；CategoryTheory.Presieve.FamilyO
fElements.functorPullback F x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem FamilyOfElements.Compatible.functorPullback (h : x.Compatible) :
    (x.functorPullback F).Compatible := by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  exact h (F.map g₁) (F.map g₂) h₁ h₂ (by simp only [← F.map_comp, eq])

end FunctorPullback

/-- Given a family of elements of a sieve `S` on `X` whose values factors through `F`, we can
realize it as a family of elements of `S.functorPushforward F`. Since the preimage is obtained by
choice, this is not well-defined generally.
-/
/-
**CategoryTheory.Presieve.FamilyOfElements.functorPushforward** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P : C
ategoryTheory.Functor Cᵒᵖ (Type w)} →       {D : Type u₂} →         [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D] →           (F : CategoryTheory.Functor D C) →
             {X : D} →               {T : CategoryTheory.Presieve X} →          
       CategoryTheory.Presieve.FamilyOfElements (F.op.comp P) T →               
    CategoryTheory.Presieve.FamilyOfElements P (CategoryTheory.Presieve.functorP
ushforward F T)
参数：Type w；F : CategoryTheory.Functor D C；F.op.comp P；CategoryTheory.Presieve.fun
ctorPushforward F T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of elements of a sieve `S` on `X` whose values factors through `F
`, we can
realize it as a family of elements of `S.functorPushforward F`. Since the preima
ge is obtained by
choice, this is not well-defined generally.
-/
noncomputable def FamilyOfElements.functorPushforward {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)
    {X : D} {T : Presieve X} (x : FamilyOfElements (F.op ⋙ P) T) :
    FamilyOfElements P (T.functorPushforward F) := fun Y f h => by
  obtain ⟨Z, g, h, h₁, _⟩ := getFunctorPushforwardStructure h
  exact P.map h.op (x g h₁)

section Pullback

/-- Given a family of elements of a sieve `S` on `X`, and a map `Y ⟶ X`, we can obtain a
family of elements of `S.pullback f` by taking the same elements.
-/
/-
**CategoryTheory.Presieve.FamilyOfElements.pullback** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P : C
ategoryTheory.Functor Cᵒᵖ (Type w)} →       {X Y : C} →         {S : CategoryThe
ory.Sieve X} →           (f : Y ⟶ X) →             CategoryTheory.Presieve.Famil
yOfElements P S.arrows →               CategoryTheory.Presieve.FamilyOfElements 
P (CategoryTheory.Sieve.pullback f S).arrows
参数：Type w；f : Y ⟶ X；CategoryTheory.Sieve.pullback f S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of elements of a sieve `S` on `X`, and a map `Y ⟶ X`, we can obta
in a
family of elements of `S.pullback f` by taking the same elements.
-/
def FamilyOfElements.pullback (f : Y ⟶ X) (x : FamilyOfElements P (S : Presieve X)) :
    FamilyOfElements P (S.pullback f : Presieve Y) := fun _ g hg => x (g ≫ f) hg
/-
**CategoryTheory.Presieve.FamilyOfElements.Compatible.pullback** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements.Compatible`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X Y : C}   {S : CategoryTheory.Sieve X} (f : Y ⟶ X)
 {x : CategoryTheory.Presieve.FamilyOfElements P S.arrows},   x.Compatible → (Ca
tegoryTheory.Presieve.FamilyOfElements.pullback f x).Compatible
参数：Type w；f : Y ⟶ X；CategoryTheory.Presieve.FamilyOfElements.pullback f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem FamilyOfElements.Compatible.pullback (f : Y ⟶ X) {x : FamilyOfElements P S.arrows}
    (h : x.Compatible) : (x.pullback f).Compatible := by
  simp only [compatible_iff_sieveCompatible] at h ⊢
  intro W Z f₁ f₂ hf
  unfold FamilyOfElements.pullback
  rw [← h (f₁ ≫ f) f₂ hf]
  congr 1
  simp only [assoc]

end Pullback

@[simp]
/-
**CategoryTheory.Presieve.FamilyOfElements.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Presieve.FamilyOfElements`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} (x : Categ
oryTheory.Presieve.FamilyOfElements P R),   x.map (CategoryTheory.CategoryStruct
.id P) = x
参数：Type w；x : CategoryTheory.Presieve.FamilyOfElements P R；CategoryTheory.Catego
ryStruct.id P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FamilyOfElements.map_id (x : FamilyOfElements P R) :
    x.map (𝟙 _) = x :=
  rfl

@[simp]
/-
**CategoryTheory.Presieve.FamilyOfElements.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q U : Categ
oryTheory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} (x : C
ategoryTheory.Presieve.FamilyOfElements P R) (f : P ⟶ Q) (g : Q ⟶ U),   (x.map f
).map g = x.map (CategoryTheory.CategoryStruct.comp f g)
参数：Type w；x : CategoryTheory.Presieve.FamilyOfElements P R；f : P ⟶ Q；g : Q ⟶ U；x
.map f；CategoryTheory.CategoryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FamilyOfElements.map_comp (x : FamilyOfElements P R) (f : P ⟶ Q) (g : Q ⟶ U) :
    (x.map f).map g = x.map (f ≫ g) := by
  rfl
/-
**CategoryTheory.Presieve.FamilyOfElements.Compatible.map** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Presieve.FamilyOfElements.Compatible`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : Categor
yTheory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} (f : P ⟶
 Q) {x : CategoryTheory.Presieve.FamilyOfElements P R},   x.Compatible → (x.map 
f).Compatible
参数：Type w；f : P ⟶ Q；x.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
theorem FamilyOfElements.Compatible.map (f : P ⟶ Q) {x : FamilyOfElements P R}
    (h : x.Compatible) : (x.map f).Compatible := by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  unfold FamilyOfElements.map
  rwa [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, h]

/--
The given element `t` of `P.obj (op X)` is an *amalgamation* for the family of elements `x` if every
restriction `P.map f.op t = x_f` for every arrow `f` in the presieve `R`.

This is the definition given in https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents,
and https://ncatlab.org/nlab/show/matching+family, as well as [MM92], Chapter III, Section 4,
equation (2).
-/
/-
**CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P : C
ategoryTheory.Functor Cᵒᵖ (Type w)} →       {X : C} →         {R : CategoryTheor
y.Presieve X} → CategoryTheory.Presieve.FamilyOfElements P R → P.obj (Opposite.o
p X) → Prop
参数：Type w；Opposite.op X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The given element `t` of `P.obj (op X)` is an *amalgamation* for the family of e
lements `x` if every
restriction `P.map f.op t = x_f` for every arrow `f` in the presieve `R`.

This is the definition given in https://ncatlab.org/nlab/show/sheaf#GeneralDefin
itionInComponents,
and https://ncatlab.org/nlab/show/matching+family, as well as [MM92], Chapter II
I, Section 4,
equation (2).
-/
def FamilyOfElements.IsAmalgamation (x : FamilyOfElements P R) (t : P.obj (op X)) : Prop :=
  ∀ ⦃Y : C⦄ (f : Y ⟶ X) (h : R f), P.map f.op t = x f h
/-
**CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation.map** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : Categor
yTheory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} {x : Cat
egoryTheory.Presieve.FamilyOfElements P R} {t : P.obj (Opposite.op X)}   (f : P 
⟶ Q),   x.IsAmalgamation t → (x.map f).IsAmalgamation ((CategoryTheory.ConcreteC
ategory.hom (f.app (Opposite.op X))) t)
参数：Type w；Opposite.op X；f : P ⟶ Q；x.map f；(CategoryTheory.ConcreteCategory.hom (
f.app (Opposite.op X))) t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
-/
theorem FamilyOfElements.IsAmalgamation.map {x : FamilyOfElements P R} {t} (f : P ⟶ Q)
    (h : x.IsAmalgamation t) : (x.map f).IsAmalgamation (f.app (op X) t) := by
  intro Y g hg
  dsimp [FamilyOfElements.map]
  change (f.app _ ≫ Q.map _) _ = _
  rw [← f.naturality, comp_apply, h g hg]
/-
**CategoryTheory.Presieve.is_compatible_of_exists_amalgamation** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：is_compatible_of_exists_amalgamation (x : FamilyOfElements P R) (h : exist
s t, x.IsAmalgamation t) : x.Compatible
参数：x : FamilyOfElements P R；h : exists t, x.IsAmalgamation t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem is_compatible_of_exists_amalgamation (x : FamilyOfElements P R)
    (h : ∃ t, x.IsAmalgamation t) : x.Compatible := by
  obtain ⟨t, ht⟩ := h
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
  rw [← ht _ h₁, ← ht _ h₂, ← comp_apply, ← Functor.map_comp, ← op_comp, comm]
  simp
/-
**CategoryTheory.Presieve.isAmalgamation_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Presieve`。
形式化陈述：isAmalgamation_restrict {R₁ R₂ : Presieve X} (h : R₁ <= R₂) (x : FamilyOfE
lements P R₂) (t : P.obj (op X)) (ht : x.IsAmalgamation t) : (x.restrict h).IsAm
algamation t
参数：h : R₁ <= R₂；x : FamilyOfElements P R₂；t : P.obj (op X)；ht : x.IsAmalgamation
 t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isAmalgamation_restrict {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂) (x : FamilyOfElements P R₂)
    (t : P.obj (op X)) (ht : x.IsAmalgamation t) : (x.restrict h).IsAmalgamation t := fun Y f hf =>
  ht f (h Y _ hf)
/-
**CategoryTheory.Presieve.isAmalgamation_sieveExtend** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Presieve`。
形式化陈述：isAmalgamation_sieveExtend {R : Presieve X} (x : FamilyOfElements P R) (t 
: P.obj (op X)) (ht : x.IsAmalgamation t) : x.sieveExtend.IsAmalgamation t
参数：x : FamilyOfElements P R；t : P.obj (op X)；ht : x.IsAmalgamation t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isAmalgamation_sieveExtend {R : Presieve X} (x : FamilyOfElements P R) (t : P.obj (op X))
    (ht : x.IsAmalgamation t) : x.sieveExtend.IsAmalgamation t := by
  intro Y f hf
  dsimp [FamilyOfElements.sieveExtend]
  rw [← ht _, ← comp_apply, ← Functor.map_comp, ← op_comp, hf.choose_spec.choose_spec.choose_spec.2]

@[simp]
/-
**CategoryTheory.Presieve.FamilyOfElements.isAmalgamation_singleton_iff** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X Y : C}   (f : X ⟶ Y) (x : CategoryTheory.Presieve
.FamilyOfElements P (CategoryTheory.Presieve.singleton f))   (y : P.obj (Opposit
e.op Y)), x.IsAmalgamation y ↔ (CategoryTheory.ConcreteCategory.hom (P.map f.op)
) y = x f ⋯
参数：Type w；f : X ⟶ Y；x : CategoryTheory.Presieve.FamilyOfElements P (CategoryTheo
ry.Presieve.singleton f)；y : P.obj (Opposite.op Y)；CategoryTheory.ConcreteCatego
ry.hom (P.map f.op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma FamilyOfElements.isAmalgamation_singleton_iff {X Y : C} (f : X ⟶ Y)
    (x : (singleton f).FamilyOfElements P) (y : P.obj (op Y)) :
    x.IsAmalgamation y ↔ P.map f.op y = x f ⟨⟩ := by
  refine ⟨fun H ↦ H _ _, ?_⟩
  rintro H Y g ⟨rfl⟩
  exact H
/-
**CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation.of_mono** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : Categor
yTheory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} (f : P ⟶
 Q) [CategoryTheory.Mono f] {x : CategoryTheory.Presieve.FamilyOfElements P R}  
 {t : P.obj (Opposite.op X)},   (x.map f).IsAmalgamation ((CategoryTheory.Concre
teCategory.hom (f.app (Opposite.op X))) t) → x.IsAmalgamation t
参数：Type w；f : P ⟶ Q；Opposite.op X；x.map f；(CategoryTheory.ConcreteCategory.hom (
f.app (Opposite.op X))) t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.injective_of_mono`：injective_of_mono {X Y : Type u} (f : 
X ⟶ Y) [hf : Mono f] : Function.Injective f
· 使用定理 `CategoryTheory.instMonoAppOfFunctor`：∀ {K : Type u} [inst : CategoryTheo
ry.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C
]   {F G : CategoryTheory…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
lemma FamilyOfElements.IsAmalgamation.of_mono (f : P ⟶ Q) [Mono f] {x : R.FamilyOfElements P}
    {t : P.obj (.op X)} (ht : (x.map f).IsAmalgamation (f.app _ t)) :
    x.IsAmalgamation t := by
  intro Y u hu
  refine injective_of_mono (f.app _) ?_
  simpa using ht _ hu

/-- A presheaf is separated for a presieve if there is at most one amalgamation. -/
/-
**CategoryTheory.Presieve.IsSeparatedFor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Presieve`。
形式化陈述：IsSeparatedFor (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) : Prop
参数：P : Cᵒᵖ ⥤ Type w；R : Presieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presheaf is separated for a presieve if there is at most one amalgamation.
-/
def IsSeparatedFor (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) : Prop :=
  ∀ (x : FamilyOfElements P R) (t₁ t₂), x.IsAmalgamation t₁ → x.IsAmalgamation t₂ → t₁ = t₂
/-
**CategoryTheory.Presieve.IsSeparatedFor.ext** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Presieve.IsSeparatedFor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X},   Categor
yTheory.Presieve.IsSeparatedFor P R →     ∀ {t₁ t₂ : P.obj (Opposite.op X)},    
   (∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄,           R f →             (CategoryTheory.ConcreteC
ategory.hom (P.map f.op)) t₁ =               (CategoryTheory.ConcreteCategory.ho
m (P.map f.op)) t₂) →         t₁ = t₂
参数：Type w；Opposite.op X；∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄,           R f →             (Cate
goryTheory.ConcreteCategory.hom (P.map f.op)) t₁ =               (CategoryTheory
.ConcreteCategory.hom (P.map f.op)) t₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSeparatedFor.ext {R : Presieve X} (hR : IsSeparatedFor P R) {t₁ t₂ : P.obj (op X)}
    (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : R f), P.map f.op t₁ = P.map f.op t₂) : t₁ = t₂ :=
  hR (fun _ f _ => P.map f.op t₂) t₁ t₂ (fun _ _ hf => h hf) fun _ _ _ => rfl
/-
**CategoryTheory.Presieve.isSeparatedFor_iff_generate** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Presieve`。
形式化陈述：isSeparatedFor_iff_generate : IsSeparatedFor P R ↔ IsSeparatedFor P (gener
ate R : Presieve X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
· 使用定理 `CategoryTheory.Presieve.isAmalgamation_restrict`：isAmalgamation_restrict
 {R₁ R₂ : Presieve X} (h : R₁ <= R₂) (x : FamilyOfElements P R₂) (t : P.obj (op 
X)) (ht : x.IsAmalgamation t) : (x.re…
· 使用定理 `CategoryTheory.Presieve.isAmalgamation_sieveExtend`：isAmalgamation_sieve
Extend {R : Presieve X} (x : FamilyOfElements P R) (t : P.obj (op X)) (ht : x.Is
Amalgamation t) : x.sieveExtend.IsAmalga…
-/
theorem isSeparatedFor_iff_generate :
    IsSeparatedFor P R ↔ IsSeparatedFor P (generate R : Presieve X) := by
  constructor
  · intro h x t₁ t₂ ht₁ ht₂
    apply h (x.restrict (le_generate R)) t₁ t₂ _ _
    · exact isAmalgamation_restrict _ x t₁ ht₁
    · exact isAmalgamation_restrict _ x t₂ ht₂
  · intro h x t₁ t₂ ht₁ ht₂
    apply h x.sieveExtend
    · exact isAmalgamation_sieveExtend x t₁ ht₁
    · exact isAmalgamation_sieveExtend x t₂ ht₂
/-
**CategoryTheory.Presieve.isSeparatedFor_top** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Presieve`。
形式化陈述：isSeparatedFor_top (P : Cᵒᵖ ⥤ Type w) : IsSeparatedFor P (⊤ : Presieve X)
参数：P : Cᵒᵖ ⥤ Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
-/
theorem isSeparatedFor_top (P : Cᵒᵖ ⥤ Type w) : IsSeparatedFor P (⊤ : Presieve X) :=
  fun x t₁ t₂ h₁ h₂ => by
  have q₁ := h₁ (𝟙 X) (by tauto)
  have q₂ := h₂ (𝟙 X) (by tauto)
  simp only [op_id, Functor.map_id, id_apply] at q₁ q₂
  rw [q₁, q₂]

/-- We define `P` to be a sheaf for the presieve `R` if every compatible family has a unique
amalgamation.

This is the definition of a sheaf for the given presieve given in C2.1.2 of [Elephant], and
https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents.
Using `compatible_iff_sieveCompatible`,
this is equivalent to the definition of a sheaf in [MM92], Chapter III, Section 4.
-/
/-
**CategoryTheory.Presieve.IsSheafFor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.P
resieve`。
形式化陈述：IsSheafFor (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) : Prop
参数：P : Cᵒᵖ ⥤ Type w；R : Presieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `P` to be a sheaf for the presieve `R` if every compatible family has 
a unique
amalgamation.

This is the definition of a sheaf for the given presieve given in C2.1.2 of [Ele
phant], and
https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents.
Using `compatible_iff_sieveCompatible`,
this is equivalent to the definition of a sheaf in [MM92], Chapter III, Section 
4.
-/
def IsSheafFor (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) : Prop :=
  ∀ x : FamilyOfElements P R, x.Compatible → ∃! t, x.IsAmalgamation t

/-- This is an equivalent condition to be a sheaf, which is useful for the abstraction to local
operators on elementary toposes. However this definition is defined only for sieves, not presieves.
The equivalence between this and `IsSheafFor` is given in `isSheafFor_iff_yonedaSheafCondition`.
This version is also useful to establish that being a sheaf is preserved under isomorphism of
presheaves.

See the discussion before Equation (3) of [MM92], Chapter III, Section 4. See also C2.1.4 of
[Elephant]. -/
@[stacks 00Z8 "Direct reformulation"]
/-
**CategoryTheory.Presieve.YonedaSheafCondition** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Presieve`。
形式化陈述：YonedaSheafCondition (P : Cᵒᵖ ⥤ Type v₁) (S : Sieve X) : Prop
参数：P : Cᵒᵖ ⥤ Type v₁；S : Sieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an equivalent condition to be a sheaf, which is useful for the abstracti
on to local
operators on elementary toposes. However this definition is defined only for sie
ves, not presieves.
The equivalence between this and `IsSheafFor` is given in `isSheafFor_iff_yoneda
SheafCondition`.
This version is also useful to establish that being a sheaf is preserved under i
somorphism of
presheaves.

See the discussion before Equation (3) of [MM92], Chapter III, Section 4. See al
so C2.1.4 of
[Elephant].
-/
def YonedaSheafCondition (P : Cᵒᵖ ⥤ Type v₁) (S : Sieve X) : Prop :=
  ∀ f : S.functor ⟶ P, ∃! g, S.functorInclusion ≫ g = f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation). This is a (primarily internal) equivalence between natural transformations
and compatible families.

Cf the discussion after Lemma 7.47.10 in <https://stacks.math.columbia.edu/tag/00YW>. See also
the proof of C2.1.4 of [Elephant], and the discussion in [MM92], Chapter III, Section 4.
-/
@[simps]
/-
**CategoryTheory.Presieve.shrinkFunctorHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Presieve`。
形式化陈述：shrinkFunctorHomEquiv [LocallySmall.{w} C] {F : Cᵒᵖ ⥤ Type w} : (S.shrinkF
unctor.toFunctor ⟶ F) ≃ { x : S.arrows.FamilyOfElements F // x.Compatible } wher
e toFun t
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
(Implementation). This is a (primarily internal) equivalence between natural tra
nsformations
and compatible families.

Cf the discussion after Lemma 7.47.10 in <https://stacks.math.columbia.edu/tag/0
0YW>. See also
the proof of C2.1.4 of [Elephant], and the discussion in [MM92], Chapter III, Se
ction 4.
-/
noncomputable def shrinkFunctorHomEquiv [LocallySmall.{w} C] {F : Cᵒᵖ ⥤ Type w} :
    (S.shrinkFunctor.toFunctor ⟶ F) ≃ { x : S.arrows.FamilyOfElements F // x.Compatible } where
  toFun t := ⟨fun Y f hf ↦ t.app _ ⟨shrinkYonedaObjObjEquiv.symm f, by simpa⟩, by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z f g hf
    simp only [shrinkFunctor_obj, ← NatTrans.naturality_apply]
    rw! [shrinkYonedaObjObjEquiv_symm_comp]
    rfl⟩
  invFun t :=
    { app X := ↾fun f ↦ t.1 _ f.mem
      naturality Y Z g := by
        ext ⟨f, hf⟩
        dsimp
        convert! t.2.to_sieveCompatible _ _ _
        simp only [Opposite.op_unop, shrinkYonedaObjObjEquiv_obj_map]
        rfl }
  left_inv t := by cat_disch
  right_inv x := by
    ext
    dsimp
    rw! [Equiv.apply_symm_apply]
    simp

@[deprecated "In terms of `Sieve.shrinkFunctor`" (since := "2026-03-13")]
alias natTransEquivCompatibleFamily := shrinkFunctorHomEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presieve.shrinkFunctor_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Presieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shrinkFunctor_ι_comp_eq_iff_isAmalgamation [LocallySmall.{w} C] (F : Cᵒᵖ ⥤ Type w)
    (f : S.shrinkFunctor.toFunctor ⟶ F) (g : shrinkYoneda.{w}.obj X ⟶ F) :
    S.shrinkFunctor.ι ≫ g = f ↔
      (shrinkFunctorHomEquiv f).1.IsAmalgamation (shrinkYonedaEquiv g) := by
  dsimp [Presieve.FamilyOfElements.IsAmalgamation]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl Y f hf
    simp [shrinkYonedaEquiv_naturality, shrinkYonedaEquiv_comp, shrinkYonedaEquiv_shrinkYoneda_map]
  · ext Y ⟨u, hu⟩
    convert! h (shrinkYonedaObjObjEquiv u) hu
    · rw [shrinkYonedaEquiv_naturality, shrinkYonedaEquiv_comp, shrinkYonedaEquiv_shrinkYoneda_map]
      simp
    · rw! [Equiv.symm_apply_apply]
      rfl

@[deprecated "In terms of `Sieve.shrinkFunctor`" (since := "2026-03-13")]
alias extension_iff_amalgamation := shrinkFunctor_ι_comp_eq_iff_isAmalgamation
/-
**CategoryTheory.Presieve.isSheafFor_iff_bijective_shrinkFunctor_** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Presieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isSheafFor_iff_bijective_shrinkFunctor_ι_comp [LocallySmall.{w} C] {X : C}
    (S : Sieve X) (F : Cᵒᵖ ⥤ Type w) :
    IsSheafFor F S.arrows ↔
      Function.Bijective (fun g : _ ⟶ F ↦ S.shrinkFunctor.ι ≫ g) := by
  simp only [IsSheafFor, Function.bijective_iff_existsUnique,
    shrinkFunctor_ι_comp_eq_iff_isAmalgamation, shrinkFunctorHomEquiv.forall_congr_left,
    Subtype.forall]
  exact forall₂_congr fun x hx ↦ by simp [Equiv.existsUnique_congr_right]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The yoneda version of the sheaf condition is equivalent to the sheaf condition.

C2.1.4 of [Elephant].
-/
/-
**CategoryTheory.Presieve.isSheafFor_iff_yonedaSheafCondition** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：isSheafFor_iff_yonedaSheafCondition {P : Cᵒᵖ ⥤ Type v₁} : IsSheafFor P (S 
: Presieve X) ↔ YonedaSheafCondition P S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp`：i
sSheafFor_iff_bijective_shrinkFunctor_ι_comp [LocallySmall.{w} C] {X : C} (S : S
ieve X) (F : Cᵒᵖ ⥤ Type w) : IsSheafFor F S.arrows ↔ Functi…
· 使用定理 `CategoryTheory.Presieve.YonedaSheafCondition.eq_1`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {X : C} (P : CategoryTheory.Functor Cᵒᵖ (
Type v₁))   (S : CategoryTheory.Sieve X…
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Equiv.existsUnique_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop
} (e : α ≃ β), (∃! a, p a) ↔ ∃! b, p (e.symm b)
· 使用定理 `existsUnique_congr`：existsUnique_congr {p q : α -> Prop} (h : forall a, 
p a ↔ q a) : (exists! a, p a) ↔ exists! a, q a
· 使用定理 `CategoryTheory.NatTrans.ext_iff`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}
   {F G : CategoryThe…
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext_iff`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_
1 : (X Y : C) → FunLike (FC X Y) …
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The yoneda version of the sheaf condition is equivalent to the sheaf condition.

C2.1.4 of [Elephant].
-/
theorem isSheafFor_iff_yonedaSheafCondition {P : Cᵒᵖ ⥤ Type v₁} :
    IsSheafFor P (S : Presieve X) ↔ YonedaSheafCondition P S := by
  rw [isSheafFor_iff_bijective_shrinkFunctor_ι_comp, YonedaSheafCondition,
    Function.bijective_iff_existsUnique,
    Equiv.forall_congr_left S.shrinkFunctorIsoFunctor.homFromEquiv]
  refine forall_congr' fun a ↦ ?_
  rw [Equiv.existsUnique_congr_left (shrinkYonedaIsoYoneda.app X).homFromEquiv]
  refine existsUnique_congr fun b ↦ ?_
  dsimp
  rw [NatTrans.ext_iff, NatTrans.ext_iff, funext_iff, funext_iff]
  congr!
  rw [ConcreteCategory.hom_ext_iff, ConcreteCategory.hom_ext_iff]
  dsimp [functor]
  simp only [Subtype.forall, shrinkYonedaObjObjEquiv.forall_congr_left, Equiv.apply_symm_apply]
  congr!
  simp

/--
If `P` is a sheaf for the sieve `S` on `X`, a natural transformation from `S` (viewed as a functor)
to `P` can be (uniquely) extended to all of `yoneda.obj X`.
```
      f
   S  →  P
   ↓  ↗
   yX
```
-/
/-
**CategoryTheory.Presieve.IsSheafFor.extend** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Presieve.IsSheafFor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X : C
} →       {S : CategoryTheory.Sieve X} →         {P : CategoryTheory.Functor Cᵒᵖ
 (Type v₁)} →           CategoryTheory.Presieve.IsSheafFor P S.arrows → (S.funct
or ⟶ P) → (CategoryTheory.yoneda.obj X ⟶ P)
参数：Type v₁；S.functor ⟶ P；CategoryTheory.yoneda.obj X ⟶ P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is a sheaf for the sieve `S` on `X`, a natural transformation from `S` (v
iewed as a functor)
to `P` can be (uniquely) extended to all of `yoneda.obj X`.
```
      f
   S  →  P
   ↓  ↗
   yX
```
-/
noncomputable def IsSheafFor.extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P (S : Presieve X))
    (f : S.functor ⟶ P) : yoneda.obj X ⟶ P :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose

/--
Show that the extension of `f : S.functor ⟶ P` to all of `yoneda.obj X` is in fact an extension,
i.e. that the triangle below commutes, provided `P` is a sheaf for `S`
```
      f
   S  →  P
   ↓  ↗
   yX
```
-/
@[reassoc (attr := simp)]
/-
**CategoryTheory.Presieve.IsSheafFor.functorInclusion_comp_extend** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Presieve.IsSheafFor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} {S : C
ategoryTheory.Sieve X}   {P : CategoryTheory.Functor Cᵒᵖ (Type v₁)} (h : Categor
yTheory.Presieve.IsSheafFor P S.arrows) (f : S.functor ⟶ P),   CategoryTheory.Ca
tegoryStruct.comp S.functorInclusion (h.extend f) = f
参数：Type v₁；h : CategoryTheory.Presieve.IsSheafFor P S.arrows；f : S.functor ⟶ P；h
.extend f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_yonedaSheafCondition`：isSheafFor_
iff_yonedaSheafCondition {P : Cᵒᵖ ⥤ Type v₁} : IsSheafFor P (S : Presieve X) ↔ Y
onedaSheafCondition P S

--- 原说明 ---
Show that the extension of `f : S.functor ⟶ P` to all of `yoneda.obj X` is in fa
ct an extension,
i.e. that the triangle below commutes, provided `P` is a sheaf for `S`
```
      f
   S  →  P
   ↓  ↗
   yX
```
-/
theorem IsSheafFor.functorInclusion_comp_extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P S.arrows)
    (f : S.functor ⟶ P) : S.functorInclusion ≫ h.extend f = f :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose_spec

/-- The extension of `f` to `yoneda.obj X` is unique. -/
/-
**CategoryTheory.Presieve.IsSheafFor.unique_extend** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Presieve.IsSheafFor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} {S : C
ategoryTheory.Sieve X}   {P : CategoryTheory.Functor Cᵒᵖ (Type v₁)} (h : Categor
yTheory.Presieve.IsSheafFor P S.arrows) {f : S.functor ⟶ P}   (t : CategoryTheor
y.yoneda.obj X ⟶ P), CategoryTheory.CategoryStruct.comp S.functorInclusion t = f
 → t = h.extend f
参数：Type v₁；h : CategoryTheory.Presieve.IsSheafFor P S.arrows；t : CategoryTheory.
yoneda.obj X ⟶ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_yonedaSheafCondition`：isSheafFor_
iff_yonedaSheafCondition {P : Cᵒᵖ ⥤ Type v₁} : IsSheafFor P (S : Presieve X) ↔ Y
onedaSheafCondition P S
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.functorInclusion_comp_extend`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} {S : CategoryTheory
.Sieve X}   {P : CategoryTheory.Functor Cᵒᵖ (Type v₁)…

--- 原说明 ---
The extension of `f` to `yoneda.obj X` is unique.
-/
theorem IsSheafFor.unique_extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P S.arrows)
    {f : S.functor ⟶ P} (t : yoneda.obj X ⟶ P) (ht : S.functorInclusion ≫ t = f) :
    t = h.extend f :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).unique ht (h.functorInclusion_comp_extend f)

/--
If `P` is a sheaf for the sieve `S` on `X`, then if two natural transformations from `yoneda.obj X`
to `P` agree when restricted to the subfunctor given by `S`, they are equal.
-/
/-
**CategoryTheory.Presieve.IsSheafFor.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Presieve.IsSheafFor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} {S : C
ategoryTheory.Sieve X}   {P : CategoryTheory.Functor Cᵒᵖ (Type v₁)},   CategoryT
heory.Presieve.IsSheafFor P S.arrows →     ∀ (t₁ t₂ : CategoryTheory.yoneda.obj 
X ⟶ P),       CategoryTheory.CategoryStruct.comp S.functorInclusion t₁ =        
   CategoryTheory.CategoryStruct.comp S.functorInclusion t₂ →         t₁ = t₂
参数：Type v₁；t₁ t₂ : CategoryTheory.yoneda.obj X ⟶ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.unique_extend`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {X : C} {S : CategoryTheory.Sieve X}   {P 
: CategoryTheory.Functor Cᵒᵖ (Type v₁)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `P` is a sheaf for the sieve `S` on `X`, then if two natural transformations 
from `yoneda.obj X`
to `P` agree when restricted to the subfunctor given by `S`, they are equal.
-/
theorem IsSheafFor.hom_ext {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P (S : Presieve X))
    (t₁ t₂ : yoneda.obj X ⟶ P) (ht : S.functorInclusion ≫ t₁ = S.functorInclusion ≫ t₂) :
    t₁ = t₂ :=
  (h.unique_extend t₁ ht).trans (h.unique_extend t₂ rfl).symm

/-- `P` is a sheaf for `R` iff it is separated for `R` and there exists an amalgamation. -/
/-
**CategoryTheory.Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFo
r** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor : (IsSeparatedFor 
P R ∧ forall x : FamilyOfElements P R, x.Compatible -> exists t, x.IsAmalgamatio
n t) ↔ IsSheafFor P R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.eq_1`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X : C} (P : CategoryTheory.Functor Cᵒᵖ (Type w
))   (R : CategoryTheory.Presieve…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `CategoryTheory.Presieve.is_compatible_of_exists_amalgamation`：is_compati
ble_of_exists_amalgamation (x : FamilyOfElements P R) (h : exists t, x.IsAmalgam
ation t) : x.Compatible
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x

--- 原说明 ---
`P` is a sheaf for `R` iff it is separated for `R` and there exists an amalgamat
ion.
-/
theorem isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor :
    (IsSeparatedFor P R ∧ ∀ x : FamilyOfElements P R, x.Compatible → ∃ t, x.IsAmalgamation t) ↔
      IsSheafFor P R := by
  rw [IsSeparatedFor, ← forall_and]
  apply forall_congr'
  intro x
  constructor
  · intro z hx
    exact existsUnique_of_exists_of_unique (z.2 hx) z.1
  · intro h
    refine ⟨?_, ExistsUnique.exists ∘ h⟩
    intro t₁ t₂ ht₁ ht₂
    apply (h _).unique ht₁ ht₂
    exact is_compatible_of_exists_amalgamation x ⟨_, ht₂⟩

/-- If `P` is separated for `R` and every family has an amalgamation, then `P` is a sheaf for `R`.
-/
/-
**CategoryTheory.Presieve.IsSeparatedFor.isSheafFor** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Presieve.IsSeparatedFor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X},   Categor
yTheory.Presieve.IsSeparatedFor P R →     (∀ (x : CategoryTheory.Presieve.Family
OfElements P R), x.Compatible → ∃ t, x.IsAmalgamation t) →       CategoryTheory.
Presieve.IsSheafFor P R
参数：Type w；∀ (x : CategoryTheory.Presieve.FamilyOfElements P R), x.Compatible → ∃
 t, x.IsAmalgamation t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isS
heafFor`：isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor : (IsSeparatedF
or P R ∧ forall x : FamilyOfElements P R, x.Compatible -> exists t, x…

--- 原说明 ---
If `P` is separated for `R` and every family has an amalgamation, then `P` is a 
sheaf for `R`.
-/
theorem IsSeparatedFor.isSheafFor (t : IsSeparatedFor P R) :
    (∀ x : FamilyOfElements P R, x.Compatible → ∃ t, x.IsAmalgamation t) → IsSheafFor P R := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  exact And.intro t

/-- If `P` is a sheaf for `R`, it is separated for `R`. -/
/-
**CategoryTheory.Presieve.IsSheafFor.isSeparatedFor** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Presieve.IsSheafFor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X}, CategoryT
heory.Presieve.IsSheafFor P R → CategoryTheory.Presieve.IsSeparatedFor P R
参数：Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isS
heafFor`：isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor : (IsSeparatedF
or P R ∧ forall x : FamilyOfElements P R, x.Compatible -> exists t, x…

--- 原说明 ---
If `P` is a sheaf for `R`, it is separated for `R`.
-/
theorem IsSheafFor.isSeparatedFor : IsSheafFor P R → IsSeparatedFor P R := fun q =>
  (isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.2 q).1

/-- Get the amalgamation of the given compatible family, provided we have a sheaf. -/
/-
**CategoryTheory.Presieve.IsSheafFor.amalgamate** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Presieve.IsSheafFor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P : C
ategoryTheory.Functor Cᵒᵖ (Type w)} →       {X : C} →         {R : CategoryTheor
y.Presieve X} →           CategoryTheory.Presieve.IsSheafFor P R →             (
x : CategoryTheory.Presieve.FamilyOfElements P R) → x.Compatible → P.obj (Opposi
te.op X)
参数：Type w；x : CategoryTheory.Presieve.FamilyOfElements P R；Opposite.op X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the amalgamation of the given compatible family, provided we have a sheaf.
-/
noncomputable def IsSheafFor.amalgamate (t : IsSheafFor P R) (x : FamilyOfElements P R)
    (hx : x.Compatible) : P.obj (op X) :=
  (t x hx).exists.choose
/-
**CategoryTheory.Presieve.IsSheafFor.isAmalgamation** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Presieve.IsSheafFor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} (t : Categ
oryTheory.Presieve.IsSheafFor P R)   {x : CategoryTheory.Presieve.FamilyOfElemen
ts P R} (hx : x.Compatible), x.IsAmalgamation (t.amalgamate x hx)
参数：Type w；t : CategoryTheory.Presieve.IsSheafFor P R；hx : x.Compatible；t.amalgam
ate x hx。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
-/
theorem IsSheafFor.isAmalgamation (t : IsSheafFor P R) {x : FamilyOfElements P R}
    (hx : x.Compatible) : x.IsAmalgamation (t.amalgamate x hx) :=
  (t x hx).exists.choose_spec

@[simp]
/-
**CategoryTheory.Presieve.IsSheafFor.valid_glue** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Presieve.IsSheafFor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.Functor Cᵒᵖ (Type w)} {X Y : C}   {R : CategoryTheory.Presieve X} (t : Cat
egoryTheory.Presieve.IsSheafFor P R)   {x : CategoryTheory.Presieve.FamilyOfElem
ents P R} (hx : x.Compatible) (f : Y ⟶ X) (Hf : R f),   (CategoryTheory.Concrete
Category.hom (P.map f.op)) (t.amalgamate x hx) = x f Hf
参数：Type w；t : CategoryTheory.Presieve.IsSheafFor P R；hx : x.Compatible；f : Y ⟶ X
；Hf : R f；CategoryTheory.ConcreteCategory.hom (P.map f.op)；t.amalgamate x hx。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isAmalgamation`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
-/
theorem IsSheafFor.valid_glue (t : IsSheafFor P R) {x : FamilyOfElements P R} (hx : x.Compatible)
    (f : Y ⟶ X) (Hf : R f) : P.map f.op (t.amalgamate x hx) = x f Hf :=
  t.isAmalgamation hx f Hf

/-- C2.1.3 in [Elephant] -/
/-
**CategoryTheory.Presieve.isSheafFor_iff_generate** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Presieve`。
形式化陈述：isSheafFor_iff_generate (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (
generate R : Presieve X)
参数：R : Presieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isS
heafFor`：isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor : (IsSeparatedF
or P R ∧ forall x : FamilyOfElements P R, x.Compatible -> exists t, x…
· 使用定理 `CategoryTheory.Presieve.isSeparatedFor_iff_generate`：isSeparatedFor_iff_
generate : IsSeparatedFor P R ↔ IsSeparatedFor P (generate R : Presieve X)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Presieve.extend_restrict`：extend_restrict {x : FamilyOfEl
ements P (generate R).arrows} (t : x.Compatible) : (x.restrict (le_generate R)).
sieveExtend = x
· 使用定理 `CategoryTheory.Presieve.isAmalgamation_sieveExtend`：isAmalgamation_sieve
Extend {R : Presieve X} (x : FamilyOfElements P R) (t : P.obj (op X)) (ht : x.Is
Amalgamation t) : x.sieveExtend.IsAmalga…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.Compatible.restrict`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒ
ᵖ (Type w)} {X : C}   {R₁ R₂ : CategoryTheory.Pres…
· 使用定理 `CategoryTheory.Presieve.restrict_extend`：restrict_extend {x : FamilyOfEl
ements P R} (t : x.Compatible) : x.sieveExtend.restrict (le_generate R) = x
· 使用定理 `CategoryTheory.Presieve.isAmalgamation_restrict`：isAmalgamation_restrict
 {R₁ R₂ : Presieve X} (h : R₁ <= R₂) (x : FamilyOfElements P R₂) (t : P.obj (op 
X)) (ht : x.IsAmalgamation t) : (x.re…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.Compatible.sieveExtend`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor
 Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve…

--- 原说明 ---
C2.1.3 in [Elephant]
-/
theorem isSheafFor_iff_generate (R : Presieve X) :
    IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X) := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_iff_generate]
  apply and_congr (Iff.refl _)
  constructor
  · intro q x hx
    apply Exists.imp _ (q _ (hx.restrict (le_generate R)))
    intro t ht
    simpa [hx] using isAmalgamation_sieveExtend _ _ ht
  · intro q x hx
    apply Exists.imp _ (q _ hx.sieveExtend)
    intro t ht
    simpa [hx] using isAmalgamation_restrict (le_generate R) _ _ ht

/-- Every presheaf is a sheaf for the family `{𝟙 X}`.

[Elephant] C2.1.5(i)
-/
/-
**CategoryTheory.Presieve.isSheafFor_singleton_iso** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Presieve`。
形式化陈述：isSheafFor_singleton_iso (P : Cᵒᵖ ⥤ Type w) : IsSheafFor P (Presieve.singl
eton (𝟙 X))
参数：P : Cᵒᵖ ⥤ Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.singleton_self`：singleton_self : singleton f f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
Every presheaf is a sheaf for the family `{𝟙 X}`.

[Elephant] C2.1.5(i)
-/
theorem isSheafFor_singleton_iso (P : Cᵒᵖ ⥤ Type w) :
    IsSheafFor P (Presieve.singleton (𝟙 X)) := by
  intro x _
  refine ⟨x _ (Presieve.singleton_self _), ?_, ?_⟩
  · rintro _ _ ⟨rfl, rfl⟩
    simp
  · intro t ht
    simpa using ht _ (Presieve.singleton_self _)

/-- Every presheaf is a sheaf for the maximal sieve.

[Elephant] C2.1.5(ii)
-/
/-
**CategoryTheory.Presieve.isSheafFor_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Presieve`。
形式化陈述：isSheafFor_top (P : Cᵒᵖ ⥤ Type w) : IsSheafFor P (⊤ : Presieve X)
参数：P : Cᵒᵖ ⥤ Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Sieve.arrows_top`：arrows_top : (⊤ : Sieve X).arrows = ⊤
· 使用定理 `CategoryTheory.Sieve.generate_of_singleton_isSplitEpi`：generate_of_singl
eton_isSplitEpi (f : Y ⟶ X) [IsSplitEpi f] : generate (Presieve.singleton f) = ⊤
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
· 使用定理 `CategoryTheory.Presieve.isSheafFor_singleton_iso`：isSheafFor_singleton_i
so (P : Cᵒᵖ ⥤ Type w) : IsSheafFor P (Presieve.singleton (𝟙 X))

--- 原说明 ---
Every presheaf is a sheaf for the maximal sieve.

[Elephant] C2.1.5(ii)
-/
theorem isSheafFor_top (P : Cᵒᵖ ⥤ Type w) : IsSheafFor P (⊤ : Presieve X) := by
  rw [← arrows_top, ← generate_of_singleton_isSplitEpi (𝟙 X)]
  rw [← isSheafFor_iff_generate]
  apply isSheafFor_singleton_iso

@[deprecated (since := "2026-01-22")]
alias isSheafFor_top_sieve := isSheafFor_top

/-- If `P₁ : Cᵒᵖ ⥤ Type w` and `P₂  : Cᵒᵖ ⥤ Type w` are two naturally equivalent
presheaves, and `P₁` is a sheaf for a presieve `R`, then `P₂` is also a sheaf for `R`. -/
/-
**CategoryTheory.Presieve.isSheafFor_of_nat_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Presieve`。
形式化陈述：isSheafFor_of_nat_equiv {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'} (e : fora
ll ⦃X : C⦄, P₁.obj (op X) ≃ P₂.obj (op X)) (he : forall ⦃X Y : C⦄ (f : X ⟶ Y) (x
 : P₁.obj (op Y)), e (P₁.map f.op x) = P₂.map f.op (e x)) {X : C} {R : Presieve 
X} (hP₁ : IsSheafFor P₁ R) : IsSheafFor P₂ R
参数：e : forall ⦃X : C⦄, P₁.obj (op X) ≃ P₂.obj (op X)；he : forall ⦃X Y : C⦄ (f : 
X ⟶ Y) (x : P₁.obj (op Y)), e (P₁.map f.op x) = P₂.map f.op (e x)；hP₁ : IsSheafF
or P₁ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isAmalgamation`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…

--- 原说明 ---
If `P₁ : Cᵒᵖ ⥤ Type w` and `P₂  : Cᵒᵖ ⥤ Type w` are two naturally equivalent
presheaves, and `P₁` is a sheaf for a presieve `R`, then `P₂` is also a sheaf fo
r `R`.
-/
lemma isSheafFor_of_nat_equiv {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
    (e : ∀ ⦃X : C⦄, P₁.obj (op X) ≃ P₂.obj (op X))
    (he : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₁.obj (op Y)),
      e (P₁.map f.op x) = P₂.map f.op (e x))
    {X : C} {R : Presieve X} (hP₁ : IsSheafFor P₁ R) :
    IsSheafFor P₂ R := fun x₂ hx₂ ↦ by
  have he' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₂.obj (op Y)),
    e.symm (P₂.map f.op x) = P₁.map f.op (e.symm x) := fun X Y f x ↦
      e.injective (by simp only [Equiv.apply_symm_apply, he])
  let x₁ : FamilyOfElements P₁ R := fun Y f hf ↦ e.symm (x₂ f hf)
  have hx₁ : x₁.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac ↦ e.injective
    (by simp only [he, Equiv.apply_symm_apply, hx₂ g₁ g₂ h₁ h₂ fac, x₁])
  have : ∀ (t₂ : P₂.obj (op X)),
      x₂.IsAmalgamation t₂ ↔ x₁.IsAmalgamation (e.symm t₂) := fun t₂ ↦ by
    simp only [FamilyOfElements.IsAmalgamation, x₁,
      ← he', EmbeddingLike.apply_eq_iff_eq]
  refine ⟨e (hP₁.amalgamate x₁ hx₁), ?_, ?_⟩
  · dsimp
    simp only [this, Equiv.symm_apply_apply]
    exact IsSheafFor.isAmalgamation hP₁ hx₁
  · intro t₂ ht₂
    refine e.symm.injective ?_
    simp only [Equiv.symm_apply_apply]
    exact hP₁.isSeparatedFor x₁ _ _ (by simpa only [this] using ht₂)
      (IsSheafFor.isAmalgamation hP₁ hx₁)
/-
**CategoryTheory.Presieve.isSheafFor_iff_of_nat_equiv** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Presieve`。
形式化陈述：isSheafFor_iff_of_nat_equiv {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'} (e : 
forall ⦃X : C⦄, P₁.obj (op X) ≃ P₂.obj (op X)) (he : forall ⦃X Y : C⦄ (f : X ⟶ Y
) (x : P₁.obj (op Y)), e (P₁.map f.op x) = P₂.map f.op (e x)) {X : C} {R : Presi
eve X} : IsSheafFor P₁ R ↔ IsSheafFor P₂ R
参数：e : forall ⦃X : C⦄, P₁.obj (op X) ≃ P₂.obj (op X)；he : forall ⦃X Y : C⦄ (f : 
X ⟶ Y) (x : P₁.obj (op Y)), e (P₁.map f.op x) = P₂.map f.op (e x)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presieve.isSheafFor_of_nat_equiv`：isSheafFor_of_nat_equiv
 {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'} (e : forall ⦃X : C⦄, P₁.obj (op X) ≃ P
₂.obj (op X)) (he : forall ⦃X Y : C⦄ …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isSheafFor_iff_of_nat_equiv {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
    (e : ∀ ⦃X : C⦄, P₁.obj (op X) ≃ P₂.obj (op X))
    (he : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₁.obj (op Y)),
      e (P₁.map f.op x) = P₂.map f.op (e x))
    {X : C} {R : Presieve X} :
    IsSheafFor P₁ R ↔ IsSheafFor P₂ R := by
  refine ⟨fun h ↦ isSheafFor_of_nat_equiv _ he h,
      fun h ↦ isSheafFor_of_nat_equiv (fun _ ↦ (@e _).symm) ?_ h⟩
  intro X Y f x
  obtain ⟨y, rfl⟩ := e.surjective x
  refine e.injective ?_
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, he]

/-- If `P` is a sheaf for `S`, and it is iso to `P'`, then `P'` is a sheaf for `S`. This shows that
"being a sheaf for a presieve" is a mathematical or hygienic property.
-/
/-
**CategoryTheory.Presieve.isSheafFor_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Presieve`。
形式化陈述：isSheafFor_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSheafFor P R) : Is
SheafFor P' R
参数：i : P ≅ P'；hP : IsSheafFor P R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presieve.isSheafFor_of_nat_equiv`：isSheafFor_of_nat_equiv
 {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'} (e : forall ⦃X : C⦄, P₁.obj (op X) ≃ P
₂.obj (op X)) (he : forall ⦃X Y : C⦄ …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
If `P` is a sheaf for `S`, and it is iso to `P'`, then `P'` is a sheaf for `S`. 
This shows that
"being a sheaf for a presieve" is a mathematical or hygienic property.
-/
theorem isSheafFor_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSheafFor P R) :
    IsSheafFor P' R :=
  isSheafFor_of_nat_equiv (fun X ↦ (i.app (op X)).toEquiv)
    (fun _ _ f x ↦ ConcreteCategory.congr_hom (i.hom.naturality f.op) x) hP
/-
**CategoryTheory.Presieve.isSheafFor_iff_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Presieve`。
形式化陈述：isSheafFor_iff_of_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') : IsSheafFor P R ↔ 
IsSheafFor P' R
参数：i : P ≅ P'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iso`：isSheafFor_iso {P' : Cᵒᵖ ⥤ Type 
w} (i : P ≅ P') (hP : IsSheafFor P R) : IsSheafFor P' R
-/
theorem isSheafFor_iff_of_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') :
    IsSheafFor P R ↔ IsSheafFor P' R :=
  ⟨isSheafFor_iso i, isSheafFor_iso i.symm⟩

/-- The property of being separated for some presieve is preserved under isomorphisms. -/
/-
**CategoryTheory.Presieve.isSeparatedFor_iso** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Presieve`。
形式化陈述：isSeparatedFor_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSeparatedFor P
 R) : IsSeparatedFor P' R
参数：i : P ≅ P'；hP : IsSeparatedFor P R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_apply`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation.map`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : CategoryTheory.Functor C
ᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presie…

--- 原说明 ---
The property of being separated for some presieve is preserved under isomorphism
s.
-/
theorem isSeparatedFor_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSeparatedFor P R) :
    IsSeparatedFor P' R := by
  intro x t₁ t₂ ht₁ ht₂
  simpa using congrArg (i.hom.app _) <| hP (x.map i.inv) _ _ (ht₁.map i.inv) (ht₂.map i.inv)
/-
**CategoryTheory.Presieve.IsSeparatedFor.of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Presieve.IsSeparatedFor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : Categor
yTheory.Functor Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve X} (f : P ⟶
 Q) [CategoryTheory.Mono f],   CategoryTheory.Presieve.IsSeparatedFor Q R → Cate
goryTheory.Presieve.IsSeparatedFor P R
参数：Type w；f : P ⟶ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.injective_of_mono`：injective_of_mono {X Y : Type u} (f : 
X ⟶ Y) [hf : Mono f] : Function.Injective f
· 使用定理 `CategoryTheory.instMonoAppOfFunctor`：∀ {K : Type u} [inst : CategoryTheo
ry.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C
]   {F G : CategoryTheory…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation.map`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : CategoryTheory.Functor C
ᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presie…
-/
lemma IsSeparatedFor.of_mono (f : P ⟶ Q) [Mono f] (h : R.IsSeparatedFor Q) :
    R.IsSeparatedFor P := by
  intro x t₁ t₂ ht₁ ht₂
  exact injective_of_mono _ <|  h (x.map f) _ _ (ht₁.map f) (ht₂.map f)

set_option backward.isDefEq.respectTransparency.types false in
/-- If a presieve `R` on `X` has a subsieve `S` such that:

* `P` is a sheaf for `S`.
* For every `f` in `R`, `P` is separated for the pullback of `S` along `f`,

then `P` is a sheaf for `R`.

This is closely related to [Elephant] C2.1.6(i).
-/
/-
**CategoryTheory.Presieve.isSheafFor_subsieve_aux** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Presieve`。
形式化陈述：isSheafFor_subsieve_aux (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X} 
(h : (S : Presieve X) <= R) (hS : IsSheafFor P (S : Presieve X)) (trans : forall
 ⦃Y⦄ ⦃f : Y ⟶ X⦄, R f -> IsSeparatedFor P (S.pullback f : Presieve Y)) : IsSheaf
For P R
参数：P : Cᵒᵖ ⥤ Type w；h : (S : Presieve X) <= R；hS : IsSheafFor P (S : Presieve X)
；trans : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, R f -> IsSeparatedFor P (S.pullback f : Presiev
e Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isS
heafFor`：isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor : (IsSeparatedF
or P R ∧ forall x : FamilyOfElements P R, x.Compatible -> exists t, x…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.isAmalgamation_restrict`：isAmalgamation_restrict
 {R₁ R₂ : Presieve X} (h : R₁ <= R₂) (x : FamilyOfElements P R₂) (t : P.obj (op 
X)) (ht : x.IsAmalgamation t) : (x.re…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.Compatible.restrict`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒ
ᵖ (Type w)} {X : C}   {R₁ R₂ : CategoryTheory.Pres…
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.valid_glue`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
Y : C}   {R : CategoryTheory.Presie…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.restrict.eq_1`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Typ
e w)} {X : C}   {R₁ R₂ : CategoryTheory.Pres…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a presieve `R` on `X` has a subsieve `S` such that:

* `P` is a sheaf for `S`.
* For every `f` in `R`, `P` is separated for the pullback of `S` along `f`,

then `P` is a sheaf for `R`.

This is closely related to [Elephant] C2.1.6(i).
-/
theorem isSheafFor_subsieve_aux (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
    (h : (S : Presieve X) ≤ R) (hS : IsSheafFor P (S : Presieve X))
    (trans : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, R f → IsSeparatedFor P (S.pullback f : Presieve Y)) :
    IsSheafFor P R := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  constructor
  · intro x t₁ t₂ ht₁ ht₂
    exact
      hS.isSeparatedFor _ _ _ (isAmalgamation_restrict h x t₁ ht₁)
        (isAmalgamation_restrict h x t₂ ht₂)
  · intro x hx
    use hS.amalgamate _ (hx.restrict h)
    intro W j hj
    apply (trans hj).ext
    intro Y f hf
    rw [← comp_apply, ← Functor.map_comp, ← op_comp, hS.valid_glue (hx.restrict h) _ hf,
      FamilyOfElements.restrict, ← hx (𝟙 _) f (h _ _ hf) _ (id_comp _)]
    simp

/--
If `P` is a sheaf for every pullback of the sieve `S`, then `P` is a sheaf for any presieve which
contains `S`.
This is closely related to [Elephant] C2.1.6.
-/
/-
**CategoryTheory.Presieve.isSheafFor_subsieve** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Presieve`。
形式化陈述：isSheafFor_subsieve (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X} (h :
 (S : Presieve X) <= R) (trans : forall ⦃Y⦄ (f : Y ⟶ X), IsSheafFor P (S.pullbac
k f : Presieve Y)) : IsSheafFor P R
参数：P : Cᵒᵖ ⥤ Type w；h : (S : Presieve X) <= R；trans : forall ⦃Y⦄ (f : Y ⟶ X), Is
SheafFor P (S.pullback f : Presieve Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.isSheafFor_subsieve_aux`：isSheafFor_subsieve_aux
 (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X} (h : (S : Presieve X) <= R) (
hS : IsSheafFor P (S : Presieve X)) (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_id`：pullback_id : S.pullback (𝟙 _) = S
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…

--- 原说明 ---
If `P` is a sheaf for every pullback of the sieve `S`, then `P` is a sheaf for a
ny presieve which
contains `S`.
This is closely related to [Elephant] C2.1.6.
-/
theorem isSheafFor_subsieve (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
    (h : (S : Presieve X) ≤ R) (trans : ∀ ⦃Y⦄ (f : Y ⟶ X),
      IsSheafFor P (S.pullback f : Presieve Y)) :
    IsSheafFor P R :=
  isSheafFor_subsieve_aux P h (by simpa using trans (𝟙 _)) fun _ f _ => (trans f).isSeparatedFor

section Arrows

variable {B : C} {I : Type*} {X : I → C} (π : (i : I) → X i ⟶ B) (P)

/--
A more explicit version of `FamilyOfElements.Compatible` for a `Presieve.ofArrows`.
-/
/-
**CategoryTheory.Presieve.Arrows.Compatible** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Presieve.Arrows`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (P : C
ategoryTheory.Functor Cᵒᵖ (Type w)) →       {B : C} → {I : Type u_1} → {X : I → 
C} → ((i : I) → X i ⟶ B) → ((i : I) → P.obj (Opposite.op (X i))) → Prop
参数：P : CategoryTheory.Functor Cᵒᵖ (Type w)；(i : I) → X i ⟶ B；(i : I) → P.obj (Op
posite.op (X i))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A more explicit version of `FamilyOfElements.Compatible` for a `Presieve.ofArrow
s`.
-/
def Arrows.Compatible (x : (i : I) → P.obj (op (X i))) : Prop :=
  ∀ i j Z (gi : Z ⟶ X i) (gj : Z ⟶ X j), gi ≫ π i = gj ≫ π j →
    P.map gi.op (x i) = P.map gj.op (x j)
/-
**CategoryTheory.Presieve.FamilyOfElements.isAmalgamation_iff_ofArrows** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (P : CategoryT
heory.Functor Cᵒᵖ (Type w)) {B : C}   {I : Type u_1} {X : I → C} (π : (i : I) → 
X i ⟶ B)   (x : CategoryTheory.Presieve.FamilyOfElements P (CategoryTheory.Presi
eve.ofArrows X π)) (t : P.obj (Opposite.op B)),   x.IsAmalgamation t ↔ ∀ (i : I)
, (CategoryTheory.ConcreteCategory.hom (P.map (π i).op)) t = x (π i) ⋯
参数：P : CategoryTheory.Functor Cᵒᵖ (Type w)；π : (i : I) → X i ⟶ B；x : CategoryThe
ory.Presieve.FamilyOfElements P (CategoryTheory.Presieve.ofArrows X π)；t : P.obj
 (Opposite.op B)；i : I；CategoryTheory.ConcreteCategory.hom (P.map (π i).op)；π i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FamilyOfElements.isAmalgamation_iff_ofArrows (x : FamilyOfElements P (ofArrows X π))
    (t : P.obj (op B)) :
    x.IsAmalgamation t ↔ ∀ (i : I), P.map (π i).op t = x _ (ofArrows.mk i) :=
  ⟨fun h i ↦ h _ (ofArrows.mk i), fun h _ f ⟨i⟩ ↦ h i⟩

namespace Arrows.Compatible

variable {x : (i : I) → P.obj (op (X i))}
variable {P π}

/-
**CategoryTheory.Presieve.Arrows.Compatible.exists_familyOfElements** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Presieve.Arrows.Compatible`。
形式化陈述：exists_familyOfElements (hx : Compatible P π x) : exists (x' : FamilyOfEle
ments P (ofArrows X π)), forall (i : I), x' _ (ofArrows.mk i) = x i
参数：hx : Compatible P π x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.Presieve.ofArrows_surj`：ofArrows_surj {ι : Type*} {Y : ι 
-> C} (f : forall i, Y i ⟶ X) {Z : C} (g : Z ⟶ X) (hg : ofArrows Y f g) : exists
 (i : ι) (h : Y i = Z), g =…
-/
theorem exists_familyOfElements (hx : Compatible P π x) :
    ∃ (x' : FamilyOfElements P (ofArrows X π)), ∀ (i : I), x' _ (ofArrows.mk i) = x i := by
  choose i h h' using @ofArrows_surj _ _ _ _ _ π
  exact ⟨fun Y f hf ↦ P.map (eqToHom (h f hf).symm).op (x _),
    fun j ↦ (hx _ j (X j) _ (𝟙 _) <| by rw [← h', id_comp]).trans <| by simp⟩

variable (hx : Compatible P π x)

/--
A `FamilyOfElements` associated to an explicit family of elements.
-/
noncomputable
/-
**CategoryTheory.Presieve.Arrows.Compatible.familyOfElements** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Presieve.Arrows.Compatible`。
形式化陈述：familyOfElements : FamilyOfElements P (ofArrows X π)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.Arrows.Compatible.exists_familyOfElements`：exist
s_familyOfElements (hx : Compatible P π x) : exists (x' : FamilyOfElements P (of
Arrows X π)), forall (i : I), x' _ (ofArrows.mk i) = x …
-/
def familyOfElements : FamilyOfElements P (ofArrows X π) :=
  (exists_familyOfElements hx).choose

@[simp]
/-
**CategoryTheory.Presieve.Arrows.Compatible.familyOfElements_ofArrows_mk** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Presieve.Arrows.Compatible`。
形式化陈述：familyOfElements_ofArrows_mk (i : I) : hx.familyOfElements _ (ofArrows.mk 
i) = x i
参数：i : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.Presieve.Arrows.Compatible.exists_familyOfElements`：exist
s_familyOfElements (hx : Compatible P π x) : exists (x' : FamilyOfElements P (of
Arrows X π)), forall (i : I), x' _ (ofArrows.mk i) = x …
-/
theorem familyOfElements_ofArrows_mk (i : I) :
    hx.familyOfElements _ (ofArrows.mk i) = x i :=
  (exists_familyOfElements hx).choose_spec _
/-
**CategoryTheory.Presieve.Arrows.Compatible.familyOfElements_compatible** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Presieve.Arrows.Compatible`。
形式化陈述：familyOfElements_compatible : hx.familyOfElements.Compatible
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.Arrows.Compatible.familyOfElements_ofArrows_mk`：
familyOfElements_ofArrows_mk (i : I) : hx.familyOfElements _ (ofArrows.mk i) = x
 i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem familyOfElements_compatible : hx.familyOfElements.Compatible := by
  rintro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i⟩ ⟨j⟩ hgf
  simp [hx i j Z g₁ g₂ hgf]

end Arrows.Compatible

/-
**CategoryTheory.Presieve.isSheafFor_arrows_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Presieve`。
形式化陈述：isSheafFor_arrows_iff : (ofArrows X π).IsSheafFor P ↔ (forall (x : (i : I)
 -> P.obj (op (X i))), Arrows.Compatible P π x -> exists! t, forall i, P.map (π 
i).op t = x i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.Arrows.Compatible.familyOfElements_compatible`：f
amilyOfElements_compatible : hx.familyOfElements.Compatible
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.Arrows.Compatible.familyOfElements_ofArrows_mk`：
familyOfElements_ofArrows_mk (i : I) : hx.familyOfElements _ (ofArrows.mk i) = x
 i
-/
theorem isSheafFor_arrows_iff : (ofArrows X π).IsSheafFor P ↔
    (∀ (x : (i : I) → P.obj (op (X i))), Arrows.Compatible P π x →
    ∃! t, ∀ i, P.map (π i).op t = x i) := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨t, ht₁, ht₂⟩ := h _ hx.familyOfElements_compatible
    refine ⟨t, fun i ↦ ?_, fun t' ht' ↦ ht₂ _ fun _ _ ⟨i⟩ ↦ ?_⟩
    · rw [ht₁ _ (ofArrows.mk i), hx.familyOfElements_ofArrows_mk]
    · rw [ht', hx.familyOfElements_ofArrows_mk]
  · obtain ⟨t, hA, ht⟩ := h (fun i ↦ x (π i) (ofArrows.mk _))
      (fun i j Z gi gj ↦ hx gi gj (ofArrows.mk _) (ofArrows.mk _))
    exact ⟨t, fun Y f ⟨i⟩ ↦ hA i, fun y hy ↦ ht y (fun i ↦ hy (π i) (ofArrows.mk _))⟩

/-- If `P` is a presheaf of types and `π : (i : I) → X i ⟶ B` is a family
of morphisms, this is the map from `P.obj (op B)` to the subtype of compatible
families in `P.obj (op (X i))`. -/
@[simps]
/-
**CategoryTheory.Presieve.Arrows.toCompatible** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Presieve.Arrows`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (P : C
ategoryTheory.Functor Cᵒᵖ (Type w)) →       {B : C} →         {I : Type u_1} →  
         {X : I → C} →             (π : (i : I) → X i ⟶ B) → P.obj (Opposite.op 
B) → Subtype (CategoryTheory.Presieve.Arrows.Compatible P π)
参数：P : CategoryTheory.Functor Cᵒᵖ (Type w)；π : (i : I) → X i ⟶ B；Opposite.op B；C
ategoryTheory.Presieve.Arrows.Compatible P π。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is a presheaf of types and `π : (i : I) → X i ⟶ B` is a family
of morphisms, this is the map from `P.obj (op B)` to the subtype of compatible
families in `P.obj (op (X i))`.
-/
def Arrows.toCompatible (s : P.obj (op B)) :
    Subtype (Arrows.Compatible P π) where
  val i := P.map (π i).op s
  property i j Z gi gj h := by
    simp [← comp_apply, ← Functor.map_comp, ← op_comp, h]
/-
**CategoryTheory.Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：isSheafFor_ofArrows_iff_bijective_toCompabible : IsSheafFor P (ofArrows X 
π) ↔ Function.Bijective (Arrows.toCompatible P π)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.isSheafFor_arrows_iff`：isSheafFor_arrows_iff : (
ofArrows X π).IsSheafFor P ↔ (forall (x : (i : I) -> P.obj (op (X i))), Arrows.C
ompatible P π x -> exists! t, foral…
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem isSheafFor_ofArrows_iff_bijective_toCompabible :
    IsSheafFor P (ofArrows X π) ↔
      Function.Bijective (Arrows.toCompatible P π) := by
  rw [isSheafFor_arrows_iff]
  refine ⟨fun h ↦ ⟨fun x₁ x₂ hx ↦
      (h _ (Arrows.toCompatible P π x₁).property).unique (fun _ ↦ rfl)
        (congr_fun (congr_arg Subtype.val hx.symm)),
      fun ⟨y, hy⟩ ↦ ?_⟩, fun h x hx ↦ ?_⟩
  · obtain ⟨x, hx, _⟩ := h y hy
    exact ⟨x, by ext; apply hx⟩
  · obtain ⟨y, hy⟩ := h.2 ⟨x, hx⟩
    rw [Subtype.ext_iff] at hy
    dsimp at hy
    subst hy
    exact ⟨y, fun _ ↦ rfl, fun y' hy' ↦ h.1 (by ext; apply hy')⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Presieve.isSheafFor_pullback_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Presieve`。
形式化陈述：isSheafFor_pullback_iff (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Sieve X) {Y : C} (
f : Y ⟶ X) [IsIso f] : IsSheafFor P (Sieve.pullback f R).arrows ↔ IsSheafFor P R
.arrows
参数：P : Cᵒᵖ ⥤ Type w；R : Sieve X；f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Sieve.exists_eq_ofArrows`：exists_eq_ofArrows (R : Sieve X
) : exists (I : Type max u₁ v₁) (Y : I -> C) (f : forall i, Y i ⟶ X), R = Sieve.
ofArrows _ f
· 使用引理 `CategoryTheory.Sieve.pullback_ofArrows_of_iso`：pullback_ofArrows_of_iso 
{I : Type*} {X : C} (Z : I -> C) (f : forall i, Z i ⟶ X) {X' : C} (e : X' ≅ X) :
 pullback e.hom (Sieve.ofArrows _ f…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Presieve.Arrows.toCompatible_coe`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (P : CategoryTheory.Functor Cᵒᵖ (Type w)) {
B : C}   {I : Type u_1} {X : I → C} (…
· 使用定理 `CategoryTheory.Iso.toEquiv_apply`：∀ {X Y : Type u} (i : X ≅ Y) (a : X), 
i.toEquiv a = (CategoryTheory.ConcreteCategory.hom i.hom) a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Iso.op_inv`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.inv = α.inv.op
· 使用定理 `CategoryTheory.op_inv`：op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).
op = inv f.op
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 34 条，此处仅展示前 30 条）
-/
lemma isSheafFor_pullback_iff (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Sieve X)
    {Y : C} (f : Y ⟶ X) [IsIso f] :
    IsSheafFor P (Sieve.pullback f R).arrows ↔ IsSheafFor P R.arrows := by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  have := Sieve.pullback_ofArrows_of_iso _ g (asIso f)
  dsimp at this
  let e : Subtype (Arrows.Compatible P g) ≃
    Subtype (Arrows.Compatible P (fun i ↦ g i ≫ inv f)) :=
    { toFun s := ⟨fun i ↦ s.val i, fun i₁ i₂ W g₁ g₂ h ↦ by
        simp only [← cancel_mono f, assoc, IsIso.inv_hom_id, comp_id] at h
        exact s.property _ _ _ _ _ h⟩
      invFun s := ⟨fun i ↦ s.val i, fun i₁ i₂ W g₁ g₂ h ↦ by
        replace h := h =≫ inv f
        simp only [Category.assoc] at h
        exact s.property _ _ _ _ _ h⟩ }
  simp only [this, ← isSheafFor_iff_generate,
    isSheafFor_ofArrows_iff_bijective_toCompabible, ← e.bijective.of_comp_iff',
    ← Function.Bijective.of_comp_iff _ (P.mapIso (asIso f).symm.op).toEquiv.bijective]
  convert! Iff.rfl using 2
  ext
  simp [e]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presieve.isSheafFor_over_map_op_comp_ofArrows_iff** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：isSheafFor_over_map_op_comp_ofArrows_iff {B B' : C} (p : B ⟶ B') (P : (Ove
r B')ᵒᵖ ⥤ Type w) {X : Over B} {Y : I -> Over B} (f : forall i, Y i ⟶ X) : IsShe
afFor ((Over.map p).op ⋙ P) (Presieve.ofArrows _ f) ↔ IsSheafFor P (Presieve.ofA
rrows _ (fun i => (Over.map p).map (f i)))
参数：p : B ⟶ B'；P : (Over B')ᵒᵖ ⥤ Type w；f : forall i, Y i ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isSheafFor_over_map_op_comp_ofArrows_iff
    {B B' : C} (p : B ⟶ B') (P : (Over B')ᵒᵖ ⥤ Type w)
    {X : Over B} {Y : I → Over B} (f : ∀ i, Y i ⟶ X) :
    IsSheafFor ((Over.map p).op ⋙ P) (Presieve.ofArrows _ f) ↔
      IsSheafFor P (Presieve.ofArrows _ (fun i ↦ (Over.map p).map (f i))) := by
  let e : Subtype (Arrows.Compatible ((Over.map p).op ⋙ P) f) ≃
      Subtype (Arrows.Compatible P (fun i ↦ (Over.map p).map (f i))) :=
    { toFun s := ⟨fun i ↦ s.val i, fun i₁ i₂ Z g₁ g₂ h ↦ by
        replace h := (Over.forget _).congr_map h
        dsimp at h
        have := s.property i₁ i₂ (Over.mk (g₁.left ≫ (f i₁).left ≫ X.hom))
          (Over.homMk g₁.left) (Over.homMk g₂.left (by
            have := Over.w (f i₂)
            dsimp at this ⊢
            rw [reassoc_of% h, this])) (by cat_disch)
        let φ : Z ⟶ (Over.map p).obj (Over.mk (g₁.left ≫ (f i₁).left ≫ X.hom)) :=
          Over.homMk (𝟙 _) (by simpa using Over.w g₁)
        replace this := congr_arg (P.map φ.op) this
        dsimp at this
        simp only [← comp_apply, ← Functor.map_comp, ← op_comp] at this
        convert! this <;> cat_disch⟩
      invFun s := ⟨fun i ↦ s.val i, fun i₁ i₂ Z g₁ g₂ h ↦
        s.property i₁ i₂ _ ((Over.map p).map g₁) ((Over.map p).map g₂)
          (by simp only [← Functor.map_comp, h])⟩ }
  simp only [isSheafFor_ofArrows_iff_bijective_toCompabible,
    ← e.bijective.of_comp_iff']
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Presieve.isSheafFor_over_map_op_comp_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Presieve`。
形式化陈述：isSheafFor_over_map_op_comp_iff {B B' : C} (p : B ⟶ B') (P : (Over B')ᵒᵖ ⥤
 Type w) {X : Over B} (R : Sieve X) {X' : Over B'} (e : (Over.map p).obj X ≅ X')
 : IsSheafFor ((Over.map p).op ⋙ P) R.arrows ↔ IsSheafFor P (Sieve.pullback e.in
v (Sieve.functorPushforward (Over.map p) R)).arrows
参数：p : B ⟶ B'；P : (Over B')ᵒᵖ ⥤ Type w；R : Sieve X；e : (Over.map p).obj X ≅ X'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Sieve.exists_eq_ofArrows`：exists_eq_ofArrows (R : Sieve X
) : exists (I : Type max u₁ v₁) (Y : I -> C) (f : forall i, Y i ⟶ X), R = Sieve.
ofArrows _ f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
· 使用引理 `CategoryTheory.Presieve.isSheafFor_pullback_iff`：isSheafFor_pullback_iff
 (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Sieve X) {Y : C} (f : Y ⟶ X) [IsIso f] : IsShea
fFor P (Sieve.pullback f R).arrows ↔ …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `CategoryTheory.Presieve.isSheafFor_over_map_op_comp_ofArrows_iff`：isShea
fFor_over_map_op_comp_ofArrows_iff {B B' : C} (p : B ⟶ B') (P : (Over B')ᵒᵖ ⥤ Ty
pe w) {X : Over B} {Y : I -> Over B} (f : forall i, Y …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Over.w_assoc`：∀ {T : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Over X} (φ : f ⟶ g) {Z : T}   (h 
: X ⟶ Z),   Categ…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Sieve.ofArrows_mk`：ofArrows_mk (i : I) : ofArrows Y f (f 
i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isSheafFor_over_map_op_comp_iff
    {B B' : C} (p : B ⟶ B') (P : (Over B')ᵒᵖ ⥤ Type w)
    {X : Over B} (R : Sieve X) {X' : Over B'}
    (e : (Over.map p).obj X ≅ X') :
    IsSheafFor ((Over.map p).op ⋙ P) R.arrows ↔
      IsSheafFor P (Sieve.pullback e.inv (Sieve.functorPushforward (Over.map p) R)).arrows := by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  rw [← isSheafFor_iff_generate, isSheafFor_pullback_iff,
    isSheafFor_over_map_op_comp_ofArrows_iff, isSheafFor_iff_generate]
  convert! Iff.rfl
  refine le_antisymm ?_ ?_
  · rintro W _ ⟨T, _, a, ⟨_, b, _, ⟨i⟩, rfl⟩, rfl⟩
    refine ⟨(Over.map p).obj (Z i), Over.homMk (a.left ≫ b.left) ?_, _, ⟨i⟩, ?_⟩
    · simpa [(Over.w_assoc b)] using Over.w a
    · cat_disch
  · rintro W _ ⟨_, a, _, ⟨i⟩, rfl⟩
    exact ⟨_, _, _, Sieve.ofArrows_mk _ _ i, rfl⟩

variable [(ofArrows X π).HasPairwisePullbacks]

/--
A more explicit version of `FamilyOfElements.PullbackCompatible` for a `Presieve.ofArrows`.
-/
/-
**CategoryTheory.Presieve.Arrows.PullbackCompatible** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Presieve.Arrows`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (P : C
ategoryTheory.Functor Cᵒᵖ (Type w)) →       {B : C} →         {I : Type u_1} →  
         {X : I → C} →             (π : (i : I) → X i ⟶ B) →               [(Cat
egoryTheory.Presieve.ofArrows X π).HasPairwisePullbacks] →                 ((i :
 I) → P.obj (Opposite.op (X i))) → Prop
参数：P : CategoryTheory.Functor Cᵒᵖ (Type w)；π : (i : I) → X i ⟶ B；CategoryTheory.
Presieve.ofArrows X π；(i : I) → P.obj (Opposite.op (X i))。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…

--- 原说明 ---
A more explicit version of `FamilyOfElements.PullbackCompatible` for a `Presieve
.ofArrows`.
-/
def Arrows.PullbackCompatible (x : (i : I) → P.obj (op (X i))) : Prop :=
  ∀ i j, P.map (pullback.fst (π i) (π j)).op (x i) =
    P.map (pullback.snd (π i) (π j)).op (x j)
/-
**CategoryTheory.Presieve.Arrows.pullbackCompatible_iff** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Presieve.Arrows`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (P : CategoryT
heory.Functor Cᵒᵖ (Type w)) {B : C}   {I : Type u_1} {X : I → C} (π : (i : I) → 
X i ⟶ B)   [inst_1 : (CategoryTheory.Presieve.ofArrows X π).HasPairwisePullbacks
] (x : (i : I) → P.obj (Opposite.op (X i))),   CategoryTheory.Presieve.Arrows.Co
mpatible P π x ↔ CategoryTheory.Presieve.Arrows.PullbackCompatible P π x
参数：P : CategoryTheory.Functor Cᵒᵖ (Type w)；π : (i : I) → X i ⟶ B；CategoryTheory.
Presieve.ofArrows X π；x : (i : I) → P.obj (Opposite.op (X i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem Arrows.pullbackCompatible_iff (x : (i : I) → P.obj (op (X i))) :
    Compatible P π x ↔ PullbackCompatible P π x := by
  refine ⟨fun t i j ↦ ?_, fun t i j Z gi gj comm ↦ ?_⟩
  · apply t
    exact pullback.condition
  · rw [← pullback.lift_fst _ _ comm, op_comp, Functor.map_comp, comp_apply, t i j,
      ← comp_apply, ← Functor.map_comp, ← op_comp, pullback.lift_snd]
/-
**CategoryTheory.Presieve.isSheafFor_arrows_iff_pullbacks** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Presieve`。
形式化陈述：isSheafFor_arrows_iff_pullbacks : (ofArrows X π).IsSheafFor P ↔ (forall (x
 : (i : I) -> P.obj (op (X i))), Arrows.PullbackCompatible P π x -> exists! t, f
orall i, P.map (π i).op t = x i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSheafFor_arrows_iff_pullbacks : (ofArrows X π).IsSheafFor P ↔
    (∀ (x : (i : I) → P.obj (op (X i))), Arrows.PullbackCompatible P π x →
    ∃! t, ∀ i, P.map (π i).op t = x i) := by
  simp_rw [← Arrows.pullbackCompatible_iff, isSheafFor_arrows_iff]

end Arrows

@[simp]
/-
**CategoryTheory.Presieve.isSeparatedFor_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Presieve`。
形式化陈述：isSeparatedFor_singleton {X Y : C} {f : X ⟶ Y} : Presieve.IsSeparatedFor P
 (.singleton f) ↔ Function.Injective (P.map f.op)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.eq_1`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X : C} (P : CategoryTheory.Functor Cᵒᵖ (Type w
))   (R : CategoryTheory.Presieve…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.singletonEquiv_symm_apply_self`
：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory
.Functor Cᵒᵖ (Type w)} {X Y : C}   (f : X ⟶ Y) (x : P.obj (Op…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma isSeparatedFor_singleton {X Y : C} {f : X ⟶ Y} :
    Presieve.IsSeparatedFor P (.singleton f) ↔
      Function.Injective (P.map f.op) := by
  rw [IsSeparatedFor, Equiv.forall_congr_left (Presieve.FamilyOfElements.singletonEquiv P f)]
  simp_rw [FamilyOfElements.isAmalgamation_singleton_iff,
    FamilyOfElements.singletonEquiv_symm_apply_self, Function.Injective]
  aesop
/-
**CategoryTheory.Presieve.isSheafFor_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Presieve`。
形式化陈述：isSheafFor_singleton {X Y : C} {f : X ⟶ Y} : Presieve.IsSheafFor P (.singl
eton f) ↔ forall (x : P.obj (op X)), (forall {Z : C} (p₁ p₂ : Z ⟶ X), p₁ ≫ f = p
₂ ≫ f -> P.map p₁.op x = P.map p₂.op x) -> exists! y, P.map f.op y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.eq_1`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X : C} (P : CategoryTheory.Functor Cᵒᵖ (Type w))  
 (R : CategoryTheory.Presieve…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.singletonEquiv_symm_apply_self`
：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory
.Functor Cᵒᵖ (Type w)} {X Y : C}   (f : X ⟶ Y) (x : P.obj (Op…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSheafFor_singleton {X Y : C} {f : X ⟶ Y} :
    Presieve.IsSheafFor P (.singleton f) ↔
      ∀ (x : P.obj (op X)),
        (∀ {Z : C} (p₁ p₂ : Z ⟶ X), p₁ ≫ f = p₂ ≫ f → P.map p₁.op x = P.map p₂.op x) →
        ∃! y, P.map f.op y = x := by
  rw [IsSheafFor, Equiv.forall_congr_left (Presieve.FamilyOfElements.singletonEquiv P f)]
  simp_rw [FamilyOfElements.compatible_singleton_iff,
    FamilyOfElements.isAmalgamation_singleton_iff, FamilyOfElements.singletonEquiv_symm_apply_self]

/--
To show `P` is a sheaf for the binding of `U` with `B`, it suffices to show that `P` is a sheaf for
`U`, that `P` is a sheaf for each sieve in `B`, and that it is separated for any pullback of any
sieve in `B`.

This is mostly an auxiliary lemma to show `Presieve.isSheafFor_trans`.
Adapted from [Elephant], Lemma C2.1.7(i) with suggestions as mentioned in
https://math.stackexchange.com/a/358709/
-/
/-
**CategoryTheory.Presieve.isSheafFor_bind** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Presieve`。
形式化陈述：isSheafFor_bind (P : Cᵒᵖ ⥤ Type*) (U : Sieve X) (B : forall ⦃Y⦄ ⦃f : Y ⟶ X
⦄, U f -> Sieve Y) (hU : Presieve.IsSheafFor P (U : Presieve X)) (hB : forall ⦃Y
⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.IsSheafFor P (B hf : Presieve Y)) (hB' : fora
ll ⦃Y⦄ ⦃f : Y ⟶ X⦄ (h : U f) ⦃Z⦄ (g : Z ⟶ Y), Presieve.IsSeparatedFor P (((B h).
pullback g) : Presieve Z)) : Presieve.IsSheafFor P (Sieve.bind (U : Presieve X) 
B : Presieve X)
参数：P : Cᵒᵖ ⥤ Type*；U : Sieve X；B : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f -> Sieve Y；hU : P
resieve.IsSheafFor P (U : Presieve X)；hB : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Pr
esieve.IsSheafFor P (B hf : Presieve Y)；hB' : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (h : U f) ⦃
Z⦄ (g : Z ⟶ Y), Presieve.IsSeparatedFor P (((B h).pullback g) : Presieve Z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.bind_comp`：bind_comp {S : Presieve X} {R : foral
l ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y} {g : Z ⟶ Y} (h₁ : S f) (h₂ : R h₁ g) :
 bind S R (g ≫ f)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isAmalgamation`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.compatible_iff_sieveCompatible`：compatible_iff_s
ieveCompatible (x : FamilyOfElements P (S : Presieve X)) : x.Compatible ↔ x.Siev
eCompatible
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Sieve.bind_apply`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X : C} (S : CategoryTheory.Presieve X)   (R : ⦃Y : C⦄ → ⦃f
 : Y ⟶ X⦄ → S f → Cat…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.valid_glue`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
Y : C}   {R : CategoryTheory.Presie…

--- 原说明 ---
To show `P` is a sheaf for the binding of `U` with `B`, it suffices to show that
 `P` is a sheaf for
`U`, that `P` is a sheaf for each sieve in `B`, and that it is separated for any
 pullback of any
sieve in `B`.

This is mostly an auxiliary lemma to show `Presieve.isSheafFor_trans`.
Adapted from [Elephant], Lemma C2.1.7(i) with suggestions as mentioned in
https://math.stackexchange.com/a/358709/
-/
theorem isSheafFor_bind (P : Cᵒᵖ ⥤ Type*) (U : Sieve X)
    (B : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f → Sieve Y)
    (hU : Presieve.IsSheafFor P (U : Presieve X))
    (hB : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.IsSheafFor P (B hf : Presieve Y))
    (hB' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (h : U f) ⦃Z⦄ (g : Z ⟶ Y),
      Presieve.IsSeparatedFor P (((B h).pullback g) : Presieve Z)) :
    Presieve.IsSheafFor P (Sieve.bind (U : Presieve X) B : Presieve X) := by
  intro s hs
  let y : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.FamilyOfElements P (B hf : Presieve Y) :=
    fun Y f hf Z g hg => s _ (Presieve.bind_comp _ _ hg)
  have hy : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).Compatible := by
    intro Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    apply hs
    apply reassoc_of% comm
  let t : Presieve.FamilyOfElements P (U : Presieve X) :=
    fun Y f hf => (hB hf).amalgamate (y hf) (hy hf)
  have ht : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).IsAmalgamation (t f hf) := fun Y f hf =>
    (hB hf).isAmalgamation _
  have hT : t.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z W f h hf
    apply (hB (U.downward_closed hf h)).isSeparatedFor.ext
    intro Y l hl
    apply (hB' hf (l ≫ h)).ext
    intro M m hm
    have : Sieve.bind U B (m ≫ l ≫ h ≫ f) := by simpa using (bind_comp f hf hm : Sieve.bind U B _)
    trans s (m ≫ l ≫ h ≫ f) this
    · have := ht (U.downward_closed hf h) _ ((B _).downward_closed hl m)
      simp only [op_comp, Functor.map_comp, comp_apply] at this
      grind
    · have h : s _ _ = _ := (ht hf _ hm).symm
      -- Porting note: this was done by `simp only [assoc] at`
      conv_lhs at h => congr; rw [assoc, assoc]
      simp [h]
  refine ⟨hU.amalgamate t hT, ?_, ?_⟩
  · rintro Z _ ⟨Y, f, g, hg, hf, rfl⟩
    rw [op_comp, Functor.map_comp, comp_apply, Presieve.IsSheafFor.valid_glue _ _ _ hg]
    apply ht hg _ hf
  · intro y hy
    apply hU.isSeparatedFor.ext
    intro Y f hf
    apply (hB hf).isSeparatedFor.ext
    intro Z g hg
    rw [← comp_apply, ← Functor.map_comp, ← op_comp, hy _ (Presieve.bind_comp _ _ hg),
      hU.valid_glue _ _ hf, ht hf _ hg]

/-- Given two sieves `R` and `S`, to show that `P` is a sheaf for `S`, we can show:
* `P` is a sheaf for `R`
* `P` is a sheaf for the pullback of `S` along any arrow in `R`
* `P` is separated for the pullback of `R` along any arrow in `S`.

This is mostly an auxiliary lemma to construct `Sheaf.finestTopology`.
Adapted from [Elephant], Lemma C2.1.7(ii) with suggestions as mentioned in
https://math.stackexchange.com/a/358709
-/
/-
**CategoryTheory.Presieve.isSheafFor_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Presieve`。
形式化陈述：isSheafFor_trans (P : Cᵒᵖ ⥤ Type*) (R S : Sieve X) (hR : Presieve.IsSheafF
or P (R : Presieve X)) (hR' : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : S f), Presieve.IsSepar
atedFor P (R.pullback f : Presieve Y)) (hS : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : R f), P
resieve.IsSheafFor P (S.pullback f : Presieve Y)) : Presieve.IsSheafFor P (S : P
resieve X)
参数：P : Cᵒᵖ ⥤ Type*；R S : Sieve X；hR : Presieve.IsSheafFor P (R : Presieve X)；hR'
 : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : S f), Presieve.IsSeparatedFor P (R.pullback f : P
resieve Y)；hS : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : R f), Presieve.IsSheafFor P (S.pullb
ack f : Presieve Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.isSheafFor_subsieve_aux`：isSheafFor_subsieve_aux
 (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X} (h : (S : Presieve X) <= R) (
hS : IsSheafFor P (S : Presieve X)) (…
· 使用定理 `CategoryTheory.Presieve.isSheafFor_bind`：isSheafFor_bind (P : Cᵒᵖ ⥤ Type
*) (U : Sieve X) (B : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f -> Sieve Y) (hU : Presieve.IsS
heafFor P (U : Presieve X)) (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.pullback_comp`：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y
} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Given two sieves `R` and `S`, to show that `P` is a sheaf for `S`, we can show:
* `P` is a sheaf for `R`
* `P` is a sheaf for the pullback of `S` along any arrow in `R`
* `P` is separated for the pullback of `R` along any arrow in `S`.

This is mostly an auxiliary lemma to construct `Sheaf.finestTopology`.
Adapted from [Elephant], Lemma C2.1.7(ii) with suggestions as mentioned in
https://math.stackexchange.com/a/358709
-/
theorem isSheafFor_trans (P : Cᵒᵖ ⥤ Type*) (R S : Sieve X)
    (hR : Presieve.IsSheafFor P (R : Presieve X))
    (hR' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : S f), Presieve.IsSeparatedFor P (R.pullback f : Presieve Y))
    (hS : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : R f), Presieve.IsSheafFor P (S.pullback f : Presieve Y)) :
    Presieve.IsSheafFor P (S : Presieve X) := by
  have : (Sieve.bind R fun Y f _ => S.pullback f : Presieve X) ≤ S := by
    rintro Z f ⟨W, f, g, hg, hf : S _, rfl⟩
    apply hf
  apply Presieve.isSheafFor_subsieve_aux P this
  · apply isSheafFor_bind _ _ _ hR hS
    intro Y f hf Z g
    rw [← Sieve.pullback_comp]
    apply (hS (R.downward_closed hf _)).isSeparatedFor
  · intro Y f hf
    have : Sieve.pullback f (Sieve.bind R fun T (k : T ⟶ X) (_ : R k) => Sieve.pullback k S) =
        R.pullback f := by
      ext Z g
      constructor
      · rintro ⟨W, k, l, hl, _, comm⟩
        rw [pullback_apply, ← comm]
        simp [hl]
      · intro a
        refine ⟨Z, 𝟙 Z, _, a, ?_⟩
        simp [hf]
    rw [this]
    apply hR' hf

end Presieve

end CategoryTheory

