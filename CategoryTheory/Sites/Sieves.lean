/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/
module

public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Theory of sieves

- For an object `X` of a category `C`, a `Sieve X` is a predicate on morphisms to `X`
  which is closed under left-composition.
- The complete lattice structure on sieves is given, as well as the Galois insertion
  given by downward-closing.
- A `Sieve X` (functorially) induces a presheaf on `C` together with a monomorphism to
  the Yoneda embedding of `X`.

## Tags

sieve, pullback
-/

@[expose] public section


universe w w' v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
variable {X Y Z : C} (f : Y ⟶ X)

/-- A predicate on arrows with codomain `X`. -/
@[implicit_reducible]
/-
**CategoryTheory.Presieve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Presieve (X : C)
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate on arrows with codomain `X`.
-/
def Presieve (X : C) :=
  ∀ ⦃Y⦄, (Y ⟶ X) → Prop
deriving CompleteLattice, Inhabited

@[simp]
/-
**CategoryTheory.top_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：top_apply (f : Y ⟶ X) : (⊤ : Presieve X) f
参数：f : Y ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
lemma top_apply (f : Y ⟶ X) : (⊤ : Presieve X) f :=
  trivial

@[simp]
/-
**CategoryTheory.bot_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：bot_apply (f : Y ⟶ X) : (⊥ : Presieve X) f ↔ False
参数：f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma bot_apply (f : Y ⟶ X) : (⊥ : Presieve X) f ↔ False :=
  .rfl

namespace Presieve

/-- The full subcategory of the over category `C/X` consisting of arrows which belong to a
    presieve on `X`. -/
/-
**CategoryTheory.Presieve.category** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.P
resieve`。
形式化陈述：category {X : C} (P : Presieve X)
参数：P : Presieve X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory of the over category `C/X` consisting of arrows which belon
g to a
    presieve on `X`.
-/
abbrev category {X : C} (P : Presieve X) :=
  ObjectProperty.FullSubcategory fun f : Over X => P f.hom

/-- Construct an object of `P.category`. -/
/-
**CategoryTheory.Presieve.categoryMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Presieve`。
形式化陈述：categoryMk {X : C} (P : Presieve X) {Y : C} (f : Y ⟶ X) (hf : P f) : P.cat
egory
参数：P : Presieve X；f : Y ⟶ X；hf : P f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an object of `P.category`.
-/
abbrev categoryMk {X : C} (P : Presieve X) {Y : C} (f : Y ⟶ X) (hf : P f) : P.category :=
  ⟨Over.mk f, hf⟩

/-- Given a sieve `S` on `X : C`, its associated diagram `S.diagram` is defined to be
    the natural functor from the full subcategory of the over category `C/X` consisting
    of arrows in `S` to `C`. -/
/-
**CategoryTheory.Presieve.diagram** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Pr
esieve`。
形式化陈述：diagram (S : Presieve X) : S.category ⥤ C
参数：S : Presieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sieve `S` on `X : C`, its associated diagram `S.diagram` is defined to b
e
    the natural functor from the full subcategory of the over category `C/X` con
sisting
    of arrows in `S` to `C`.
-/
abbrev diagram (S : Presieve X) : S.category ⥤ C :=
  ObjectProperty.ι _ ⋙ Over.forget X

/-- Given a sieve `S` on `X : C`, its associated cocone `S.cocone` is defined to be
    the natural cocone over the diagram defined above with cocone point `X`. -/
/-
**CategoryTheory.Presieve.cocone** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Pre
sieve`。
形式化陈述：cocone (S : Presieve X) : Cocone S.diagram
参数：S : Presieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sieve `S` on `X : C`, its associated cocone `S.cocone` is defined to be
    the natural cocone over the diagram defined above with cocone point `X`.
-/
abbrev cocone (S : Presieve X) : Cocone S.diagram :=
  (Over.forgetCocone X).whisker (ObjectProperty.ι _)

/-- Given a presieve `S` on `X`, and presieve `R` on `Y` for each
`f : Y ⟶ X` in `S`, produce a presieve on `X`:
`{ g ≫ f | (f : Y ⟶ X) ∈ S, (g : Z ⟶ Y) ∈ R f }`.
-/
/-
**CategoryTheory.Presieve.bind** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Presiev
e`。
形式化陈述：bind (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y) : Pr
esieve X
参数：S : Presieve X；R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presieve `S` on `X`, and presieve `R` on `Y` for each
`f : Y ⟶ X` in `S`, produce a presieve on `X`:
`{ g ≫ f | (f : Y ⟶ X) ∈ S, (g : Z ⟶ Y) ∈ R f }`.
-/
def bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y) : Presieve X := fun Z h =>
  ∃ (Y : C) (g : Z ⟶ Y) (f : Y ⟶ X) (H : S f), R H g ∧ g ≫ f = h

/-- Structure which contains the data and properties for a morphism `h` satisfying
`Presieve.bind S R h`. -/
/-
**CategoryTheory.Presieve.BindStruct** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.P
resieve`。
形式化陈述：BindStruct (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y
) {Z : C} (h : Z ⟶ X) where /-- the intermediate object -/ Y : C /-- a morphism 
in the family of presieves `R` -/ g : Z ⟶ Y /-- a morphism in the presieve `S` -
/ f : Y ⟶ X hf : S f hg : R hf g fac : g ≫ f = h  attribute [reassoc (attr
参数：S : Presieve X；R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y；h : Z ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure which contains the data and properties for a morphism `h` satisfying
`Presieve.bind S R h`.
-/
structure BindStruct (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y)
    {Z : C} (h : Z ⟶ X) where
  /-- the intermediate object -/
  Y : C
  /-- a morphism in the family of presieves `R` -/
  g : Z ⟶ Y
  /-- a morphism in the presieve `S` -/
  f : Y ⟶ X
  hf : S f
  hg : R hf g
  fac : g ≫ f = h

attribute [reassoc (attr := simp)] BindStruct.fac

/-- If a morphism `h` satisfies `Presieve.bind S R h`, this is a choice of a structure
in `BindStruct S R h`. -/
/-
**CategoryTheory.Presieve.bind.bindStruct** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Presieve.bind`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X : C
} →       {S : CategoryTheory.Presieve X} →         {R : ⦃Y : C⦄ → ⦃f : Y ⟶ X⦄ →
 S f → CategoryTheory.Presieve Y} →           {Z : C} → {h : Z ⟶ X} → S.bind R h
 → S.BindStruct R h
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a morphism `h` satisfies `Presieve.bind S R h`, this is a choice of a structu
re
in `BindStruct S R h`.
-/
noncomputable def bind.bindStruct {S : Presieve X} {R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y}
    {Z : C} {h : Z ⟶ X} (H : bind S R h) : BindStruct S R h :=
  Nonempty.some (by
    obtain ⟨Y, g, f, hf, hg, fac⟩ := H
    exact ⟨{ hf := hf, hg := hg, fac := fac, .. }⟩)
/-
**CategoryTheory.Presieve.BindStruct.bind** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Presieve.BindStruct`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} {S : C
ategoryTheory.Presieve X}   {R : ⦃Y : C⦄ → ⦃f : Y ⟶ X⦄ → S f → CategoryTheory.Pr
esieve Y} {Z : C} {h : Z ⟶ X} (b : S.BindStruct R h), S.bind R h
参数：b : S.BindStruct R h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.BindStruct.hf`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {X : C} {S : CategoryTheory.Presieve X}   {R : ⦃Y : C
⦄ → ⦃f : Y ⟶ X⦄ → S f → Cat…
· 使用定理 `CategoryTheory.Presieve.BindStruct.hg`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {X : C} {S : CategoryTheory.Presieve X}   {R : ⦃Y : C
⦄ → ⦃f : Y ⟶ X⦄ → S f → Cat…
· 使用定理 `CategoryTheory.Presieve.BindStruct.fac`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {X : C} {S : CategoryTheory.Presieve X}   {R : ⦃Y : 
C⦄ → ⦃f : Y ⟶ X⦄ → S f → Cat…
-/
lemma BindStruct.bind {S : Presieve X} {R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y}
    {Z : C} {h : Z ⟶ X} (b : BindStruct S R h) : bind S R h :=
  ⟨b.Y, b.g, b.f, b.hf, b.hg, b.fac⟩

@[simp]
/-
**CategoryTheory.Presieve.bind_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pr
esieve`。
形式化陈述：bind_comp {S : Presieve X} {R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Presiev
e Y} {g : Z ⟶ Y} (h₁ : S f) (h₂ : R h₁ g) : bind S R (g ≫ f)
参数：h₁ : S f；h₂ : R h₁ g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_comp {S : Presieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y} {g : Z ⟶ Y}
    (h₁ : S f) (h₂ : R h₁ g) : bind S R (g ≫ f) :=
  ⟨_, _, _, h₁, h₂, rfl⟩

-- Note we can't make this into `HasSingleton` because of the out-param.
/-- The singleton presieve. -/
/-
**CategoryTheory.Presieve.singleton** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
Presieve`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → {X Y : C} → 
(Y ⟶ X) → CategoryTheory.Presieve X
参数：Y ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The singleton presieve.
-/
inductive singleton : Presieve X
  | mk : singleton f

@[simp]
/-
**CategoryTheory.Presieve.singleton_eq_iff_domain** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Presieve`。
形式化陈述：singleton_eq_iff_domain (f g : Y ⟶ X) : singleton f g ↔ f = g
参数：f g : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem singleton_eq_iff_domain (f g : Y ⟶ X) : singleton f g ↔ f = g := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · rintro rfl
    apply singleton.mk
/-
**CategoryTheory.Presieve.singleton_self** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Presieve`。
形式化陈述：singleton_self : singleton f f
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_self : singleton f f :=
  singleton.mk

/-- A presieve `R` has pullbacks along `f` if for every `h` in `R`, the pullback
with `f` exists. -/
/-
**CategoryTheory.Presieve.HasPullbacks** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Presieve`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {X : C} → 
CategoryTheory.Presieve X → {Y : C} → (Y ⟶ X) → Prop
参数：Y ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presieve `R` has pullbacks along `f` if for every `h` in `R`, the pullback
with `f` exists.
-/
protected class HasPullbacks (R : Presieve X) {Y : C} (f : Y ⟶ X) : Prop where
  hasPullback (f) {Z : C} {h : Z ⟶ X} : R h → Limits.HasPullback h f

protected alias hasPullback := HasPullbacks.hasPullback
/-
**CategoryTheory.Presieve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasPullbacks C] (R : Presieve X) {Y : C} (f : Y ⟶ X) : R.HasPullbacks f where
  hasPullback _ := inferInstance
/-
**CategoryTheory.Presieve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (g : Z ⟶ X) [HasPullback g f] : (singleton g).HasPullbacks f where
  hasPullback {Z} h := by
    intro ⟨⟩
    infer_instance

/-- Pullback a presieve along a fixed map, by taking the pullback in the
category.
This is not the same as the underlying presieve of `Sieve.pullback`, but there is a relation between
them in `pullbackArrows_comm`.
-/
/-
**CategoryTheory.Presieve.pullbackArrows** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Presieve`。
形式化陈述：pullbackArrows (R : Presieve X) [R.HasPullbacks f] : Presieve Y | mk (Z : 
C) (h : Z ⟶ X) (hRh : R h) : haveI
参数：R : Presieve X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a presieve along a fixed map, by taking the pullback in the
category.
This is not the same as the underlying presieve of `Sieve.pullback`, but there i
s a relation between
them in `pullbackArrows_comm`.
-/
inductive pullbackArrows (R : Presieve X) [R.HasPullbacks f] : Presieve Y
  | mk (Z : C) (h : Z ⟶ X) (hRh : R h) :
    haveI := R.hasPullback f hRh
    pullbackArrows _ (pullback.snd h f)
/-
**CategoryTheory.Presieve.pullback_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Presieve`。
形式化陈述：pullback_singleton (g : Z ⟶ X) [HasPullback g f] : pullbackArrows f (singl
eton g) = singleton (pullback.snd g f)
参数：g : Z ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Presieve.instHasPullbacksSingletonOfHasPullback`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : Y ⟶ X) (g :
 Z ⟶ X)   [CategoryTheory.Limits.HasPullback g f], (…
· 使用定理 `CategoryTheory.Presieve.hasPullback`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Presieve X} {Y : C} (f : Y 
⟶ X)   [self : R.HasPullb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem pullback_singleton (g : Z ⟶ X) [HasPullback g f] :
    pullbackArrows f (singleton g) = singleton (pullback.snd g f) := by
  funext W
  ext h
  constructor
  · rintro ⟨W, _, _, _⟩
    exact singleton.mk
  · rintro ⟨_⟩
    exact pullbackArrows.mk Z g singleton.mk

/-- Construct the presieve given by the family of arrows indexed by `ι`. -/
/-
**CategoryTheory.Presieve.ofArrows** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.P
resieve`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X : C
} → {ι : Type u_1} → (Y : ι → C) → ((i : ι) → Y i ⟶ X) → CategoryTheory.Presieve
 X
参数：Y : ι → C；(i : ι) → Y i ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the presieve given by the family of arrows indexed by `ι`.
-/
inductive ofArrows {ι : Type*} (Y : ι → C) (f : ∀ i, Y i ⟶ X) : Presieve X
  | mk (i : ι) : ofArrows _ _ (f i)
/-
**CategoryTheory.Presieve.ofArrows.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Presieve.ofArrows`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} {ι : T
ype u_1} {Y : ι → C} {f : (i : ι) → Y i ⟶ X}   {Z : C} {g : Z ⟶ X} (i : ι) (h : 
Z = Y i),   g = CategoryTheory.CategoryStruct.comp (CategoryTheory.eqToHom h) (f
 i) → CategoryTheory.Presieve.ofArrows Y f g
参数：i : ι；i : ι；h : Z = Y i；CategoryTheory.eqToHom h；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma ofArrows.mk' {ι : Type*} {Y : ι → C} {f : ∀ i, Y i ⟶ X} {Z : C} {g : Z ⟶ X}
    (i : ι) (h : Z = Y i) (hg : g = eqToHom h ≫ f i) :
    ofArrows Y f g := by
  subst h
  simp only [eqToHom_refl, id_comp] at hg
  subst hg
  constructor
/-
**CategoryTheory.Presieve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X)
    [∀ i, HasPullback (g i) f] : (ofArrows Z g).HasPullbacks f where
  hasPullback {_} _ := fun ⟨i⟩ ↦ inferInstance
/-
**CategoryTheory.Presieve.ofArrows_pullback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Presieve`。
形式化陈述：ofArrows_pullback {ι : Type*} (Z : ι -> C) (g : forall i : ι, Z i ⟶ X) [fo
rall i, HasPullback (g i) f] : (ofArrows (fun i => pullback (g i) f) fun _ => pu
llback.snd _ _) = pullbackArrows f (ofArrows Z g)
参数：Z : ι -> C；g : forall i : ι, Z i ⟶ X；g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Presieve.instHasPullbacksOfArrowsOfHasPullback`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) {ι : Ty
pe u_1} (Z : ι → C)   (g : (i : ι) → Z i ⟶ X) [∀ (i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Presieve.hasPullback`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Presieve X} {Y : C} (f : Y 
⟶ X)   [self : R.HasPullb…
-/
theorem ofArrows_pullback {ι : Type*} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X)
    [∀ i, HasPullback (g i) f] :
    (ofArrows (fun i => pullback (g i) f) fun _ => pullback.snd _ _) =
      pullbackArrows f (ofArrows Z g) := by
  funext T
  ext h
  constructor
  · rintro ⟨hk⟩
    exact pullbackArrows.mk _ _ (ofArrows.mk hk)
  · rintro ⟨W, k, ⟨_⟩⟩
    apply ofArrows.mk
/-
**CategoryTheory.Presieve.ofArrows_bind** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Presieve`。
形式化陈述：ofArrows_bind {ι : Type*} (Z : ι -> C) (g : forall i : ι, Z i ⟶ X) (j : fo
rall ⦃Y⦄ (f : Y ⟶ X), ofArrows Z g f -> Type*) (W : forall ⦃Y⦄ (f : Y ⟶ X) (H), 
j f H -> C) (k : forall ⦃Y⦄ (f : Y ⟶ X) (H i), W f H i ⟶ Y) : ((ofArrows Z g).bi
nd fun _ f H => ofArrows (W f H) (k f H)) = ofArrows (fun i : Σ i, j _ (ofArrows
.mk i) => W (g i.1) _ i.2) fun ij => k (g ij.1) _ ij.2 ≫ g ij.1
参数：Z : ι -> C；g : forall i : ι, Z i ⟶ X；j : forall ⦃Y⦄ (f : Y ⟶ X), ofArrows Z g
 f -> Type*；W : forall ⦃Y⦄ (f : Y ⟶ X) (H), j f H -> C；k : forall ⦃Y⦄ (f : Y ⟶ X
) (H i), W f H i ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Presieve.bind_comp`：bind_comp {S : Presieve X} {R : foral
l ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y} {g : Z ⟶ Y} (h₁ : S f) (h₂ : R h₁ g) :
 bind S R (g ≫ f)
-/
theorem ofArrows_bind {ι : Type*} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X)
    (j : ∀ ⦃Y⦄ (f : Y ⟶ X), ofArrows Z g f → Type*) (W : ∀ ⦃Y⦄ (f : Y ⟶ X) (H), j f H → C)
    (k : ∀ ⦃Y⦄ (f : Y ⟶ X) (H i), W f H i ⟶ Y) :
    ((ofArrows Z g).bind fun _ f H => ofArrows (W f H) (k f H)) =
      ofArrows (fun i : Σ i, j _ (ofArrows.mk i) => W (g i.1) _ i.2) fun ij =>
        k (g ij.1) _ ij.2 ≫ g ij.1 := by
  funext Y
  ext f
  constructor
  · rintro ⟨_, _, _, ⟨i⟩, ⟨i'⟩, rfl⟩
    exact ofArrows.mk (Sigma.mk _ _)
  · rintro ⟨i⟩
    exact bind_comp _ (ofArrows.mk _) (ofArrows.mk _)
/-
**CategoryTheory.Presieve.ofArrows_surj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Presieve`。
形式化陈述：ofArrows_surj {ι : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X) {Z : C} (g 
: Z ⟶ X) (hg : ofArrows Y f g) : exists (i : ι) (h : Y i = Z), g = eqToHom h.sym
m ≫ f i
参数：f : forall i, Y i ⟶ X；g : Z ⟶ X；hg : ofArrows Y f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem ofArrows_surj {ι : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ X) {Z : C} (g : Z ⟶ X)
    (hg : ofArrows Y f g) : ∃ (i : ι) (h : Y i = Z),
    g = eqToHom h.symm ≫ f i := by
  obtain ⟨i⟩ := hg
  exact ⟨i, rfl, by simp only [eqToHom_refl, id_comp]⟩
/-
**CategoryTheory.Presieve.exists_eq_ofArrows** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Presieve`。
形式化陈述：exists_eq_ofArrows (R : Presieve X) : exists (ι : Type (max u₁ v₁)) (Y : ι
 -> C) (f : forall i, Y i ⟶ X), R = .ofArrows Y f
参数：R : Presieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma exists_eq_ofArrows (R : Presieve X) :
    ∃ (ι : Type (max u₁ v₁)) (Y : ι → C) (f : ∀ i, Y i ⟶ X), R = .ofArrows Y f := by
  let ι := { x : Σ Z, (Z ⟶ X) // R x.2 }
  use ι, fun x ↦ x.1.1, fun x ↦ x.1.2
  exact le_antisymm (fun Z g hg ↦ .mk (⟨⟨_, _⟩, hg⟩ : ι)) fun Z g ⟨x⟩ ↦ x.2
/-
**CategoryTheory.Presieve.ofArrows_category** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Presieve`。
形式化陈述：ofArrows_category {S : C} (R : Presieve S) : Presieve.ofArrows _ (fun (f :
 R.category) => f.obj.hom) = R
参数：R : Presieve S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma ofArrows_category {S : C} (R : Presieve S) :
    Presieve.ofArrows _ (fun (f : R.category) ↦ f.obj.hom) = R := by
  refine le_antisymm ?_ ?_
  · rintro _ _ ⟨X, h⟩
    exact h
  · rintro X g hg
    exact .mk (ι := R.category) ⟨Over.mk g, hg⟩

/-- If `g : Y ⟶ S` is in the presieve given by the indexed family `fᵢ`, this is a choice
of index such that `g = fᵢ` modulo `eqToHom`.
Note: This should generally not be used! If possible, use the induction principle
for the type `Presieve.ofArrows` instead (using e.g., `rintro / obtain`). -/
noncomputable
/-
**CategoryTheory.Presieve.ofArrows.idx** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Presieve.ofArrows`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {ι : T
ype u_1} →       {S : C} →         {X : ι → C} → {f : (i : ι) → X i ⟶ S} → {Y : 
C} → {g : Y ⟶ S} → CategoryTheory.Presieve.ofArrows X f g → ι
参数：i : ι。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.ofArrows_surj`：ofArrows_surj {ι : Type*} {Y : ι 
-> C} (f : forall i, Y i ⟶ X) {Z : C} (g : Z ⟶ X) (hg : ofArrows Y f g) : exists
 (i : ι) (h : Y i = Z), g =…
-/
def ofArrows.idx {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
    (hf : Presieve.ofArrows X f g) : ι :=
  (ofArrows_surj _ _ hf).choose
/-
**CategoryTheory.Presieve.ofArrows.obj_idx** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Presieve.ofArrows`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {ι : Type u_1}
 {S : C} {X : ι → C} {f : (i : ι) → X i ⟶ S}   {Y : C} {g : Y ⟶ S} (hf : Categor
yTheory.Presieve.ofArrows X f g), X hf.idx = Y
参数：i : ι；hf : CategoryTheory.Presieve.ofArrows X f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.ofArrows_surj`：ofArrows_surj {ι : Type*} {Y : ι 
-> C} (f : forall i, Y i ⟶ X) {Z : C} (g : Z ⟶ X) (hg : ofArrows Y f g) : exists
 (i : ι) (h : Y i = Z), g =…
-/
lemma ofArrows.obj_idx {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
    (hf : ofArrows X f g) : X hf.idx = Y :=
  (ofArrows_surj _ _ hf).choose_spec.1
/-
**CategoryTheory.Presieve.ofArrows.eq_eqToHom_comp_hom_idx** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Presieve.ofArrows`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {ι : Type u_1}
 {S : C} {X : ι → C} {f : (i : ι) → X i ⟶ S}   {Y : C} {g : Y ⟶ S} (hf : Categor
yTheory.Presieve.ofArrows X f g),   g = CategoryTheory.CategoryStruct.comp (Cate
goryTheory.eqToHom ⋯) (f hf.idx)
参数：i : ι；hf : CategoryTheory.Presieve.ofArrows X f g；CategoryTheory.eqToHom ⋯；f 
hf.idx。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.ofArrows_surj`：ofArrows_surj {ι : Type*} {Y : ι 
-> C} (f : forall i, Y i ⟶ X) {Z : C} (g : Z ⟶ X) (hg : ofArrows Y f g) : exists
 (i : ι) (h : Y i = Z), g =…
-/
lemma ofArrows.eq_eqToHom_comp_hom_idx {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S} {Y : C}
    {g : Y ⟶ S} (hf : ofArrows X f g) : g = eqToHom hf.obj_idx.symm ≫ f hf.idx :=
  (Presieve.ofArrows_surj _ _ hf).choose_spec.2
/-
**CategoryTheory.Presieve.ofArrows.hom_idx** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Presieve.ofArrows`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {ι : Type u_1}
 {S : C} {X : ι → C} {f : (i : ι) → X i ⟶ S}   {Y : C} {g : Y ⟶ S} (hf : Categor
yTheory.Presieve.ofArrows X f g),   f hf.idx = CategoryTheory.CategoryStruct.com
p (CategoryTheory.eqToHom ⋯) g
参数：i : ι；hf : CategoryTheory.Presieve.ofArrows X f g；CategoryTheory.eqToHom ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Presieve.ofArrows.obj_idx`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {ι : Type u_1} {S : C} {X : ι → C} {f : (i : ι) → 
X i ⟶ S}   {Y : C} {g : Y ⟶ S}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.ofArrows.eq_eqToHom_comp_hom_idx`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {ι : Type u_1} {S : C} {X : ι → C}
 {f : (i : ι) → X i ⟶ S}   {Y : C} {g : Y ⟶ S}…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofArrows.hom_idx {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
    (hf : ofArrows X f g) : f hf.idx = eqToHom hf.obj_idx ≫ g := by
  simp [eq_eqToHom_comp_hom_idx hf]
/-
**CategoryTheory.Presieve.ofArrows_comp_le** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Presieve`。
形式化陈述：ofArrows_comp_le {X : C} {ι σ : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X
) (a : σ -> ι) : ofArrows (Y ∘ a) (fun i => f (a i)) <= ofArrows Y f
参数：f : forall i, Y i ⟶ X；a : σ -> ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma ofArrows_comp_le {X : C} {ι σ : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ X) (a : σ → ι) :
    ofArrows (Y ∘ a) (fun i ↦ f (a i)) ≤ ofArrows Y f := by
  rintro - - ⟨i⟩
  use a i
/-
**CategoryTheory.Presieve.ofArrows_comp_eq_of_surjective** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Presieve`。
形式化陈述：ofArrows_comp_eq_of_surjective {X : C} {ι σ : Type*} {Y : ι -> C} (f : for
all i, Y i ⟶ X) {a : σ -> ι} (ha : a.Surjective) : ofArrows (Y ∘ a) (fun i => f 
(a i)) = ofArrows Y f
参数：f : forall i, Y i ⟶ X；ha : a.Surjective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.Presieve.ofArrows_comp_le`：ofArrows_comp_le {X : C} {ι σ 
: Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X) (a : σ -> ι) : ofArrows (Y ∘ a) (f
un i => f (a i)) <= ofArrows Y…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma ofArrows_comp_eq_of_surjective {X : C} {ι σ : Type*} {Y : ι → C}
    (f : ∀ i, Y i ⟶ X) {a : σ → ι} (ha : a.Surjective) :
    ofArrows (Y ∘ a) (fun i ↦ f (a i)) = ofArrows Y f := by
  refine le_antisymm (ofArrows_comp_le f a) ?_
  rintro - - ⟨i⟩
  obtain ⟨j, rfl⟩ := ha i
  use j
/-
**CategoryTheory.Presieve.ofArrows_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Presieve`。
形式化陈述：ofArrows_le_iff {X : C} {ι : Type*} {Y : ι -> C} {f : forall i, Y i ⟶ X} {
R : Presieve X} : Presieve.ofArrows Y f <= R ↔ forall i, R (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofArrows_le_iff {X : C} {ι : Type*} {Y : ι → C} {f : ∀ i, Y i ⟶ X} {R : Presieve X} :
    Presieve.ofArrows Y f ≤ R ↔ ∀ i, R (f i) :=
  ⟨fun hle i ↦ hle _ _ ⟨i⟩, fun h _ g ⟨i⟩ ↦ h i⟩
/-
**CategoryTheory.Presieve.ofArrows_of_unique** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Presieve`。
形式化陈述：ofArrows_of_unique {X : C} {ι : Type*} [Unique ι] {Y : ι -> C} (f : forall
 i, Y i ⟶ X) : ofArrows Y f = singleton (f default)
参数：f : forall i, Y i ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.ofArrows_le_iff`：ofArrows_le_iff {X : C} {ι : Ty
pe*} {Y : ι -> C} {f : forall i, Y i ⟶ X} {R : Presieve X} : Presieve.ofArrows Y
 f <= R ↔ forall i, R (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma ofArrows_of_unique {X : C} {ι : Type*} [Unique ι] {Y : ι → C} (f : ∀ i, Y i ⟶ X) :
    ofArrows Y f = singleton (f default) := by
  refine le_antisymm ?_ fun Y _ ⟨⟩ ↦ ⟨default⟩
  rw [ofArrows_le_iff]
  intro i
  obtain rfl : i = default := Subsingleton.elim _ _
  simp
/-
**CategoryTheory.Presieve.ofArrows_pUnit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Presieve`。
形式化陈述：ofArrows_pUnit : (ofArrows _ fun _ : PUnit.{w + 1} => f) = singleton f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.ofArrows_of_unique`：ofArrows_of_unique {X : C} {
ι : Type*} [Unique ι] {Y : ι -> C} (f : forall i, Y i ⟶ X) : ofArrows Y f = sing
leton (f default)
-/
theorem ofArrows_pUnit : (ofArrows _ fun _ : PUnit.{w + 1} => f) = singleton f := by
  rw [ofArrows_of_unique]

@[grind =]
/-
**CategoryTheory.Presieve.ofArrows_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Presieve`。
形式化陈述：ofArrows_of_isEmpty {X : C} {ι : Type*} [IsEmpty ι] {Y : ι -> C} (f : fora
ll i, Y i ⟶ X) : ofArrows Y f = ⊥
参数：f : forall i, Y i ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `CategoryTheory.Presieve.ofArrows_le_iff`：ofArrows_le_iff {X : C} {ι : Ty
pe*} {Y : ι -> C} {f : forall i, Y i ⟶ X} {R : Presieve X} : Presieve.ofArrows Y
 f <= R ↔ forall i, R (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma ofArrows_of_isEmpty {X : C} {ι : Type*} [IsEmpty ι] {Y : ι → C} (f : ∀ i, Y i ⟶ X) :
    ofArrows Y f = ⊥ := by
  rw [eq_bot_iff, ofArrows_le_iff]
  simp

/-- A convenient constructor for a refinement of a presieve of the form `Presieve.ofArrows`.
This contains a sieve obtained by `Sieve.bind` and `Sieve.ofArrows`, see
`Presieve.bind_ofArrows_le_bindOfArrows`, but has better definitional properties. -/
/-
**CategoryTheory.Presieve.bindOfArrows** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Presieve`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {ι : T
ype u_1} →       {X : C} →         (Y : ι → C) → ((i : ι) → Y i ⟶ X) → ((i : ι) 
→ CategoryTheory.Presieve (Y i)) → CategoryTheory.Presieve X
参数：Y : ι → C；(i : ι) → Y i ⟶ X；(i : ι) → CategoryTheory.Presieve (Y i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenient constructor for a refinement of a presieve of the form `Presieve.of
Arrows`.
This contains a sieve obtained by `Sieve.bind` and `Sieve.ofArrows`, see
`Presieve.bind_ofArrows_le_bindOfArrows`, but has better definitional properties
.
-/
inductive bindOfArrows {ι : Type*} {X : C} (Y : ι → C)
    (f : ∀ i, Y i ⟶ X) (R : ∀ i, Presieve (Y i)) : Presieve X
  | mk (i : ι) {Z : C} (g : Z ⟶ Y i) (hg : R i g) : bindOfArrows Y f R (g ≫ f i)
/-
**CategoryTheory.Presieve.bindOfArrows_ofArrows** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Presieve`。
形式化陈述：bindOfArrows_ofArrows {ι : Type*} {S : C} {X : ι -> C} (f : (i : ι) -> X i
 ⟶ S) {σ : ι -> Type*} {Y : (i : ι) -> σ i -> C} (g : (i : ι) -> (j : σ i) -> Y 
i j ⟶ X i) : Presieve.bindOfArrows X f (fun i => .ofArrows (Y i) (g i)) = Presie
ve.ofArrows (fun p : Σ i, σ i => Y p.1 p.2) (fun p => g p.1 p.2 ≫ f p.1)
参数：f : (i : ι) -> X i ⟶ S；i : ι；g : (i : ι) -> (j : σ i) -> Y i j ⟶ X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma bindOfArrows_ofArrows {ι : Type*} {S : C} {X : ι → C} (f : (i : ι) → X i ⟶ S)
    {σ : ι → Type*} {Y : (i : ι) → σ i → C} (g : (i : ι) → (j : σ i) → Y i j ⟶ X i) :
    Presieve.bindOfArrows X f (fun i ↦ .ofArrows (Y i) (g i)) =
      Presieve.ofArrows (fun p : Σ i, σ i ↦ Y p.1 p.2) (fun p ↦ g p.1 p.2 ≫ f p.1) := by
  refine le_antisymm ?_ (fun _ _ ⟨p⟩ ↦ ⟨p.1, _, ⟨p.2⟩⟩)
  rintro W u ⟨i, v, ⟨j⟩⟩
  exact ⟨Sigma.mk i j⟩

/-- Compose a presieve on the right with a morphism. -/
/-
**CategoryTheory.Presieve.pushforward** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Presieve`。
形式化陈述：pushforward {X Y : C} (f : X ⟶ Y) (R : Presieve X) : Presieve Y
参数：f : X ⟶ Y；R : Presieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a presieve on the right with a morphism.
-/
def pushforward {X Y : C} (f : X ⟶ Y) (R : Presieve X) : Presieve Y :=
  fun Z fg ↦ ∃ (g : Z ⟶ X), g ≫ f = fg ∧ R g

@[grind .]
/-
**CategoryTheory.Presieve.pushforward_apply_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Presieve`。
形式化陈述：pushforward_apply_comp {X Y Z : C} {f : X ⟶ Y} {R : Presieve X} {g : Z ⟶ X
} (hg : R g) : R.pushforward f (g ≫ f)
参数：hg : R g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushforward_apply_comp {X Y Z : C} {f : X ⟶ Y} {R : Presieve X} {g : Z ⟶ X} (hg : R g) :
    R.pushforward f (g ≫ f) :=
  ⟨g, rfl, hg⟩
/-
**CategoryTheory.Presieve.pushforward_ofArrows** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Presieve`。
形式化陈述：pushforward_ofArrows {ι : Type*} {U : ι -> C} {X Y : C} (g : forall i, U i
 ⟶ X) (f : X ⟶ Y) : (ofArrows _ g).pushforward f = ofArrows _ (g · ≫ f)
参数：g : forall i, U i ⟶ X；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.ofArrows_le_iff`：ofArrows_le_iff {X : C} {ι : Ty
pe*} {Y : ι -> C} {f : forall i, Y i ⟶ X} {R : Presieve X} : Presieve.ofArrows Y
 f <= R ↔ forall i, R (f i)
-/
lemma pushforward_ofArrows {ι : Type*} {U : ι → C} {X Y : C} (g : ∀ i, U i ⟶ X)
    (f : X ⟶ Y) : (ofArrows _ g).pushforward f = ofArrows _ (g · ≫ f) := by
  refine le_antisymm ?_ ?_
  · rintro _ _ ⟨u, rfl, ⟨i⟩⟩
    exact ⟨i⟩
  · rw [ofArrows_le_iff]
    intro i
    use g i, rfl
    exact ⟨i⟩
/-
**CategoryTheory.Presieve.pushforward_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Presieve`。
形式化陈述：pushforward_singleton {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (singleton f).
pushforward g = .singleton (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.ofArrows_pUnit`：ofArrows_pUnit : (ofArrows _ fun
 _ : PUnit.{w + 1} => f) = singleton f
· 使用引理 `CategoryTheory.Presieve.pushforward_ofArrows`：pushforward_ofArrows {ι : 
Type*} {U : ι -> C} {X Y : C} (g : forall i, U i ⟶ X) (f : X ⟶ Y) : (ofArrows _ 
g).pushforward f = ofArrows _ (g ·…
-/
lemma pushforward_singleton {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (singleton f).pushforward g = .singleton (f ≫ g) := by
  rw [← ofArrows_pUnit.{0}, pushforward_ofArrows, ofArrows_pUnit.{0}]

/-- The pullback of a presieve `R` on `Y` along a morphism `f : X ⟶ Y` is the presieve on `X`
given by all morphisms `g : Z ⟶ X` such that `g ≫ f` is in `R`. -/
/-
**CategoryTheory.Presieve.pullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pre
sieve`。
形式化陈述：pullback {X Y : C} (f : X ⟶ Y) (R : Presieve Y) : Presieve X
参数：f : X ⟶ Y；R : Presieve Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a presieve `R` on `Y` along a morphism `f : X ⟶ Y` is the presie
ve on `X`
given by all morphisms `g : Z ⟶ X` such that `g ≫ f` is in `R`.
-/
def pullback {X Y : C} (f : X ⟶ Y) (R : Presieve Y) : Presieve X :=
  fun _ g ↦ R (g ≫ f)

variable {f} in
@[simp, grind =]
/-
**CategoryTheory.Presieve.pullback_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Presieve`。
形式化陈述：pullback_iff {R : Presieve X} {Z : C} {g : Z ⟶ Y} : R.pullback f g ↔ R (g 
≫ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma pullback_iff {R : Presieve X} {Z : C} {g : Z ⟶ Y} :
    R.pullback f g ↔ R (g ≫ f) :=
  .rfl
/-
**CategoryTheory.Presieve.pushforward_le_iff_le_pullback** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Presieve`。
形式化陈述：pushforward_le_iff_le_pullback (R : Presieve Y) (T : Presieve X) : R.pushf
orward f <= T ↔ R <= T.pullback f
参数：R : Presieve Y；T : Presieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presieve.pushforward_apply_comp`：pushforward_apply_comp {
X Y Z : C} {f : X ⟶ Y} {R : Presieve X} {g : Z ⟶ X} (hg : R g) : R.pushforward f
 (g ≫ f)
-/
lemma pushforward_le_iff_le_pullback (R : Presieve Y) (T : Presieve X) :
    R.pushforward f ≤ T ↔ R ≤ T.pullback f := by
  refine ⟨fun hle Z g hg ↦ hle _ _ (pushforward_apply_comp hg), ?_⟩
  rintro hle Z - ⟨g, rfl, hg⟩
  exact hle _ _ hg
/-
**CategoryTheory.Presieve.galoisConnection_pushforward_pullback** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：galoisConnection_pushforward_pullback : GaloisConnection (pushforward f) (
pullback f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presieve.pushforward_le_iff_le_pullback`：pushforward_le_i
ff_le_pullback (R : Presieve Y) (T : Presieve X) : R.pushforward f <= T ↔ R <= T
.pullback f
-/
lemma galoisConnection_pushforward_pullback :
    GaloisConnection (pushforward f) (pullback f) :=
  pushforward_le_iff_le_pullback f
/-
**CategoryTheory.Presieve.monotone_pushforward** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Presieve`。
形式化陈述：monotone_pushforward : Monotone (pushforward f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用引理 `CategoryTheory.Presieve.galoisConnection_pushforward_pullback`：galoisCon
nection_pushforward_pullback : GaloisConnection (pushforward f) (pullback f)
-/
lemma monotone_pushforward : Monotone (pushforward f) :=
  (galoisConnection_pushforward_pullback f).monotone_l
/-
**CategoryTheory.Presieve.monotone_pullback** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Presieve`。
形式化陈述：monotone_pullback : Monotone (pullback f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用引理 `CategoryTheory.Presieve.galoisConnection_pushforward_pullback`：galoisCon
nection_pushforward_pullback : GaloisConnection (pushforward f) (pullback f)
-/
lemma monotone_pullback : Monotone (pullback f) :=
  (galoisConnection_pushforward_pullback f).monotone_u
/-
**CategoryTheory.Presieve.pushforward_pullback_le** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Presieve`。
形式化陈述：pushforward_pullback_le (R : Presieve X) : (R.pullback f).pushforward f <=
 R
参数：R : Presieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用引理 `CategoryTheory.Presieve.galoisConnection_pushforward_pullback`：galoisCon
nection_pushforward_pullback : GaloisConnection (pushforward f) (pullback f)
-/
lemma pushforward_pullback_le (R : Presieve X) : (R.pullback f).pushforward f ≤ R :=
  (galoisConnection_pushforward_pullback f).l_u_le _
/-
**CategoryTheory.Presieve.le_pullback_pushforward** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Presieve`。
形式化陈述：le_pullback_pushforward (R : Presieve Y) : R <= (R.pushforward f).pullback
 f
参数：R : Presieve Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用引理 `CategoryTheory.Presieve.galoisConnection_pushforward_pullback`：galoisCon
nection_pushforward_pullback : GaloisConnection (pushforward f) (pullback f)
-/
lemma le_pullback_pushforward (R : Presieve Y) : R ≤ (R.pushforward f).pullback f :=
  (galoisConnection_pushforward_pullback f).le_u_l _

@[simp]
/-
**CategoryTheory.Presieve.pullback_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Presieve`。
形式化陈述：pullback_id (R : Presieve X) : R.pullback (𝟙 X) = R
参数：R : Presieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullback_id (R : Presieve X) : R.pullback (𝟙 X) = R := by
  funext
  simp
/-
**CategoryTheory.Presieve.pullback_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Presieve`。
形式化陈述：pullback_comp (R : Presieve Z) (g : X ⟶ Z) : R.pullback (f ≫ g) = (R.pullb
ack g).pullback f
参数：R : Presieve Z；g : X ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullback_comp (R : Presieve Z) (g : X ⟶ Z) :
    R.pullback (f ≫ g) = (R.pullback g).pullback f := by
  funext
  simp

@[simp]
/-
**CategoryTheory.Presieve.pushforward_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Presieve`。
形式化陈述：pushforward_id (R : Presieve X) : R.pushforward (𝟙 X) = R
参数：R : Presieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pushforward_id (R : Presieve X) : R.pushforward (𝟙 X) = R := by
  funext
  simp [pushforward]
/-
**CategoryTheory.Presieve.pushforward_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Presieve`。
形式化陈述：pushforward_comp (R : Presieve Y) (g : X ⟶ Z) : R.pushforward (f ≫ g) = (R
.pushforward f).pushforward g
参数：R : Presieve Y；g : X ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma pushforward_comp (R : Presieve Y) (g : X ⟶ Z) :
    R.pushforward (f ≫ g) = (R.pushforward f).pushforward g := by
  funext
  simp [pushforward]

/-- Given a presieve on `F(X)`, we can define a presieve on `X` by taking the preimage via `F`. -/
/-
**CategoryTheory.Presieve.functorPullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Presieve`。
形式化陈述：functorPullback (R : Presieve (F.obj X)) : Presieve X
参数：R : Presieve (F.obj X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presieve on `F(X)`, we can define a presieve on `X` by taking the preima
ge via `F`.
-/
def functorPullback (R : Presieve (F.obj X)) : Presieve X := fun _ f => R (F.map f)

@[simp]
/-
**CategoryTheory.Presieve.functorPullback_mem** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Presieve`。
形式化陈述：functorPullback_mem (R : Presieve (F.obj X)) {Y} (f : Y ⟶ X) : R.functorPu
llback F f ↔ R (F.map f)
参数：R : Presieve (F.obj X)；f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem functorPullback_mem (R : Presieve (F.obj X)) {Y} (f : Y ⟶ X) :
    R.functorPullback F f ↔ R (F.map f) :=
  Iff.rfl

@[simp]
/-
**CategoryTheory.Presieve.functorPullback_id** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Presieve`。
形式化陈述：functorPullback_id (R : Presieve X) : R.functorPullback (𝟭 _) = R
参数：R : Presieve X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem functorPullback_id (R : Presieve X) : R.functorPullback (𝟭 _) = R :=
  rfl

/-- Given a presieve `R` on `X`, the predicate `R.HasPairwisePullbacks` means that for all arrows
`f` and `g` in `R`, the pullback of `f` and `g` exists. -/
/-
**CategoryTheory.Presieve.HasPairwisePullbacks** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Presieve`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → {X : C} → Ca
tegoryTheory.Presieve X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presieve `R` on `X`, the predicate `R.HasPairwisePullbacks` means that f
or all arrows
`f` and `g` in `R`, the pullback of `f` and `g` exists.
-/
class HasPairwisePullbacks (R : Presieve X) : Prop where
  /-- For all arrows `f` and `g` in `R`, the pullback of `f` and `g` exists. -/
  has_pullbacks : ∀ {Y Z} {f : Y ⟶ X} (_ : R f) {g : Z ⟶ X} (_ : R g), HasPullback f g
/-
**CategoryTheory.Presieve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Presieve X) [HasPullbacks C] : R.HasPairwisePullbacks := ⟨fun _ _ ↦ inferInstance⟩
/-
**CategoryTheory.Presieve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type v₂} {X : α → C} {B : C} (π : (a : α) → X a ⟶ B)
    [(Presieve.ofArrows X π).HasPairwisePullbacks] (a b : α) : HasPullback (π a) (π b) :=
  Presieve.HasPairwisePullbacks.has_pullbacks (Presieve.ofArrows.mk _) (Presieve.ofArrows.mk _)

section FunctorPushforward

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/-- Given a presieve on `X`, we can define a presieve on `F(X)` (which is actually a sieve)
by taking the sieve generated by the image via `F`.
-/
/-
**CategoryTheory.Presieve.functorPushforward** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Presieve`。
形式化陈述：functorPushforward (S : Presieve X) : Presieve (F.obj X)
参数：S : Presieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presieve on `X`, we can define a presieve on `F(X)` (which is actually a
 sieve)
by taking the sieve generated by the image via `F`.
-/
def functorPushforward (S : Presieve X) : Presieve (F.obj X) := fun Y f =>
  ∃ (Z : C) (g : Z ⟶ X) (h : Y ⟶ F.obj Z), S g ∧ f = h ≫ F.map g

variable {F} in
/-
**CategoryTheory.Presieve.functorPushforward_monotone** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Presieve`。
形式化陈述：functorPushforward_monotone {X : C} : Monotone (Presieve.functorPushforwar
d (X
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorPushforward_monotone {X : C} :
    Monotone (Presieve.functorPushforward (X := X) F) :=
  fun _ _ hle _ _ ⟨Z, g, u, hg, hf⟩ ↦ ⟨Z, g, u, hle _ _ hg, hf⟩

/-- An auxiliary definition in order to fix the choice of the preimages between various definitions.
-/
/-
**CategoryTheory.Presieve.FunctorPushforwardStructure** 是 Mathlib 中的一个归纳类型，位于命名空
间 `CategoryTheory.Presieve`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) →           {X : C} → CategoryTheory.Presieve X → {Y : 
D} → (Y ⟶ F.obj X) → Type (max (max u₁ v₁) v₂)
参数：F : CategoryTheory.Functor C D；Y ⟶ F.obj X；max (max u₁ v₁) v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary definition in order to fix the choice of the preimages between vari
ous definitions.
-/
structure FunctorPushforwardStructure (S : Presieve X) {Y} (f : Y ⟶ F.obj X) where
  /-- an object in the source category -/
  preobj : C
  /-- a map in the source category which has to be in the presieve -/
  premap : preobj ⟶ X
  /-- the morphism which appear in the factorisation -/
  lift : Y ⟶ F.obj preobj
  /-- the condition that `premap` is in the presieve -/
  cover : S premap
  /-- the factorisation of the morphism -/
  fac : f = lift ≫ F.map premap

/-- The fixed choice of a preimage. -/
/-
**CategoryTheory.Presieve.getFunctorPushforwardStructure** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Presieve`。
形式化陈述：getFunctorPushforwardStructure {F : C ⥤ D} {S : Presieve X} {Y : D} {f : Y
 ⟶ F.obj X} (h : S.functorPushforward F f) : FunctorPushforwardStructure F S f
参数：h : S.functorPushforward F f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fixed choice of a preimage.
-/
noncomputable def getFunctorPushforwardStructure {F : C ⥤ D} {S : Presieve X} {Y : D}
    {f : Y ⟶ F.obj X} (h : S.functorPushforward F f) : FunctorPushforwardStructure F S f := by
  choose Z f' g h₁ h using h
  exact ⟨Z, f', g, h₁, h⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Presieve.functorPushforward_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Presieve`。
形式化陈述：functorPushforward_comp (R : Presieve X) : R.functorPushforward (F ⋙ G) = 
(R.functorPushforward F).functorPushforward G
参数：R : Presieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem functorPushforward_comp (R : Presieve X) :
    R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPushforward G := by
  funext x
  ext f
  constructor
  · rintro ⟨X, f₁, g₁, h₁, rfl⟩
    exact ⟨F.obj X, F.map f₁, g₁, ⟨X, f₁, 𝟙 _, h₁, by simp⟩, rfl⟩
  · rintro ⟨X, f₁, g₁, ⟨X', f₂, g₂, h₁, rfl⟩, rfl⟩
    exact ⟨X', f₂, g₁ ≫ G.map g₂, h₁, by simp⟩
/-
**CategoryTheory.Presieve.image_mem_functorPushforward** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Presieve`。
形式化陈述：image_mem_functorPushforward (R : Presieve X) {f : Y ⟶ X} (h : R f) : R.fu
nctorPushforward F (F.map f)
参数：R : Presieve X；h : R f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_mem_functorPushforward (R : Presieve X) {f : Y ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨Y, f, 𝟙 _, h, by simp⟩

/-- This presieve generates `functorPushforward`.
See `arrows_generate_map_eq_functorPushforward`. -/
/-
**CategoryTheory.Presieve.map** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Presie
ve`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) → {X : C} → CategoryTheory.Presieve X → CategoryTheory.
Presieve (F.obj X)
参数：F : CategoryTheory.Functor C D；F.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This presieve generates `functorPushforward`.
See `arrows_generate_map_eq_functorPushforward`.
-/
inductive map (s : Presieve X) : Presieve (F.obj X) where
  | of {Y : C} {u : Y ⟶ X} (h : s u) : map s (F.map u)

section

variable {F}

@[grind ←]
/-
**CategoryTheory.Presieve.map_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pres
ieve`。
形式化陈述：map_map {X Y : C} {f : Y ⟶ X} {R : Presieve X} (hf : R f) : R.map F (F.map
 f)
参数：hf : R f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_map {X Y : C} {f : Y ⟶ X} {R : Presieve X} (hf : R f) : R.map F (F.map f) :=
  ⟨hf⟩
/-
**CategoryTheory.Presieve.map_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pres
ieve`。
形式化陈述：map_iff {X : C} {R : Presieve X} {Y : D} {f : Y ⟶ F.obj X} : R.map F f ↔ e
xists (Z : C) (h : F.obj Z = Y) (g : Z ⟶ X), R g ∧ F.map g = eqToHom h ≫ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `CategoryTheory.Presieve.map_map`：map_map {X Y : C} {f : Y ⟶ X} {R : Pres
ieve X} (hf : R f) : R.map F (F.map f)
-/
lemma map_iff {X : C} {R : Presieve X} {Y : D} {f : Y ⟶ F.obj X} :
    R.map F f ↔ ∃ (Z : C) (h : F.obj Z = Y) (g : Z ⟶ X), R g ∧ F.map g = eqToHom h ≫ f := by
  refine ⟨fun (.of (u := u) hu) ↦ ⟨_, rfl, u, hu, by simp⟩, fun ⟨Z, h, g, hg, heq⟩ ↦ ?_⟩
  subst h
  rw [eqToHom_refl, Category.id_comp] at heq
  simp [← heq, map_map hg]

@[simp]
/-
**CategoryTheory.Presieve.map_ofArrows** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Presieve`。
形式化陈述：map_ofArrows {X : C} {ι : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X) : (o
fArrows Y f).map F = ofArrows _ (fun i => F.map (f i))
参数：f : forall i, Y i ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.ofArrows_surj`：ofArrows_surj {ι : Type*} {Y : ι 
-> C} (f : forall i, Y i ⟶ X) {Z : C} (g : Z ⟶ X) (hg : ofArrows Y f g) : exists
 (i : ι) (h : Y i = Z), g =…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `CategoryTheory.Presieve.map_map`：map_map {X Y : C} {f : Y ⟶ X} {R : Pres
ieve X} (hf : R f) : R.map F (F.map f)
-/
lemma map_ofArrows {X : C} {ι : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ X) :
    (ofArrows Y f).map F = ofArrows _ (fun i ↦ F.map (f i)) := by
  refine le_antisymm (fun Z g hg ↦ ?_) fun _ _ ⟨i⟩ ↦ map_map ⟨i⟩
  obtain ⟨hu⟩ := hg
  obtain ⟨i, rfl, rfl⟩ := Presieve.ofArrows_surj _ _ hu
  simpa using ofArrows.mk i

@[simp]
/-
**CategoryTheory.Presieve.map_singleton** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Presieve`。
形式化陈述：map_singleton {X Y : C} (f : X ⟶ Y) : (singleton f).map F = singleton (F.m
ap f)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.ofArrows_pUnit`：ofArrows_pUnit : (ofArrows _ fun
 _ : PUnit.{w + 1} => f) = singleton f
· 使用引理 `CategoryTheory.Presieve.map_ofArrows`：map_ofArrows {X : C} {ι : Type*} {
Y : ι -> C} (f : forall i, Y i ⟶ X) : (ofArrows Y f).map F = ofArrows _ (fun i =
> F.map (f i))
-/
lemma map_singleton {X Y : C} (f : X ⟶ Y) : (singleton f).map F = singleton (F.map f) := by
  rw [← ofArrows_pUnit.{0}, map_ofArrows, ofArrows_pUnit]
/-
**CategoryTheory.Presieve.map_le_iff_le_functorPullback** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Presieve`。
形式化陈述：map_le_iff_le_functorPullback {R : Presieve X} {S : Presieve (F.obj X)} : 
R.map F <= S ↔ R <= S.functorPullback F
参数：F.obj X。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_le_iff_le_functorPullback {R : Presieve X} {S : Presieve (F.obj X)} :
    R.map F ≤ S ↔ R ≤ S.functorPullback F :=
  ⟨fun h _ _ hf ↦ h _ _ (.of hf), fun h _ f ⟨hu⟩ ↦ h _ _ hu⟩

variable (F) in
/-
**CategoryTheory.Presieve.galoisConnection_map_functorPullback** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：galoisConnection_map_functorPullback (X : C) : GaloisConnection (Presieve.
map F (X
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presieve.map_le_iff_le_functorPullback`：map_le_iff_le_fun
ctorPullback {R : Presieve X} {S : Presieve (F.obj X)} : R.map F <= S ↔ R <= S.f
unctorPullback F
-/
lemma galoisConnection_map_functorPullback (X : C) :
    GaloisConnection (Presieve.map F (X := X)) (Presieve.functorPullback F) :=
  fun _ _ ↦ Presieve.map_le_iff_le_functorPullback
/-
**CategoryTheory.Presieve.map_functorPullback** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Presieve`。
形式化陈述：map_functorPullback {X : C} (R : Presieve (F.obj X)) : (R.functorPullback 
F).map F <= R
参数：R : Presieve (F.obj X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用引理 `CategoryTheory.Presieve.galoisConnection_map_functorPullback`：galoisConn
ection_map_functorPullback (X : C) : GaloisConnection (Presieve.map F (X
-/
lemma map_functorPullback {X : C} (R : Presieve (F.obj X)) : (R.functorPullback F).map F ≤ R :=
  (galoisConnection_map_functorPullback _ _).l_u_le _
/-
**CategoryTheory.Presieve.le_functorPullback_map** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Presieve`。
形式化陈述：le_functorPullback_map {X : C} (R : Presieve X) : R <= (R.map F).functorPu
llback F
参数：R : Presieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用引理 `CategoryTheory.Presieve.galoisConnection_map_functorPullback`：galoisConn
ection_map_functorPullback (X : C) : GaloisConnection (Presieve.map F (X
-/
lemma le_functorPullback_map {X : C} (R : Presieve X) : R ≤ (R.map F).functorPullback F :=
  (galoisConnection_map_functorPullback _ _).le_u_l _

@[simp]
/-
**CategoryTheory.Presieve.map_functorPullback_map** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Presieve`。
形式化陈述：map_functorPullback_map {X : C} (R : Presieve X) : Presieve.map F (Presiev
e.functorPullback F (R.map F)) = R.map F
参数：R : Presieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用引理 `CategoryTheory.Presieve.galoisConnection_map_functorPullback`：galoisConn
ection_map_functorPullback (X : C) : GaloisConnection (Presieve.map F (X
-/
lemma map_functorPullback_map {X : C} (R : Presieve X) :
    Presieve.map F (Presieve.functorPullback F (R.map F)) = R.map F :=
  (galoisConnection_map_functorPullback _ _).l_u_l_eq_l _

@[simp]
/-
**CategoryTheory.Presieve.functorPullback_map_functorPullback** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：functorPullback_map_functorPullback {X : C} (R : Presieve (F.obj X)) : Pre
sieve.functorPullback F (Presieve.map F (R.functorPullback F)) = R.functorPullba
ck F
参数：R : Presieve (F.obj X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用引理 `CategoryTheory.Presieve.galoisConnection_map_functorPullback`：galoisConn
ection_map_functorPullback (X : C) : GaloisConnection (Presieve.map F (X
-/
lemma functorPullback_map_functorPullback {X : C} (R : Presieve (F.obj X)) :
    Presieve.functorPullback F (Presieve.map F (R.functorPullback F)) = R.functorPullback F :=
  (galoisConnection_map_functorPullback _ _).u_l_u_eq_u _

@[simp]
/-
**CategoryTheory.Presieve.map_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presi
eve`。
形式化陈述：map_id {X : C} (R : Presieve X) : R.map (𝟭 C) = R
参数：R : Presieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma map_id {X : C} (R : Presieve X) : R.map (𝟭 C) = R :=
  le_antisymm (fun _ _ ⟨hg⟩ ↦ hg) fun _ _ hg ↦ ⟨hg⟩

@[gcongr]
/-
**CategoryTheory.Presieve.map_monotone** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Presieve`。
形式化陈述：map_monotone : Monotone (map (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用引理 `CategoryTheory.Presieve.galoisConnection_map_functorPullback`：galoisConn
ection_map_functorPullback (X : C) : GaloisConnection (Presieve.map F (X
-/
lemma map_monotone : Monotone (map (X := X) F) :=
  (galoisConnection_map_functorPullback _ _).monotone_l

@[gcongr]
/-
**CategoryTheory.Presieve.functorPullback_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Presieve`。
形式化陈述：functorPullback_monotone {X : C} : Monotone (Presieve.functorPullback (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用引理 `CategoryTheory.Presieve.galoisConnection_map_functorPullback`：galoisConn
ection_map_functorPullback (X : C) : GaloisConnection (Presieve.map F (X
-/
lemma functorPullback_monotone {X : C} : Monotone (Presieve.functorPullback (X := X) F) :=
  (galoisConnection_map_functorPullback F X).monotone_u

@[simp]
/-
**CategoryTheory.Presieve.map_bot** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pres
ieve`。
形式化陈述：map_bot : map F (⊥ : Presieve X) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用引理 `CategoryTheory.Presieve.galoisConnection_map_functorPullback`：galoisConn
ection_map_functorPullback (X : C) : GaloisConnection (Presieve.map F (X
-/
lemma map_bot : map F (⊥ : Presieve X) = ⊥ :=
  (galoisConnection_map_functorPullback _ _).l_bot

end

end FunctorPushforward

section uncurry

variable (s : Presieve X)

/-- Uncurry a presieve to one set over the sigma type. -/
/-
**CategoryTheory.Presieve.uncurry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pres
ieve`。
形式化陈述：uncurry : Set (Σ Y, Y ⟶ X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uncurry a presieve to one set over the sigma type.
-/
def uncurry : Set (Σ Y, Y ⟶ X) :=
  { u | s u.snd }
/-
**CategoryTheory.Presieve.uncurry_singleton** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Presieve`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (u :
 Y ⟶ X),   (CategoryTheory.Presieve.singleton u).uncurry = {⟨Y, u⟩}
参数：u : Y ⟶ X；CategoryTheory.Presieve.singleton u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.ext_iff`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x = y ↔ 
x.fst = y.fst ∧ x.snd ≍ y.snd
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
@[simp] theorem uncurry_singleton {Y : C} (u : Y ⟶ X) : (singleton u).uncurry = { ⟨Y, u⟩ } := by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨⟩; rfl
  · intro h
    rw [Set.mem_singleton_iff, Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h; subst h; constructor
/-
**CategoryTheory.Presieve.uncurry_pullbackArrows** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Presieve`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (s : C
ategoryTheory.Presieve X)   [inst_1 : CategoryTheory.Limits.HasPullbacks C] {B :
 C} (b : B ⟶ X),   (CategoryTheory.Presieve.pullbackArrows b s).uncurry =     (f
un f => ⟨CategoryTheory.Limits.pullback f.snd b, CategoryTheory.Limits.pullback.
snd f.snd b⟩) '' s.uncurry
参数：s : CategoryTheory.Presieve X；b : B ⟶ X；CategoryTheory.Presieve.pullbackArrow
s b s；fun f => ⟨CategoryTheory.Limits.pullback f.snd b, CategoryTheory.Limits.pu
llback.snd f.snd b⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.Presieve.instHasPullbacksOfHasPullbacks`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} [CategoryTheory.Limits.HasPu
llbacks C]   (R : CategoryTheory.Presieve X)…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Presieve.hasPullback`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Presieve X} {Y : C} (f : Y 
⟶ X)   [self : R.HasPullb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.ext_iff`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x = y ↔ 
x.fst = y.fst ∧ x.snd ≍ y.snd
· 使用定理 `heq_iff_eq`：∀ {α : Sort u_1} {a b : α}, a ≍ b ↔ a = b
-/
@[simp] theorem uncurry_pullbackArrows [HasPullbacks C] {B : C} (b : B ⟶ X) :
    (pullbackArrows b s).uncurry =
      (fun f ↦ ⟨Limits.pullback f.2 b, pullback.snd _ _⟩) '' s.uncurry := by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨Y, u, hu⟩; exact ⟨⟨Y, u⟩, hu, rfl⟩
  · rintro ⟨⟨Y, u⟩, hu, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    exact ⟨Y, u, hu⟩
/-
**CategoryTheory.Presieve.uncurry_bind** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Presieve`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (s : C
ategoryTheory.Presieve X)   (t : ⦃Y : C⦄ → (f : Y ⟶ X) → s f → CategoryTheory.Pr
esieve Y),   (s.bind t).uncurry =     ⋃ i,       ⋃ (h : i ∈ s.uncurry), (Sigma.m
ap id fun Z g => CategoryTheory.CategoryStruct.comp g i.snd) '' (t i.snd h).uncu
rry
参数：s : CategoryTheory.Presieve X；t : ⦃Y : C⦄ → (f : Y ⟶ X) → s f → CategoryTheor
y.Presieve Y；s.bind t；h : i ∈ s.uncurry；Sigma.map id fun Z g => CategoryTheory.C
ategoryStruct.comp g i.snd；t i.snd h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Sigma.ext`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x.fst = y.fs
t → x.snd ≍ y.snd → x = y
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Sigma.ext_iff`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x = y ↔ 
x.fst = y.fst ∧ x.snd ≍ y.snd
· 使用定理 `heq_iff_eq`：∀ {α : Sort u_1} {a b : α}, a ≍ b ↔ a = b
-/
@[simp] theorem uncurry_bind (t : ⦃Y : C⦄ → (f : Y ⟶ X) → s f → Presieve Y) :
    (s.bind t).uncurry = ⋃ i ∈ s.uncurry,
      Sigma.map id (fun Z g ↦ (g ≫ i.2 : Z ⟶ X)) '' (t i.2 ‹_›).uncurry := by
  ext ⟨Z, v⟩; simp only [Set.mem_iUnion, Set.mem_image]; constructor
  · rintro ⟨Y, g, f, hf, ht, hv⟩
    exact ⟨⟨_, f⟩, hf, ⟨_, g⟩, ht, Sigma.ext rfl (heq_of_eq hv)⟩
  · rintro ⟨⟨_, f⟩, hf, ⟨Y, g⟩, hg, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    exact ⟨_, _, _, _, hg, rfl⟩
/-
**CategoryTheory.Presieve.uncurry_ofArrows** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Presieve`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} {ι : T
ype u_1} (Y : ι → C) (f : (i : ι) → Y i ⟶ X),   (CategoryTheory.Presieve.ofArrow
s Y f).uncurry = Set.range fun i => ⟨Y i, f i⟩
参数：Y : ι → C；f : (i : ι) → Y i ⟶ X；CategoryTheory.Presieve.ofArrows Y f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
@[simp] theorem uncurry_ofArrows {ι : Type*} (Y : ι → C) (f : (i : ι) → Y i ⟶ X) :
    (ofArrows Y f).uncurry = Set.range fun i : ι ↦ ⟨_, f i⟩ := by
  ext ⟨Z, v⟩; simp only [Set.mem_range, Sigma.mk.injEq]; constructor
  · rintro ⟨i⟩; exact ⟨_, rfl, HEq.refl _⟩
  · rintro ⟨i, rfl, h⟩; rw [← eq_of_heq h]; exact ⟨i⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Presieve.ofArrows_eq_ofArrows_uncurry** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Presieve`。
形式化陈述：ofArrows_eq_ofArrows_uncurry {ι : Type*} {S : C} {X : ι -> C} (f : forall 
i, X i ⟶ S) : ofArrows X f = ofArrows _ (fun i : (Presieve.ofArrows X f).uncurry
 => f i.2.idx)
参数：f : forall i, X i ⟶ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.Presieve.ofArrows.mk'`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} {ι : Type u_1} {Y : ι → C} {f : (i : ι) → Y i 
⟶ X}   {Z : C} {g : Z ⟶ X}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.ofArrows.obj_idx`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {ι : Type u_1} {S : C} {X : ι → C} {f : (i : ι) → 
X i ⟶ S}   {Y : C} {g : Y ⟶ S}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Presieve.ofArrows.hom_idx`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {ι : Type u_1} {S : C} {X : ι → C} {f : (i : ι) → 
X i ⟶ S}   {Y : C} {g : Y ⟶ S}…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma ofArrows_eq_ofArrows_uncurry {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) :
    ofArrows X f = ofArrows _ (fun i : (Presieve.ofArrows X f).uncurry ↦ f i.2.idx) := by
  refine le_antisymm (fun Z g hg ↦ ?_) fun Z g ⟨i⟩ ↦ .mk _
  exact .mk' ⟨⟨_, _⟩, hg⟩ (by simp [ofArrows.obj_idx]) (by simp [ofArrows.hom_idx])

end uncurry

end Presieve

/--
For an object `X` of a category `C`, a `Sieve X` is a predicate on morphisms to `X` which is closed
under left-composition.
-/
/-
**CategoryTheory.Sieve** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} → [CategoryTheory.Category.{v₁, u₁} C] → C → Type (max u₁ v₁
)
参数：max u₁ v₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an object `X` of a category `C`, a `Sieve X` is a predicate on morphisms to 
`X` which is closed
under left-composition.
-/
structure Sieve {C : Type u₁} [Category.{v₁} C] (X : C) where
  /-- the underlying presieve -/
  arrows : Presieve X
  /-- stability by precomposition -/
  downward_closed : ∀ {Y Z f} (_ : arrows f) (g : Z ⟶ Y), arrows (g ≫ f)

namespace Sieve

/-
**CategoryTheory.Sieve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (Sieve X) fun _ => Presieve X :=
  ⟨Sieve.arrows⟩

initialize_simps_projections Sieve (arrows → apply)

variable {S R : Sieve X}

attribute [simp] downward_closed
/-
**CategoryTheory.Sieve.arrows_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Siev
e`。
形式化陈述：arrows_ext : forall {R S : Sieve X}, R.arrows = S.arrows -> R = S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrows_ext : ∀ {R S : Sieve X}, R.arrows = S.arrows → R = S := by
  rintro ⟨_, _⟩ ⟨_, _⟩ rfl
  rfl

@[ext]
/-
**CategoryTheory.Sieve.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} {R S :
 CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), R.arrows f ↔ S.arrows f) → R
 = S
参数：∀ ⦃Y : C⦄ (f : Y ⟶ X), R.arrows f ↔ S.arrows f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.arrows_ext`：arrows_ext : forall {R S : Sieve X}, R.
arrows = S.arrows -> R = S
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem ext {R S : Sieve X} (h : ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) : R = S :=
  arrows_ext <| funext fun _ => funext fun f => propext <| h f

open Lattice

/-- The supremum of a collection of sieves: the union of them all. -/
/-
**CategoryTheory.Sieve.sup** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {X : C} → 
Set (CategoryTheory.Sieve X) → CategoryTheory.Sieve X
参数：CategoryTheory.Sieve X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supremum of a collection of sieves: the union of them all.
-/
protected def sup (𝒮 : Set (Sieve X)) : Sieve X where
  arrows _ f := ∃ S ∈ 𝒮, Sieve.arrows S f
  downward_closed {_ _ f} hf _ := by
    obtain ⟨S, hS, hf⟩ := hf
    exact ⟨S, hS, S.downward_closed hf _⟩

/-- The infimum of a collection of sieves: the intersection of them all. -/
/-
**CategoryTheory.Sieve.inf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {X : C} → 
Set (CategoryTheory.Sieve X) → CategoryTheory.Sieve X
参数：CategoryTheory.Sieve X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of a collection of sieves: the intersection of them all.
-/
protected def inf (𝒮 : Set (Sieve X)) : Sieve X where
  arrows _ f := ∀ S ∈ 𝒮, Sieve.arrows S f
  downward_closed {_ _ _} hf g S H := S.downward_closed (hf S H) g

/-- The union of two sieves is a sieve. -/
/-
**CategoryTheory.Sieve.union** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X : C
} → CategoryTheory.Sieve X → CategoryTheory.Sieve X → CategoryTheory.Sieve X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union of two sieves is a sieve.
-/
protected def union (S R : Sieve X) : Sieve X where
  arrows _ f := S f ∨ R f
  downward_closed := by rintro _ _ _ (h | h) g <;> simp [h]

/-- The intersection of two sieves is a sieve. -/
/-
**CategoryTheory.Sieve.inter** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X : C
} → CategoryTheory.Sieve X → CategoryTheory.Sieve X → CategoryTheory.Sieve X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intersection of two sieves is a sieve.
-/
protected def inter (S R : Sieve X) : Sieve X where
  arrows _ f := S f ∧ R f
  downward_closed := by
    rintro _ _ _ ⟨h₁, h₂⟩ g
    simp [h₁, h₂]

/-- Sieves on an object `X` form a complete lattice.
We generate this directly rather than using the Galois insertion for nicer definitional properties.
-/
/-
**CategoryTheory.Sieve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sieves on an object `X` form a complete lattice.
We generate this directly rather than using the Galois insertion for nicer defin
itional properties.
-/
instance : CompleteLattice (Sieve X) where
  le S R := ∀ ⦃Y⦄ (f : Y ⟶ X), S f → R f
  le_refl _ _ _ := id
  le_trans _ _ _ S₁₂ S₂₃ _ _ h := S₂₃ _ (S₁₂ _ h)
  le_antisymm _ _ p q := Sieve.ext fun _ _ => ⟨p _, q _⟩
  top :=
    { arrows := ⊤
      downward_closed := fun _ _ => ⟨⟩ }
  bot :=
    { arrows := ⊥
      downward_closed := False.elim }
  sup := Sieve.union
  inf := Sieve.inter
  sSup := Sieve.sup
  sInf := Sieve.inf
  isLUB_sSup _ := ⟨fun S hS _ _ hf ↦ ⟨S, hS, hf⟩, fun _ ha _ _ ⟨b, hb, hf⟩ ↦ ha hb _ hf⟩
  isGLB_sInf _ := ⟨fun S hS _ _ h ↦ h _ hS, fun _ hS _ _ hf _ hR ↦ hS hR _ hf⟩
  le_sup_left _ _ _ _ := Or.inl
  le_sup_right _ _ _ _ := Or.inr
  sup_le _ _ _ h₁ h₂ _ f := by
    rintro (hf | hf)
    · exact h₁ _ hf
    · exact h₂ _ hf
  inf_le_left _ _ _ _ := And.left
  inf_le_right _ _ _ _ := And.right
  le_inf _ _ _ p q _ _ z := ⟨p _ z, q _ z⟩
  le_top _ _ _ _ := trivial
  bot_le _ _ _ := False.elim

/-- The maximal sieve always exists. -/
/-
**CategoryTheory.Sieve.sieveInhabited** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Sieve`。
形式化陈述：sieveInhabited : Inhabited (Sieve X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal sieve always exists.
-/
instance sieveInhabited : Inhabited (Sieve X) :=
  ⟨⊤⟩

@[simp]
/-
**CategoryTheory.Sieve.sInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Siev
e`。
形式化陈述：sInf_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) : sInf Ss f ↔ forall (S : 
Sieve X) (_ : S in Ss), S f
参数：Sieve X；f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sInf_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sInf Ss f ↔ ∀ (S : Sieve X) (_ : S ∈ Ss), S f :=
  Iff.rfl

@[simp]
/-
**CategoryTheory.Sieve.sSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Siev
e`。
形式化陈述：sSup_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) : sSup Ss f ↔ exists (S : 
Sieve X) (_ : S in Ss), S f
参数：Sieve X；f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sSup_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sSup Ss f ↔ ∃ (S : Sieve X) (_ : S ∈ Ss), S f := by
  simp [sSup, Sieve.sup]

@[simp]
/-
**CategoryTheory.Sieve.inter_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sie
ve`。
形式化陈述：inter_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊓ S) f ↔ R f ∧ S f
参数：f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inter_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊓ S) f ↔ R f ∧ S f :=
  Iff.rfl

@[simp]
/-
**CategoryTheory.Sieve.union_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sie
ve`。
形式化陈述：union_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊔ S) f ↔ R f ∨ S f
参数：f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem union_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊔ S) f ↔ R f ∨ S f :=
  Iff.rfl
/-
**CategoryTheory.Sieve.top_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sieve
`。
形式化陈述：top_apply (f : Y ⟶ X) : (⊤ : Sieve X) f
参数：f : Y ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem top_apply (f : Y ⟶ X) : (⊤ : Sieve X) f :=
  trivial

@[simp]
/-
**CategoryTheory.Sieve.bot_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sieve
`。
形式化陈述：bot_apply (f : Y ⟶ X) : (⊥ : Sieve X) f ↔ False
参数：f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bot_apply (f : Y ⟶ X) : (⊥ : Sieve X) f ↔ False :=
  .rfl

@[simp]
/-
**CategoryTheory.Sieve.arrows_top** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Siev
e`。
形式化陈述：arrows_top : (⊤ : Sieve X).arrows = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma arrows_top : (⊤ : Sieve X).arrows = ⊤ := rfl
/-
**CategoryTheory.Sieve.arrows_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：arrows_eq_top_iff {S : Sieve X} : S.arrows = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.arrows_ext`：arrows_ext : forall {R S : Sieve X}, R.
arrows = S.arrows -> R = S
· 使用引理 `CategoryTheory.Sieve.arrows_top`：arrows_top : (⊤ : Sieve X).arrows = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma arrows_eq_top_iff {S : Sieve X} : S.arrows = ⊤ ↔ S = ⊤ :=
  ⟨fun h ↦ arrows_ext (h ▸ arrows_top), fun h ↦ h ▸ arrows_top⟩

@[simp]
/-
**CategoryTheory.Sieve.arrows_bot** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Siev
e`。
形式化陈述：arrows_bot : (⊥ : Sieve X).arrows = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma arrows_bot : (⊥ : Sieve X).arrows = ⊥ := rfl
/-
**CategoryTheory.Sieve.arrows_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：arrows_eq_bot_iff {S : Sieve X} : S.arrows = ⊥ ↔ S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.arrows_ext`：arrows_ext : forall {R S : Sieve X}, R.
arrows = S.arrows -> R = S
· 使用引理 `CategoryTheory.Sieve.arrows_bot`：arrows_bot : (⊥ : Sieve X).arrows = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma arrows_eq_bot_iff {S : Sieve X} : S.arrows = ⊥ ↔ S = ⊥ :=
  ⟨fun h ↦ arrows_ext (h ▸ arrows_bot), fun h ↦ h ▸ arrows_bot⟩
/-
**CategoryTheory.Sieve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial (Sieve X) where
  exists_pair_ne := ⟨⊤, ⊥, fun h ↦ by simp [← bot_apply (𝟙 X), ← h]⟩

/-- Generate the smallest sieve containing the given presieve. -/
@[simps]
/-
**CategoryTheory.Sieve.generate** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve`
。
形式化陈述：generate (R : Presieve X) : Sieve X where arrows Z f
参数：R : Presieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generate the smallest sieve containing the given presieve.
-/
def generate (R : Presieve X) : Sieve X where
  arrows Z f := ∃ (Y : _) (h : Z ⟶ Y) (g : Y ⟶ X), R g ∧ h ≫ g = f
  downward_closed := by
    rintro Y Z _ ⟨W, g, f, hf, rfl⟩ h
    exact ⟨_, h ≫ g, _, hf, by simp⟩
/-
**CategoryTheory.Sieve.arrows_generate_map_eq_functorPushforward** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：arrows_generate_map_eq_functorPushforward {s : Presieve X} : (generate (s.
map F)).arrows = s.functorPushforward F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem arrows_generate_map_eq_functorPushforward {s : Presieve X} :
    (generate (s.map F)).arrows = s.functorPushforward F := by
  refine funext fun Z ↦ funext fun u ↦ propext ⟨?_, ?_⟩
  · rintro ⟨_, _, _, ⟨hu⟩, rfl⟩; exact ⟨_, _, _, hu, rfl⟩
  · rintro ⟨_, _, _, hu, rfl⟩; exact ⟨_, _, _, ⟨hu⟩, rfl⟩

/-- Given a presieve on `X`, and a sieve on each domain of an arrow in the presieve, we can bind to
produce a sieve on `X`.
-/
@[simps]
/-
**CategoryTheory.Sieve.bind** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：bind (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) : Sieve
 X where arrows
参数：S : Presieve X；R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presieve on `X`, and a sieve on each domain of an arrow in the presieve,
 we can bind to
produce a sieve on `X`.
-/
def bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) : Sieve X where
  arrows := S.bind fun _ _ h => R h
  downward_closed := by
    rintro Y Z f ⟨W, f, h, hh, hf, rfl⟩ g
    exact ⟨_, g ≫ f, _, hh, by simp [hf]⟩

/-- Structure which contains the data and properties for a morphism `h` satisfying
`Sieve.bind S R h`. -/
/-
**CategoryTheory.Sieve.BindStruct** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Si
eve`。
形式化陈述：BindStruct (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) {
Z : C} (h : Z ⟶ X)
参数：S : Presieve X；R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y；h : Z ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure which contains the data and properties for a morphism `h` satisfying
`Sieve.bind S R h`.
-/
abbrev BindStruct (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y)
    {Z : C} (h : Z ⟶ X) :=
  Presieve.BindStruct S (fun _ _ hf ↦ R hf) h

open Order Lattice
/-
**CategoryTheory.Sieve.generate_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Sieve`。
形式化陈述：generate_le_iff (R : Presieve X) (S : Sieve X) : generate R <= S ↔ R <= S
参数：R : Presieve X；S : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
-/
theorem generate_le_iff (R : Presieve X) (S : Sieve X) : generate R ≤ S ↔ R ≤ S :=
  ⟨fun H _ _ hg => H _ ⟨_, 𝟙 _, _, hg, id_comp _⟩, fun ss Y f => by
    rintro ⟨Z, f, g, hg, rfl⟩
    exact S.downward_closed (ss Z _ hg) f⟩

/-- Show that there is a Galois insertion (generate, underlying presieve). -/
/-
**CategoryTheory.Sieve.giGenerate** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Siev
e`。
形式化陈述：giGenerate : GaloisInsertion (generate : Presieve X -> Sieve X) arrows whe
re gc
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.generate_le_iff`：generate_le_iff (R : Presieve X) (
S : Sieve X) : generate R <= S ↔ R <= S

--- 原说明 ---
Show that there is a Galois insertion (generate, underlying presieve).
-/
def giGenerate : GaloisInsertion (generate : Presieve X → Sieve X) arrows where
  gc := generate_le_iff
  choice 𝒢 _ := generate 𝒢
  choice_eq _ _ := rfl
  le_l_u _ _ _ hf := ⟨_, 𝟙 _, _, hf, id_comp _⟩
/-
**CategoryTheory.Sieve.le_generate** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sie
ve`。
形式化陈述：le_generate (R : Presieve X) : R <= generate R
参数：R : Presieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem le_generate (R : Presieve X) : R ≤ generate R :=
  giGenerate.gc.le_u_l R

@[simp]
/-
**CategoryTheory.Sieve.generate_sieve** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Sieve`。
形式化陈述：generate_sieve (S : Sieve X) : generate S = S
参数：S : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
-/
theorem generate_sieve (S : Sieve X) : generate S = S :=
  giGenerate.l_u_eq S

@[gcongr]
/-
**CategoryTheory.Sieve.generate_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ieve`。
形式化陈述：generate_mono : Monotone (generate : Presieve X -> Sieve X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem generate_mono : Monotone (generate : Presieve X → Sieve X) := giGenerate.gc.monotone_l

@[gcongr]
/-
**CategoryTheory.Sieve.arrows_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sie
ve`。
形式化陈述：arrows_mono : Monotone (arrows : Sieve X -> Presieve X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem arrows_mono : Monotone (arrows : Sieve X → Presieve X) := giGenerate.gc.monotone_u

/-- If the identity arrow is in a sieve, the sieve is maximal. -/
/-
**CategoryTheory.Sieve.id_mem_iff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：id_mem_iff_eq_top : S (𝟙 X) ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the identity arrow is in a sieve, the sieve is maximal.
-/
theorem id_mem_iff_eq_top : S (𝟙 X) ↔ S = ⊤ :=
  ⟨fun h => top_unique fun Y f _ => by simpa using downward_closed _ h f, fun h => h.symm ▸ trivial⟩

/-- If a presieve contains a split epi, it generates the maximal sieve. -/
/-
**CategoryTheory.Sieve.generate_of_contains_isSplitEpi** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Sieve`。
形式化陈述：generate_of_contains_isSplitEpi {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f
] (hf : R f) : generate R = ⊤
参数：f : Y ⟶ X；hf : R f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.id_mem_iff_eq_top`：id_mem_iff_eq_top : S (𝟙 X) ↔ S 
= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsSplitEpi.id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   Ca
tegoryTheory.Categ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a presieve contains a split epi, it generates the maximal sieve.
-/
theorem generate_of_contains_isSplitEpi {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f) :
    generate R = ⊤ := by
  rw [← id_mem_iff_eq_top]
  exact ⟨_, section_ f, f, hf, by simp⟩

@[simp]
/-
**CategoryTheory.Sieve.generate_of_singleton_isSplitEpi** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Sieve`。
形式化陈述：generate_of_singleton_isSplitEpi (f : Y ⟶ X) [IsSplitEpi f] : generate (Pr
esieve.singleton f) = ⊤
参数：f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.generate_of_contains_isSplitEpi`：generate_of_contai
ns_isSplitEpi {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f) : generate 
R = ⊤
· 使用定理 `CategoryTheory.Presieve.singleton_self`：singleton_self : singleton f f
-/
theorem generate_of_singleton_isSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    generate (Presieve.singleton f) = ⊤ :=
  generate_of_contains_isSplitEpi f (Presieve.singleton_self _)

@[simp]
/-
**CategoryTheory.Sieve.generate_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Si
eve`。
形式化陈述：generate_top : generate (⊤ : Presieve X) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.generate_of_contains_isSplitEpi`：generate_of_contai
ns_isSplitEpi {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f) : generate 
R = ⊤
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
-/
theorem generate_top : generate (⊤ : Presieve X) = ⊤ :=
  generate_of_contains_isSplitEpi (𝟙 _) ⟨⟩

@[simp]
/-
**CategoryTheory.Sieve.generate_bot** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Si
eve`。
形式化陈述：generate_bot : generate (⊥ : Presieve X) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma generate_bot : generate (⊥ : Presieve X) = ⊥ := by
  simp only [eq_bot_iff, generate_le_iff, bot_le]

@[simp]
/-
**CategoryTheory.Sieve.generate_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Sieve`。
形式化陈述：generate_eq_bot_iff (R : Presieve X) : generate R = ⊥ ↔ R = ⊥
参数：R : Presieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaloisConnection.l_eq_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOr
der α] [inst_1 : Preorder β] [inst_2 : OrderBot α] {u : α → β} {l : β → α},   Ga
loisConnection …
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma generate_eq_bot_iff (R : Presieve X) : generate R = ⊥ ↔ R = ⊥ := by
  simp [giGenerate.gc.l_eq_bot]

@[simp]
/-
**CategoryTheory.Sieve.comp_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Si
eve`。
形式化陈述：comp_mem_iff (i : X ⟶ Y) (f : Y ⟶ Z) [IsIso i] (S : Sieve Z) : S (i ≫ f) ↔
 S f
参数：i : X ⟶ Y；f : Y ⟶ Z；S : Sieve Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
-/
lemma comp_mem_iff (i : X ⟶ Y) (f : Y ⟶ Z) [IsIso i] (S : Sieve Z) :
    S (i ≫ f) ↔ S f := by
  refine ⟨fun H ↦ ?_, fun H ↦ S.downward_closed H _⟩
  convert! S.downward_closed H (inv i)
  simp

section

variable {I : Type*} {X : C} (Y : I → C) (f : ∀ i, Y i ⟶ X)

/-- The sieve of `X` generated by family of morphisms `Y i ⟶ X`. -/
/-
**CategoryTheory.Sieve.ofArrows** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Siev
e`。
形式化陈述：ofArrows : Sieve X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sieve of `X` generated by family of morphisms `Y i ⟶ X`.
-/
abbrev ofArrows : Sieve X := generate (Presieve.ofArrows Y f)
/-
**CategoryTheory.Sieve.ofArrows_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sie
ve`。
形式化陈述：ofArrows_mk (i : I) : ofArrows Y f (f i)
参数：i : I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofArrows_mk (i : I) : ofArrows Y f (f i) :=
  ⟨_, 𝟙 _, _, ⟨i⟩, by simp⟩
/-
**CategoryTheory.Sieve.mem_ofArrows_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Sieve`。
形式化陈述：mem_ofArrows_iff {W : C} (g : W ⟶ X) : ofArrows Y f g ↔ exists (i : I) (a 
: W ⟶ Y i), g = a ≫ f i
参数：g : W ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用引理 `CategoryTheory.Sieve.ofArrows_mk`：ofArrows_mk (i : I) : ofArrows Y f (f 
i)
-/
lemma mem_ofArrows_iff {W : C} (g : W ⟶ X) :
    ofArrows Y f g ↔ ∃ (i : I) (a : W ⟶ Y i), g = a ≫ f i := by
  constructor
  · rintro ⟨T, a, b, ⟨i⟩, rfl⟩
    exact ⟨i, a, rfl⟩
  · rintro ⟨i, a, rfl⟩
    apply downward_closed _ (ofArrows_mk Y f i)

variable {Y f} {W : C} {g : W ⟶ X} (hg : ofArrows Y f g)

include hg in
/-
**CategoryTheory.Sieve.ofArrows.exists** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Sieve.ofArrows`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {I : Type u_1}
 {X : C} {Y : I → C} {f : (i : I) → Y i ⟶ X}   {W : C} {g : W ⟶ X},   (CategoryT
heory.Sieve.ofArrows Y f).arrows g → ∃ i h, g = CategoryTheory.CategoryStruct.co
mp h (f i)
参数：i : I；CategoryTheory.Sieve.ofArrows Y f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma ofArrows.exists : ∃ (i : I) (h : W ⟶ Y i), g = h ≫ f i := by
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hg
  exact ⟨i, h, rfl⟩

/-- When `hg : Sieve.ofArrows Y f g`, this is a choice of `i` such that `g`
factors through `f i`. -/
/-
**CategoryTheory.Sieve.ofArrows.i** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Siev
e.ofArrows`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {I : T
ype u_1} →       {X : C} →         {Y : I → C} → {f : (i : I) → Y i ⟶ X} → {W : 
C} → {g : W ⟶ X} → (CategoryTheory.Sieve.ofArrows Y f).arrows g → I
参数：i : I；CategoryTheory.Sieve.ofArrows Y f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ofArrows.exists`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {I : Type u_1} {X : C} {Y : I → C} {f : (i : I) → Y i 
⟶ X}   {W : C} {g : W ⟶ X}…

--- 原说明 ---
When `hg : Sieve.ofArrows Y f g`, this is a choice of `i` such that `g`
factors through `f i`.
-/
noncomputable def ofArrows.i : I := (ofArrows.exists hg).choose

/-- When `hg : Sieve.ofArrows Y f g`, this is a morphism `h : W ⟶ Y (i hg)` such
that `h ≫ f (i hg) = g`. -/
/-
**CategoryTheory.Sieve.ofArrows.h** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Siev
e.ofArrows`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {I : T
ype u_1} →       {X : C} →         {Y : I → C} →           {f : (i : I) → Y i ⟶ 
X} →             {W : C} →               {g : W ⟶ X} →                 (hg : (Ca
tegoryTheory.Sieve.ofArrows Y f).arrows g) → W ⟶ Y (CategoryTheory.Sieve.ofArrow
s.i hg)
参数：i : I；hg : (CategoryTheory.Sieve.ofArrows Y f).arrows g；CategoryTheory.Sieve.
ofArrows.i hg。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ofArrows.exists`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {I : Type u_1} {X : C} {Y : I → C} {f : (i : I) → Y i 
⟶ X}   {W : C} {g : W ⟶ X}…

--- 原说明 ---
When `hg : Sieve.ofArrows Y f g`, this is a morphism `h : W ⟶ Y (i hg)` such
that `h ≫ f (i hg) = g`.
-/
noncomputable def ofArrows.h : W ⟶ Y (i hg) := (ofArrows.exists hg).choose_spec.choose

@[reassoc (attr := simp)]
/-
**CategoryTheory.Sieve.ofArrows.fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Si
eve.ofArrows`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {I : Type u_1}
 {X : C} {Y : I → C} {f : (i : I) → Y i ⟶ X}   {W : C} {g : W ⟶ X} (hg : (Catego
ryTheory.Sieve.ofArrows Y f).arrows g),   CategoryTheory.CategoryStruct.comp (Ca
tegoryTheory.Sieve.ofArrows.h hg) (f (CategoryTheory.Sieve.ofArrows.i hg)) = g
参数：i : I；hg : (CategoryTheory.Sieve.ofArrows Y f).arrows g；CategoryTheory.Sieve.
ofArrows.h hg；f (CategoryTheory.Sieve.ofArrows.i hg)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.ofArrows.exists`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {I : Type u_1} {X : C} {Y : I → C} {f : (i : I) → Y i 
⟶ X}   {W : C} {g : W ⟶ X}…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma ofArrows.fac : h hg ≫ f (i hg) = g :=
  (ofArrows.exists hg).choose_spec.choose_spec.symm

end

/-- The sieve generated by the morphisms in `R.category`
for a presieve `R` is the sieve generated by `R`. -/
/-
**CategoryTheory.Sieve.ofArrows_category'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Sieve`。
形式化陈述：ofArrows_category' {S : C} (R : Presieve S) : Sieve.ofArrows _ (fun (f : R
.category) => f.obj.hom) = generate R
参数：R : Presieve S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.generate_le_iff`：generate_le_iff (R : Presieve X) (
S : Sieve X) : generate R <= S ↔ R <= S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
The sieve generated by the morphisms in `R.category`
for a presieve `R` is the sieve generated by `R`.
-/
lemma ofArrows_category' {S : C} (R : Presieve S) :
    Sieve.ofArrows _ (fun (f : R.category) ↦ f.obj.hom) = generate R := by
  refine le_antisymm ?_ ?_
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨f, hf⟩
    exact ⟨_, 𝟙 _, f.hom, hf, by simp⟩
  · rintro _ _ ⟨_, a, b, h, rfl⟩
    exact ⟨_, _, _, .mk (ι := R.category) ⟨Over.mk b, h⟩, rfl⟩
/-
**CategoryTheory.Sieve.ofArrows_category** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：ofArrows_category {S : C} (R : Sieve S) : Sieve.ofArrows _ (fun (f : R.arr
ows.category) => f.obj.hom) = R
参数：R : Sieve S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.ofArrows_category'`：ofArrows_category' {S : C} (R :
 Presieve S) : Sieve.ofArrows _ (fun (f : R.category) => f.obj.hom) = generate R
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
-/
lemma ofArrows_category {S : C} (R : Sieve S) :
    Sieve.ofArrows _ (fun (f : R.arrows.category) ↦ f.obj.hom) = R := by
  rw [ofArrows_category', generate_sieve]
/-
**CategoryTheory.Sieve.exists_eq_ofArrows** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Sieve`。
形式化陈述：exists_eq_ofArrows (R : Sieve X) : exists (I : Type max u₁ v₁) (Y : I -> C
) (f : forall i, Y i ⟶ X), R = Sieve.ofArrows _ f
参数：R : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Sieve.ofArrows_category`：ofArrows_category {S : C} (R : S
ieve S) : Sieve.ofArrows _ (fun (f : R.arrows.category) => f.obj.hom) = R
-/
lemma exists_eq_ofArrows (R : Sieve X) :
    ∃ (I : Type max u₁ v₁) (Y : I → C) (f : ∀ i, Y i ⟶ X),
      R = Sieve.ofArrows _ f :=
  ⟨_, _, _, (ofArrows_category R).symm⟩

/-- The sieve generated by two morphisms. -/
/-
**CategoryTheory.Sieve.ofTwoArrows** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.S
ieve`。
形式化陈述：ofTwoArrows {U V X : C} (i : U ⟶ X) (j : V ⟶ X) : Sieve X
参数：i : U ⟶ X；j : V ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sieve generated by two morphisms.
-/
abbrev ofTwoArrows {U V X : C} (i : U ⟶ X) (j : V ⟶ X) : Sieve X :=
  Sieve.ofArrows (Y := pairFunction U V) (fun k ↦ WalkingPair.casesOn k i j)

/-- The sieve of `X : C` that is generated by a family of objects `Y : I → C`:
it consists of morphisms `p : Z ⟶ X` such that there exists a morphism `Z ⟶ Y i`
for some `i` (note that this does not depend on `p`, only on the object `Z`). -/
/-
**CategoryTheory.Sieve.ofObjects** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve
`。
形式化陈述：ofObjects {I : Type*} (Y : I -> C) (X : C) : Sieve X where arrows Z _
参数：Y : I -> C；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sieve of `X : C` that is generated by a family of objects `Y : I → C`:
it consists of morphisms `p : Z ⟶ X` such that there exists a morphism `Z ⟶ Y i`
for some `i` (note that this does not depend on `p`, only on the object `Z`).
-/
def ofObjects {I : Type*} (Y : I → C) (X : C) : Sieve X where
  arrows Z _ := ∃ (i : I), Nonempty (Z ⟶ Y i)
  downward_closed := by
    rintro Z₁ Z₂ p ⟨i, ⟨f⟩⟩ g
    exact ⟨i, ⟨g ≫ f⟩⟩
/-
**CategoryTheory.Sieve.mem_ofObjects_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：mem_ofObjects_iff {I : Type*} (Y : I -> C) {Z X : C} (g : Z ⟶ X) : ofObjec
ts Y X g ↔ exists (i : I), Nonempty (Z ⟶ Y i)
参数：Y : I -> C；g : Z ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_ofObjects_iff {I : Type*} (Y : I → C) {Z X : C} (g : Z ⟶ X) :
    ofObjects Y X g ↔ ∃ (i : I), Nonempty (Z ⟶ Y i) := by rfl
/-
**CategoryTheory.Sieve.ofArrows_le_ofObjects** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Sieve`。
形式化陈述：ofArrows_le_ofObjects {I : Type*} (Y : I -> C) {X : C} (f : forall i, Y i 
⟶ X) : Sieve.ofArrows Y f <= Sieve.ofObjects Y X
参数：Y : I -> C；f : forall i, Y i ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.mem_ofArrows_iff`：mem_ofArrows_iff {W : C} (g : W ⟶
 X) : ofArrows Y f g ↔ exists (i : I) (a : W ⟶ Y i), g = a ≫ f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ofArrows_le_ofObjects
    {I : Type*} (Y : I → C) {X : C} (f : ∀ i, Y i ⟶ X) :
    Sieve.ofArrows Y f ≤ Sieve.ofObjects Y X := by
  intro W g hg
  rw [mem_ofArrows_iff] at hg
  obtain ⟨i, a, rfl⟩ := hg
  exact ⟨i, ⟨a⟩⟩
/-
**CategoryTheory.Sieve.ofArrows_eq_ofObjects** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Sieve`。
形式化陈述：ofArrows_eq_ofObjects {X : C} (hX : IsTerminal X) {I : Type*} (Y : I -> C)
 (f : forall i, Y i ⟶ X) : ofArrows Y f = ofObjects Y X
参数：hX : IsTerminal X；Y : I -> C；f : forall i, Y i ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.Sieve.ofArrows_le_ofObjects`：ofArrows_le_ofObjects {I : T
ype*} (Y : I -> C) {X : C} (f : forall i, Y i ⟶ X) : Sieve.ofArrows Y f <= Sieve
.ofObjects Y X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.mem_ofArrows_iff`：mem_ofArrows_iff {W : C} (g : W ⟶
 X) : ofArrows Y f g ↔ exists (i : I) (a : W ⟶ Y i), g = a ≫ f i
· 使用引理 `CategoryTheory.Sieve.mem_ofObjects_iff`：mem_ofObjects_iff {I : Type*} (Y
 : I -> C) {Z X : C} (g : Z ⟶ X) : ofObjects Y X g ↔ exists (i : I), Nonempty (Z
 ⟶ Y i)
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
lemma ofArrows_eq_ofObjects {X : C} (hX : IsTerminal X)
    {I : Type*} (Y : I → C) (f : ∀ i, Y i ⟶ X) :
    ofArrows Y f = ofObjects Y X := by
  refine le_antisymm (ofArrows_le_ofObjects Y f) (fun W g => ?_)
  rw [mem_ofArrows_iff, mem_ofObjects_iff]
  rintro ⟨i, ⟨h⟩⟩
  exact ⟨i, h, hX.hom_ext _ _⟩
/-
**CategoryTheory.Sieve.ofObjects_mono** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Sieve`。
形式化陈述：ofObjects_mono {I : Type*} {X : I -> C} {I' : Type*} {X' : I' -> C} {Y : C
} (h : Set.range X subseteq Set.range X') : Sieve.ofObjects X Y <= Sieve.ofObjec
ts X' Y
参数：h : Set.range X subseteq Set.range X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ofObjects_mono {I : Type*} {X : I → C} {I' : Type*} {X' : I' → C} {Y : C}
    (h : Set.range X ⊆ Set.range X') :
    Sieve.ofObjects X Y ≤ Sieve.ofObjects X' Y := by
  rintro Z f ⟨i, ⟨g⟩⟩
  obtain ⟨i', h⟩ := h ⟨i, rfl⟩
  exact ⟨i', ⟨h ▸ g⟩⟩

/-- Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
as the inverse image of S with `_ ≫ h`. That is, `Sieve.pullback S h := (≫ h) '⁻¹ S`. -/
@[simps]
/-
**CategoryTheory.Sieve.pullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve`
。
形式化陈述：pullback (h : Y ⟶ X) (S : Sieve X) : Sieve Y where arrows _ sl
参数：h : Y ⟶ X；S : Sieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
as the inverse image of S with `_ ≫ h`. That is, `Sieve.pullback S h := (≫ h) '⁻
¹ S`.
-/
def pullback (h : Y ⟶ X) (S : Sieve X) : Sieve Y where
  arrows _ sl := S (sl ≫ h)
  downward_closed g := by simp [g]

@[simp]
/-
**CategoryTheory.Sieve.pullback_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sie
ve`。
形式化陈述：pullback_id : S.pullback (𝟙 _) = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem pullback_id : S.pullback (𝟙 _) = S := by simp [Sieve.ext_iff]

@[simp]
/-
**CategoryTheory.Sieve.pullback_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Si
eve`。
形式化陈述：pullback_top {f : Y ⟶ X} : (⊤ : Sieve X).pullback f = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
-/
theorem pullback_top {f : Y ⟶ X} : (⊤ : Sieve X).pullback f = ⊤ :=
  top_unique fun _ _ => id
/-
**CategoryTheory.Sieve.pullback_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ieve`。
形式化陈述：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : Sieve X) : S.pullback (g ≫ f) =
 (S.pullback f).pullback g
参数：S : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : Sieve X) :
    S.pullback (g ≫ f) = (S.pullback f).pullback g := by simp [Sieve.ext_iff]

@[simp]
/-
**CategoryTheory.Sieve.pullback_inter** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Sieve`。
形式化陈述：pullback_inter {f : Y ⟶ X} (S R : Sieve X) : (S ⊓ R).pullback f = S.pullba
ck f ⊓ R.pullback f
参数：S R : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem pullback_inter {f : Y ⟶ X} (S R : Sieve X) :
    (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f := by simp [Sieve.ext_iff]
/-
**CategoryTheory.Sieve.pullback_ofArrows_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Sieve`。
形式化陈述：pullback_ofArrows_of_iso {I : Type*} {X : C} (Z : I -> C) (f : forall i, Z
 i ⟶ X) {X' : C} (e : X' ≅ X) : pullback e.hom (Sieve.ofArrows _ f) = Sieve.ofAr
rows _ (fun i => f i ≫ e.inv)
参数：Z : I -> C；f : forall i, Z i ⟶ X；e : X' ≅ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.ext_iff`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   R = S ↔ ∀ ⦃Y : C⦄ (f
 : Y ⟶ X), R.arrow…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma pullback_ofArrows_of_iso
    {I : Type*} {X : C} (Z : I → C) (f : ∀ i, Z i ⟶ X) {X' : C} (e : X' ≅ X) :
    pullback e.hom (Sieve.ofArrows _ f) =
      Sieve.ofArrows _ (fun i ↦ f i ≫ e.inv) := by
  rw [Sieve.ext_iff]
  intro W a
  constructor
  · rintro ⟨T, b, c, ⟨i⟩, fac⟩
    exact ⟨_, b, _, ⟨i⟩, by simp [reassoc_of% fac]⟩
  · rintro ⟨_, a, _, ⟨i⟩, rfl⟩
    exact ⟨_, a, _, ⟨i⟩, by simp⟩
/-
**CategoryTheory.Sieve.mem_iff_pullback_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Sieve`。
形式化陈述：mem_iff_pullback_eq_top (f : Y ⟶ X) : S f ↔ S.pullback f = ⊤
参数：f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.id_mem_iff_eq_top`：id_mem_iff_eq_top : S (𝟙 X) ↔ S 
= ⊤
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff_pullback_eq_top (f : Y ⟶ X) : S f ↔ S.pullback f = ⊤ := by
  rw [← id_mem_iff_eq_top, pullback_apply, id_comp]
/-
**CategoryTheory.Sieve.pullback_eq_top_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Sieve`。
形式化陈述：pullback_eq_top_of_mem (S : Sieve X) {f : Y ⟶ X} : S f -> S.pullback f = ⊤
参数：S : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Sieve.mem_iff_pullback_eq_top`：mem_iff_pullback_eq_top (f
 : Y ⟶ X) : S f ↔ S.pullback f = ⊤
-/
theorem pullback_eq_top_of_mem (S : Sieve X) {f : Y ⟶ X} : S f → S.pullback f = ⊤ :=
  (mem_iff_pullback_eq_top f).1
/-
**CategoryTheory.Sieve.pullback_ofObjects_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Sieve`。
形式化陈述：pullback_ofObjects_eq_top {I : Type*} (Y : I -> C) {X : C} {i : I} (g : X 
⟶ Y i) : ofObjects Y X = ⊤
参数：Y : I -> C；g : X ⟶ Y i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用引理 `CategoryTheory.Sieve.mem_ofObjects_iff`：mem_ofObjects_iff {I : Type*} (Y
 : I -> C) {Z X : C} (g : Z ⟶ X) : ofObjects Y X g ↔ exists (i : I), Nonempty (Z
 ⟶ Y i)
-/
lemma pullback_ofObjects_eq_top
    {I : Type*} (Y : I → C) {X : C} {i : I} (g : X ⟶ Y i) :
    ofObjects Y X = ⊤ := by
  ext Z h
  simp only [top_apply, iff_true]
  rw [mem_ofObjects_iff]
  exact ⟨i, ⟨h ≫ g⟩⟩

@[simp]
/-
**CategoryTheory.Sieve.pullback_ofObjects** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Sieve`。
形式化陈述：pullback_ofObjects {I : Type*} (X : I -> C) {Y Z : C} (f : Z ⟶ Y) : (ofObj
ects X Y).pullback f = ofObjects X Z
参数：X : I -> C；f : Z ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pullback_ofObjects {I : Type*} (X : I → C) {Y Z : C} (f : Z ⟶ Y) :
    (ofObjects X Y).pullback f = ofObjects X Z := by
  ext
  simp [Sieve.ofObjects]

@[simp]
/-
**CategoryTheory.Sieve.ofObjects_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Si
eve`。
形式化陈述：ofObjects_id (X : C) : Sieve.ofObjects id X = ⊤
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Sieve.pullback_ofObjects_eq_top`：pullback_ofObjects_eq_to
p {I : Type*} (Y : I -> C) {X : C} {i : I} (g : X ⟶ Y i) : ofObjects Y X = ⊤
-/
lemma ofObjects_id (X : C) : Sieve.ofObjects id X = ⊤ :=
  Sieve.pullback_ofObjects_eq_top _ (𝟙 _)

/-- Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X` is in the sieve if `gf`
factors through some `g : Z ⟶ Y` which is in `R`.
-/
@[simps]
/-
**CategoryTheory.Sieve.pushforward** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sie
ve`。
形式化陈述：pushforward (f : Y ⟶ X) (R : Sieve Y) : Sieve X where arrows _ gf
参数：f : Y ⟶ X；R : Sieve Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X` is in t
he sieve if `gf`
factors through some `g : Z ⟶ Y` which is in `R`.
-/
def pushforward (f : Y ⟶ X) (R : Sieve Y) : Sieve X where
  arrows _ gf := ∃ g, g ≫ f = gf ∧ R g
  downward_closed := fun ⟨j, k, z⟩ h => ⟨h ≫ j, by simp [k], by simp [z]⟩
/-
**CategoryTheory.Sieve.pushforward_apply_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Sieve`。
形式化陈述：pushforward_apply_comp {R : Sieve Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y
 ⟶ X) : R.pushforward f (g ≫ f)
参数：hg : R g；f : Y ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushforward_apply_comp {R : Sieve Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y ⟶ X) :
    R.pushforward f (g ≫ f) :=
  ⟨g, rfl, hg⟩
/-
**CategoryTheory.Sieve.pushforward_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Sieve`。
形式化陈述：pushforward_comp {f : Y ⟶ X} {g : Z ⟶ Y} (R : Sieve Z) : R.pushforward (g 
≫ f) = (R.pushforward g).pushforward f
参数：R : Sieve Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pushforward_comp {f : Y ⟶ X} {g : Z ⟶ Y} (R : Sieve Z) :
    R.pushforward (g ≫ f) = (R.pushforward g).pushforward f :=
  Sieve.ext fun W h =>
    ⟨fun ⟨f₁, hq, hf₁⟩ => ⟨f₁ ≫ g, by simpa, f₁, rfl, hf₁⟩, fun ⟨y, hy, z, hR, hz⟩ =>
      ⟨z, by rw [← Category.assoc, hR]; tauto⟩⟩
/-
**CategoryTheory.Sieve.galoisConnection** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Sieve`。
形式化陈述：galoisConnection (f : Y ⟶ X) : GaloisConnection (Sieve.pushforward f) (Sie
ve.pullback f)
参数：f : Y ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem galoisConnection (f : Y ⟶ X) : GaloisConnection (Sieve.pushforward f) (Sieve.pullback f) :=
  fun _ _ => ⟨fun hR _ g hg => hR _ ⟨g, rfl, hg⟩, fun hS _ _ ⟨h, hg, hh⟩ => hg ▸ hS h hh⟩
/-
**CategoryTheory.Sieve.pullback_monotone** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：pullback_monotone (f : Y ⟶ X) : Monotone (Sieve.pullback f)
参数：f : Y ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `CategoryTheory.Sieve.galoisConnection`：galoisConnection (f : Y ⟶ X) : Ga
loisConnection (Sieve.pushforward f) (Sieve.pullback f)
-/
theorem pullback_monotone (f : Y ⟶ X) : Monotone (Sieve.pullback f) :=
  (galoisConnection f).monotone_u
/-
**CategoryTheory.Sieve.pushforward_monotone** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Sieve`。
形式化陈述：pushforward_monotone (f : Y ⟶ X) : Monotone (Sieve.pushforward f)
参数：f : Y ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `CategoryTheory.Sieve.galoisConnection`：galoisConnection (f : Y ⟶ X) : Ga
loisConnection (Sieve.pushforward f) (Sieve.pullback f)
-/
theorem pushforward_monotone (f : Y ⟶ X) : Monotone (Sieve.pushforward f) :=
  (galoisConnection f).monotone_l
/-
**CategoryTheory.Sieve.le_pushforward_pullback** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Sieve`。
形式化陈述：le_pushforward_pullback (f : Y ⟶ X) (R : Sieve Y) : R <= (R.pushforward f)
.pullback f
参数：f : Y ⟶ X；R : Sieve Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `CategoryTheory.Sieve.galoisConnection`：galoisConnection (f : Y ⟶ X) : Ga
loisConnection (Sieve.pushforward f) (Sieve.pullback f)
-/
theorem le_pushforward_pullback (f : Y ⟶ X) (R : Sieve Y) : R ≤ (R.pushforward f).pullback f :=
  (galoisConnection f).le_u_l _
/-
**CategoryTheory.Sieve.pullback_pushforward_le** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Sieve`。
形式化陈述：pullback_pushforward_le (f : Y ⟶ X) (R : Sieve X) : (R.pullback f).pushfor
ward f <= R
参数：f : Y ⟶ X；R : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `CategoryTheory.Sieve.galoisConnection`：galoisConnection (f : Y ⟶ X) : Ga
loisConnection (Sieve.pushforward f) (Sieve.pullback f)
-/
theorem pullback_pushforward_le (f : Y ⟶ X) (R : Sieve X) : (R.pullback f).pushforward f ≤ R :=
  (galoisConnection f).l_u_le _
/-
**CategoryTheory.Sieve.pushforward_union** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：pushforward_union {f : Y ⟶ X} (S R : Sieve Y) : (S ⊔ R).pushforward f = S.
pushforward f ⊔ R.pushforward f
参数：S R : Sieve Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `CategoryTheory.Sieve.galoisConnection`：galoisConnection (f : Y ⟶ X) : Ga
loisConnection (Sieve.pushforward f) (Sieve.pullback f)
-/
theorem pushforward_union {f : Y ⟶ X} (S R : Sieve Y) :
    (S ⊔ R).pushforward f = S.pushforward f ⊔ R.pushforward f :=
  (galoisConnection f).l_sup

@[simp]
/-
**CategoryTheory.Sieve.pullback_bot** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Si
eve`。
形式化陈述：pullback_bot (f : Y ⟶ X) : (⊥ : Sieve X).pullback f = ⊥
参数：f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback_bot (f : Y ⟶ X) : (⊥ : Sieve X).pullback f = ⊥ :=
  rfl

@[simp]
/-
**CategoryTheory.Sieve.pushforward_bot** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Sieve`。
形式化陈述：pushforward_bot (f : Y ⟶ X) : (⊥ : Sieve Y).pushforward f = ⊥
参数：f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `CategoryTheory.Sieve.galoisConnection`：galoisConnection (f : Y ⟶ X) : Ga
loisConnection (Sieve.pushforward f) (Sieve.pullback f)
-/
lemma pushforward_bot (f : Y ⟶ X) : (⊥ : Sieve Y).pushforward f = ⊥ :=
  (galoisConnection f).l_bot
/-
**CategoryTheory.Sieve.pushforward_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Sieve`。
形式化陈述：pushforward_eq_bot_iff {f : Y ⟶ X} {S : Sieve Y} : S.pushforward f = ⊥ ↔ S
 = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaloisConnection.l_eq_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOr
der α] [inst_1 : Preorder β] [inst_2 : OrderBot α] {u : α → β} {l : β → α},   Ga
loisConnection …
· 使用定理 `CategoryTheory.Sieve.galoisConnection`：galoisConnection (f : Y ⟶ X) : Ga
loisConnection (Sieve.pushforward f) (Sieve.pullback f)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pushforward_eq_bot_iff {f : Y ⟶ X} {S : Sieve Y} : S.pushforward f = ⊥ ↔ S = ⊥ := by
  simp [(galoisConnection f).l_eq_bot]
/-
**CategoryTheory.Sieve.pushforward_le_bind_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Sieve`。
形式化陈述：pushforward_le_bind_of_mem (S : Presieve X) (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X
⦄, S f -> Sieve Y) (f : Y ⟶ X) (h : S f) : (R h).pushforward f <= bind S R
参数：S : Presieve X；R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y；f : Y ⟶ X；h : S
 f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushforward_le_bind_of_mem (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y)
    (f : Y ⟶ X) (h : S f) : (R h).pushforward f ≤ bind S R := by
  rintro Z _ ⟨g, rfl, hg⟩
  exact ⟨_, g, f, h, hg, rfl⟩
/-
**CategoryTheory.Sieve.le_pullback_bind** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Sieve`。
形式化陈述：le_pullback_bind (S : Presieve X) (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> 
Sieve Y) (f : Y ⟶ X) (h : S f) : R h <= (bind S R).pullback f
参数：S : Presieve X；R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y；f : Y ⟶ X；h : S
 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.galoisConnection`：galoisConnection (f : Y ⟶ X) : Ga
loisConnection (Sieve.pushforward f) (Sieve.pullback f)
· 使用定理 `CategoryTheory.Sieve.pushforward_le_bind_of_mem`：pushforward_le_bind_of_
mem (S : Presieve X) (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) (f : Y ⟶ X
) (h : S f) : (R h).pushforward f <= …
-/
theorem le_pullback_bind (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) (f : Y ⟶ X)
    (h : S f) : R h ≤ (bind S R).pullback f := by
  rw [← galoisConnection f]
  apply pushforward_le_bind_of_mem

/-- If `f` is a monomorphism, the pushforward-pullback adjunction on sieves is coreflective. -/
/-
**CategoryTheory.Sieve.galoisCoinsertionOfMono** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Sieve`。
形式化陈述：galoisCoinsertionOfMono (f : Y ⟶ X) [Mono f] : GaloisCoinsertion (Sieve.pu
shforward f) (Sieve.pullback f)
参数：f : Y ⟶ X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.galoisConnection`：galoisConnection (f : Y ⟶ X) : Ga
loisConnection (Sieve.pushforward f) (Sieve.pullback f)

--- 原说明 ---
If `f` is a monomorphism, the pushforward-pullback adjunction on sieves is coref
lective.
-/
def galoisCoinsertionOfMono (f : Y ⟶ X) [Mono f] :
    GaloisCoinsertion (Sieve.pushforward f) (Sieve.pullback f) := by
  apply (galoisConnection f).toGaloisCoinsertion
  rintro S Z g ⟨g₁, hf, hg₁⟩
  rw [cancel_mono f] at hf
  rwa [← hf]

/-- If `f` is a split epi, the pushforward-pullback adjunction on sieves is reflective. -/
/-
**CategoryTheory.Sieve.galoisInsertionOfIsSplitEpi** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Sieve`。
形式化陈述：galoisInsertionOfIsSplitEpi (f : Y ⟶ X) [IsSplitEpi f] : GaloisInsertion (
Sieve.pushforward f) (Sieve.pullback f)
参数：f : Y ⟶ X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.galoisConnection`：galoisConnection (f : Y ⟶ X) : Ga
loisConnection (Sieve.pushforward f) (Sieve.pullback f)

--- 原说明 ---
If `f` is a split epi, the pushforward-pullback adjunction on sieves is reflecti
ve.
-/
def galoisInsertionOfIsSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    GaloisInsertion (Sieve.pushforward f) (Sieve.pullback f) := by
  apply (galoisConnection f).toGaloisInsertion
  intro S Z g hg
  exact ⟨g ≫ section_ f, by simpa⟩
/-
**CategoryTheory.Sieve.pullbackArrows_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Sieve`。
形式化陈述：pullbackArrows_comm {X Y : C} (f : Y ⟶ X) (R : Presieve X) [R.HasPullbacks
 f] : Sieve.generate (R.pullbackArrows f) = (Sieve.generate R).pullback f
参数：f : Y ⟶ X；R : Presieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `CategoryTheory.Presieve.hasPullback`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Presieve X} {Y : C} (f : Y 
⟶ X)   [self : R.HasPullb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem pullbackArrows_comm {X Y : C} (f : Y ⟶ X) (R : Presieve X) [R.HasPullbacks f] :
    Sieve.generate (R.pullbackArrows f) = (Sieve.generate R).pullback f := by
  ext W g
  constructor
  · rintro ⟨_, h, k, ⟨W, g, hg⟩, rfl⟩
    have := R.hasPullback f hg
    rw [Sieve.pullback_apply, assoc, ← pullback.condition, ← assoc]
    exact Sieve.downward_closed _ (by exact Sieve.le_generate R W _ hg) (h ≫ pullback.fst g f)
  · rintro ⟨W, h, k, hk, comm⟩
    have := R.hasPullback f hk
    exact ⟨_, _, _, Presieve.pullbackArrows.mk _ _ hk, pullback.lift_snd _ _ comm⟩
/-
**CategoryTheory.Sieve.pullback_arrows** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Sieve`。
形式化陈述：pullback_arrows {X Y : C} (f : X ⟶ Y) (S : Sieve Y) : (S.pullback f).arrow
s = S.arrows.pullback f
参数：f : X ⟶ Y；S : Sieve Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback_arrows {X Y : C} (f : X ⟶ Y) (S : Sieve Y) :
    (S.pullback f).arrows = S.arrows.pullback f :=
  rfl
/-
**CategoryTheory.Sieve.pushforward_arrows** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Sieve`。
形式化陈述：pushforward_arrows {X Y : C} (f : X ⟶ Y) (S : Sieve X) : (S.pushforward f)
.arrows = S.arrows.pushforward f
参数：f : X ⟶ Y；S : Sieve X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushforward_arrows {X Y : C} (f : X ⟶ Y) (S : Sieve X) :
    (S.pushforward f).arrows = S.arrows.pushforward f :=
  rfl
/-
**CategoryTheory.Sieve.generate_pushforward** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Sieve`。
形式化陈述：generate_pushforward {X Y : C} (f : X ⟶ Y) (R : Presieve X) : generate (R.
pushforward f) = (generate R).pushforward f
参数：f : X ⟶ Y；R : Presieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
-/
lemma generate_pushforward {X Y : C} (f : X ⟶ Y) (R : Presieve X) :
    generate (R.pushforward f) = (generate R).pushforward f := by
  ext
  grind [generate_apply, Presieve.pushforward, pushforward_apply]

section Functor

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/--
If `R` is a sieve, then the `CategoryTheory.Presieve.functorPullback` of `R` is actually a sieve.
-/
@[simps]
/-
**CategoryTheory.Sieve.functorPullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Sieve`。
形式化陈述：functorPullback (R : Sieve (F.obj X)) : Sieve X where arrows
参数：R : Sieve (F.obj X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a sieve, then the `CategoryTheory.Presieve.functorPullback` of `R` is 
actually a sieve.
-/
def functorPullback (R : Sieve (F.obj X)) : Sieve X where
  arrows := Presieve.functorPullback F R
  downward_closed := by
    intro _ _ f hf g
    unfold Presieve.functorPullback
    rw [F.map_comp]
    exact R.downward_closed hf (F.map g)

@[simp]
/-
**CategoryTheory.Sieve.functorPullback_arrows** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Sieve`。
形式化陈述：functorPullback_arrows (R : Sieve (F.obj X)) : (R.functorPullback F).arrow
s = R.arrows.functorPullback F
参数：R : Sieve (F.obj X)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem functorPullback_arrows (R : Sieve (F.obj X)) :
    (R.functorPullback F).arrows = R.arrows.functorPullback F :=
  rfl

@[simp]
/-
**CategoryTheory.Sieve.functorPullback_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Sieve`。
形式化陈述：functorPullback_id (R : Sieve X) : R.functorPullback (𝟭 _) = R
参数：R : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem functorPullback_id (R : Sieve X) : R.functorPullback (𝟭 _) = R := by
  ext
  rfl
/-
**CategoryTheory.Sieve.functorPullback_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Sieve`。
形式化陈述：functorPullback_comp (R : Sieve ((F ⋙ G).obj X)) : R.functorPullback (F ⋙ 
G) = (R.functorPullback G).functorPullback F
参数：R : Sieve ((F ⋙ G).obj X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem functorPullback_comp (R : Sieve ((F ⋙ G).obj X)) :
    R.functorPullback (F ⋙ G) = (R.functorPullback G).functorPullback F := by
  ext
  rfl
/-
**CategoryTheory.Sieve.generate_functorPullback_le** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Sieve`。
形式化陈述：generate_functorPullback_le {X : C} (R : Presieve (F.obj X)) : generate (R
.functorPullback F) <= functorPullback F (generate R)
参数：R : Presieve (F.obj X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.generate_le_iff`：generate_le_iff (R : Presieve X) (
S : Sieve X) : generate R <= S ↔ R <= S
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
-/
lemma generate_functorPullback_le {X : C} (R : Presieve (F.obj X)) :
     generate (R.functorPullback F) ≤ functorPullback F (generate R) := by
  rw [generate_le_iff]
  intro Z g hg
  exact le_generate _ _ _ hg
/-
**CategoryTheory.Sieve.functorPullback_pullback** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Sieve`。
形式化陈述：functorPullback_pullback {X Y : C} (f : X ⟶ Y) (S : Sieve (F.obj Y)) : fun
ctorPullback F (pullback (F.map f) S) = pullback f (functorPullback F S)
参数：f : X ⟶ Y；S : Sieve (F.obj Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.functorPullback_apply`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma functorPullback_pullback {X Y : C} (f : X ⟶ Y) (S : Sieve (F.obj Y)) :
    functorPullback F (pullback (F.map f) S) = pullback f (functorPullback F S) := by
  ext
  simp
/-
**CategoryTheory.Sieve.functorPushforward_extend_eq** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Sieve`。
形式化陈述：functorPushforward_extend_eq {R : Presieve X} : (generate R).arrows.functo
rPushforward F = R.functorPushforward F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
-/
theorem functorPushforward_extend_eq {R : Presieve X} :
    (generate R).arrows.functorPushforward F = R.functorPushforward F := by
  funext Y
  ext f
  constructor
  · rintro ⟨X', g, f', ⟨X'', g', f'', h₁, rfl⟩, rfl⟩
    exact ⟨X'', f'', f' ≫ F.map g', h₁, by simp⟩
  · rintro ⟨X', g, f', h₁, h₂⟩
    exact ⟨X', g, f', le_generate R _ _ h₁, h₂⟩

/-- The sieve generated by the image of `R` under `F`. -/
@[simps]
/-
**CategoryTheory.Sieve.functorPushforward** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Sieve`。
形式化陈述：functorPushforward (R : Sieve X) : Sieve (F.obj X) where arrows
参数：R : Sieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sieve generated by the image of `R` under `F`.
-/
def functorPushforward (R : Sieve X) : Sieve (F.obj X) where
  arrows := R.arrows.functorPushforward F
  downward_closed := by
    intro _ _ f h g
    obtain ⟨X, α, β, hα, rfl⟩ := h
    exact ⟨X, α, g ≫ β, hα, by simp⟩
/-
**CategoryTheory.Sieve.generate_map_eq_functorPushforward** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Sieve`。
形式化陈述：generate_map_eq_functorPushforward {s : Presieve X} : generate (s.map F) =
 (generate s).functorPushforward F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.arrows_generate_map_eq_functorPushforward`：arrows_g
enerate_map_eq_functorPushforward {s : Presieve X} : (generate (s.map F)).arrows
 = s.functorPushforward F
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sieve.functorPushforward_apply`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Sieve.functorPushforward_extend_eq`：functorPushforward_ex
tend_eq {R : Presieve X} : (generate R).arrows.functorPushforward F = R.functorP
ushforward F
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem generate_map_eq_functorPushforward {s : Presieve X} :
    generate (s.map F) = (generate s).functorPushforward F := by
  ext
  rw [arrows_generate_map_eq_functorPushforward]
  simp [functorPushforward_extend_eq]
/-
**CategoryTheory.Sieve.functorPushforward_ofArrows** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Sieve`。
形式化陈述：functorPushforward_ofArrows {X : C} {ι : Type*} {Y : ι -> C} (f : forall i
, Y i ⟶ X) : functorPushforward F (ofArrows Y f) = ofArrows _ fun i : ι => F.map
 (f i)
参数：f : forall i, Y i ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.generate_map_eq_functorPushforward`：generate_map_eq
_functorPushforward {s : Presieve X} : generate (s.map F) = (generate s).functor
Pushforward F
· 使用引理 `CategoryTheory.Presieve.map_ofArrows`：map_ofArrows {X : C} {ι : Type*} {
Y : ι -> C} (f : forall i, Y i ⟶ X) : (ofArrows Y f).map F = ofArrows _ (fun i =
> F.map (f i))
-/
lemma functorPushforward_ofArrows {X : C} {ι : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ X) :
    functorPushforward F (ofArrows Y f) = ofArrows _ fun i : ι ↦ F.map (f i) := by
  rw [← generate_map_eq_functorPushforward, Presieve.map_ofArrows]

@[simp]
/-
**CategoryTheory.Sieve.functorPushforward_id** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Sieve`。
形式化陈述：functorPushforward_id (R : Sieve X) : R.functorPushforward (𝟭 _) = R
参数：R : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem functorPushforward_id (R : Sieve X) : R.functorPushforward (𝟭 _) = R := by
  ext X f
  constructor
  · intro hf
    obtain ⟨X, g, h, hg, rfl⟩ := hf
    exact R.downward_closed hg h
  · intro hf
    exact ⟨X, f, 𝟙 _, hf, by simp⟩
/-
**CategoryTheory.Sieve.functorPushforward_comp** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Sieve`。
形式化陈述：functorPushforward_comp (R : Sieve X) : R.functorPushforward (F ⋙ G) = (R.
functorPushforward F).functorPushforward G
参数：R : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.functorPushforward_apply`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Presieve.functorPushforward_comp`：functorPushforward_comp
 (R : Presieve X) : R.functorPushforward (F ⋙ G) = (R.functorPushforward F).func
torPushforward G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem functorPushforward_comp (R : Sieve X) :
    R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPushforward G := by
  ext
  simp [R.arrows.functorPushforward_comp F G]
/-
**CategoryTheory.Sieve.functor_galoisConnection** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Sieve`。
形式化陈述：functor_galoisConnection (X : C) : GaloisConnection (Sieve.functorPushforw
ard F : Sieve X -> Sieve (F.obj X)) (Sieve.functorPullback F)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem functor_galoisConnection (X : C) :
    GaloisConnection (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  intro R S
  constructor
  · intro hle X f hf
    apply hle
    refine ⟨X, f, 𝟙 _, hf, ?_⟩
    rw [id_comp]
  · rintro hle Y f ⟨X, g, h, hg, rfl⟩
    apply Sieve.downward_closed S
    exact hle g hg
/-
**CategoryTheory.Sieve.functorPushforward_le_iff_le_functorPullback** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：functorPushforward_le_iff_le_functorPullback {X : C} (S : Sieve X) (R : Si
eve (F.obj X)) : S.functorPushforward F <= R ↔ S <= R.functorPullback F
参数：S : Sieve X；R : Sieve (F.obj X)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_iff_le`：le_iff_le {a : α} {b : β} : l a <= b ↔ a <= 
u b
· 使用定理 `CategoryTheory.Sieve.functor_galoisConnection`：functor_galoisConnection 
(X : C) : GaloisConnection (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj
 X)) (Sieve.functorPullback F)
-/
lemma functorPushforward_le_iff_le_functorPullback {X : C} (S : Sieve X) (R : Sieve (F.obj X)) :
    S.functorPushforward F ≤ R ↔ S ≤ R.functorPullback F :=
  (Sieve.functor_galoisConnection F X).le_iff_le
/-
**CategoryTheory.Sieve.functorPullback_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Sieve`。
形式化陈述：functorPullback_monotone (X : C) : Monotone (Sieve.functorPullback F : Sie
ve (F.obj X) -> Sieve X)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `CategoryTheory.Sieve.functor_galoisConnection`：functor_galoisConnection 
(X : C) : GaloisConnection (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj
 X)) (Sieve.functorPullback F)
-/
theorem functorPullback_monotone (X : C) :
    Monotone (Sieve.functorPullback F : Sieve (F.obj X) → Sieve X) :=
  (functor_galoisConnection F X).monotone_u
/-
**CategoryTheory.Sieve.functorPushforward_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Sieve`。
形式化陈述：functorPushforward_monotone (X : C) : Monotone (Sieve.functorPushforward F
 : Sieve X -> Sieve (F.obj X))
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `CategoryTheory.Sieve.functor_galoisConnection`：functor_galoisConnection 
(X : C) : GaloisConnection (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj
 X)) (Sieve.functorPullback F)
-/
theorem functorPushforward_monotone (X : C) :
    Monotone (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X)) :=
  (functor_galoisConnection F X).monotone_l
/-
**CategoryTheory.Sieve.le_functorPushforward_pullback** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Sieve`。
形式化陈述：le_functorPushforward_pullback (R : Sieve X) : R <= (R.functorPushforward 
F).functorPullback F
参数：R : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `CategoryTheory.Sieve.functor_galoisConnection`：functor_galoisConnection 
(X : C) : GaloisConnection (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj
 X)) (Sieve.functorPullback F)
-/
theorem le_functorPushforward_pullback (R : Sieve X) :
    R ≤ (R.functorPushforward F).functorPullback F :=
  (functor_galoisConnection F X).le_u_l _
/-
**CategoryTheory.Sieve.functorPullback_pushforward_le** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Sieve`。
形式化陈述：functorPullback_pushforward_le (R : Sieve (F.obj X)) : (R.functorPullback 
F).functorPushforward F <= R
参数：R : Sieve (F.obj X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `CategoryTheory.Sieve.functor_galoisConnection`：functor_galoisConnection 
(X : C) : GaloisConnection (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj
 X)) (Sieve.functorPullback F)
-/
theorem functorPullback_pushforward_le (R : Sieve (F.obj X)) :
    (R.functorPullback F).functorPushforward F ≤ R :=
  (functor_galoisConnection F X).l_u_le _
/-
**CategoryTheory.Sieve.functorPushforward_union** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Sieve`。
形式化陈述：functorPushforward_union (S R : Sieve X) : (S ⊔ R).functorPushforward F = 
S.functorPushforward F ⊔ R.functorPushforward F
参数：S R : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `CategoryTheory.Sieve.functor_galoisConnection`：functor_galoisConnection 
(X : C) : GaloisConnection (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj
 X)) (Sieve.functorPullback F)
-/
theorem functorPushforward_union (S R : Sieve X) :
    (S ⊔ R).functorPushforward F = S.functorPushforward F ⊔ R.functorPushforward F :=
  (functor_galoisConnection F X).l_sup
/-
**CategoryTheory.Sieve.functorPullback_union** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Sieve`。
形式化陈述：functorPullback_union (S R : Sieve (F.obj X)) : (S ⊔ R).functorPullback F 
= S.functorPullback F ⊔ R.functorPullback F
参数：S R : Sieve (F.obj X)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem functorPullback_union (S R : Sieve (F.obj X)) :
    (S ⊔ R).functorPullback F = S.functorPullback F ⊔ R.functorPullback F :=
  rfl
/-
**CategoryTheory.Sieve.functorPullback_inter** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Sieve`。
形式化陈述：functorPullback_inter (S R : Sieve (F.obj X)) : (S ⊓ R).functorPullback F 
= S.functorPullback F ⊓ R.functorPullback F
参数：S R : Sieve (F.obj X)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem functorPullback_inter (S R : Sieve (F.obj X)) :
    (S ⊓ R).functorPullback F = S.functorPullback F ⊓ R.functorPullback F :=
  rfl

@[simp]
/-
**CategoryTheory.Sieve.functorPushforward_bot** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Sieve`。
形式化陈述：functorPushforward_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve X).functorPushforw
ard F = ⊥
参数：F : C ⥤ D；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `CategoryTheory.Sieve.functor_galoisConnection`：functor_galoisConnection 
(X : C) : GaloisConnection (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj
 X)) (Sieve.functorPullback F)
-/
theorem functorPushforward_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve X).functorPushforward F = ⊥ :=
  (functor_galoisConnection F X).l_bot

@[simp]
/-
**CategoryTheory.Sieve.functorPushforward_top** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Sieve`。
形式化陈述：functorPushforward_top (F : C ⥤ D) (X : C) : (⊤ : Sieve X).functorPushforw
ard F = ⊤
参数：F : C ⥤ D；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
· 使用定理 `CategoryTheory.Sieve.generate_of_contains_isSplitEpi`：generate_of_contai
ns_isSplitEpi {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f) : generate 
R = ⊤
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `trivial`：True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem functorPushforward_top (F : C ⥤ D) (X : C) : (⊤ : Sieve X).functorPushforward F = ⊤ := by
  refine (generate_sieve _).symm.trans ?_
  apply generate_of_contains_isSplitEpi (𝟙 (F.obj X))
  exact ⟨X, 𝟙 _, 𝟙 _, trivial, by simp⟩

@[simp]
/-
**CategoryTheory.Sieve.functorPullback_bot** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Sieve`。
形式化陈述：functorPullback_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve (F.obj X)).functorPul
lback F = ⊥
参数：F : C ⥤ D；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem functorPullback_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve (F.obj X)).functorPullback F = ⊥ :=
  rfl

@[simp]
/-
**CategoryTheory.Sieve.functorPullback_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Sieve`。
形式化陈述：functorPullback_top (F : C ⥤ D) (X : C) : (⊤ : Sieve (F.obj X)).functorPul
lback F = ⊤
参数：F : C ⥤ D；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem functorPullback_top (F : C ⥤ D) (X : C) : (⊤ : Sieve (F.obj X)).functorPullback F = ⊤ :=
  rfl
/-
**CategoryTheory.Sieve.image_mem_functorPushforward** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Sieve`。
形式化陈述：image_mem_functorPushforward (R : Sieve X) {V} {f : V ⟶ X} (h : R f) : R.f
unctorPushforward F (F.map f)
参数：R : Sieve X；h : R f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_mem_functorPushforward (R : Sieve X) {V} {f : V ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨V, f, 𝟙 _, h, by simp⟩
/-
**CategoryTheory.Sieve.functorPushforward_pullback_le** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Sieve`。
形式化陈述：functorPushforward_pullback_le {X Y : C} (f : Y ⟶ X) (S : Sieve X) : (S.pu
llback f).functorPushforward F <= (S.functorPushforward F).pullback (F.map f)
参数：f : Y ⟶ X；S : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.functorPushforward_le_iff_le_functorPullback`：funct
orPushforward_le_iff_le_functorPullback {X : C} (S : Sieve X) (R : Sieve (F.obj 
X)) : S.functorPushforward F <= R ↔ S <= R.functorPullb…
· 使用引理 `CategoryTheory.Sieve.functorPullback_pullback`：functorPullback_pullback 
{X Y : C} (f : X ⟶ Y) (S : Sieve (F.obj Y)) : functorPullback F (pullback (F.map
 f) S) = pullback f (functorPullbac…
· 使用定理 `CategoryTheory.Sieve.pullback_monotone`：pullback_monotone (f : Y ⟶ X) : 
Monotone (Sieve.pullback f)
· 使用定理 `CategoryTheory.Sieve.le_functorPushforward_pullback`：le_functorPushforwa
rd_pullback (R : Sieve X) : R <= (R.functorPushforward F).functorPullback F
-/
lemma functorPushforward_pullback_le {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    (S.pullback f).functorPushforward F ≤ (S.functorPushforward F).pullback (F.map f) := by
  rw [Sieve.functorPushforward_le_iff_le_functorPullback, Sieve.functorPullback_pullback]
  apply Sieve.pullback_monotone
  exact Sieve.le_functorPushforward_pullback _ _

/-- When `F` is essentially surjective and full, the Galois connection is a Galois insertion. -/
/-
**CategoryTheory.Sieve.essSurjFullFunctorGaloisInsertion** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Sieve`。
形式化陈述：essSurjFullFunctorGaloisInsertion [F.EssSurj] [F.Full] (X : C) : GaloisIns
ertion (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj X)) (Sieve.functorP
ullback F)
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.functor_galoisConnection`：functor_galoisConnection 
(X : C) : GaloisConnection (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj
 X)) (Sieve.functorPullback F)

--- 原说明 ---
When `F` is essentially surjective and full, the Galois connection is a Galois i
nsertion.
-/
def essSurjFullFunctorGaloisInsertion [F.EssSurj] [F.Full] (X : C) :
    GaloisInsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  apply (functor_galoisConnection F X).toGaloisInsertion
  intro S Y f hf
  refine ⟨_, F.preimage ((F.objObjPreimageIso Y).hom ≫ f), (F.objObjPreimageIso Y).inv, ?_⟩
  simpa using hf

/-- When `F` is fully faithful, the Galois connection is a Galois coinsertion. -/
/-
**CategoryTheory.Sieve.fullyFaithfulFunctorGaloisCoinsertion** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：fullyFaithfulFunctorGaloisCoinsertion [F.Full] [F.Faithful] (X : C) : Galo
isCoinsertion (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj X)) (Sieve.f
unctorPullback F)
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.functor_galoisConnection`：functor_galoisConnection 
(X : C) : GaloisConnection (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj
 X)) (Sieve.functorPullback F)

--- 原说明 ---
When `F` is fully faithful, the Galois connection is a Galois coinsertion.
-/
def fullyFaithfulFunctorGaloisCoinsertion [F.Full] [F.Faithful] (X : C) :
    GaloisCoinsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  apply (functor_galoisConnection F X).toGaloisCoinsertion
  rintro S Y f ⟨Z, g, h, h₁, h₂⟩
  rw [← F.map_preimage h, ← F.map_comp] at h₂
  rw [F.map_injective h₂]
  exact S.downward_closed h₁ _
/-
**CategoryTheory.Sieve.functorPullback_functorPushforward_eq** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：functorPullback_functorPushforward_eq {X : C} {S : Sieve X} [F.Full] [F.Fa
ithful] : Sieve.functorPullback F (Sieve.functorPushforward F S) = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_l_eq`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β
 → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsertion l 
u) (b : β), u …
-/
lemma functorPullback_functorPushforward_eq {X : C} {S : Sieve X} [F.Full] [F.Faithful] :
    Sieve.functorPullback F (Sieve.functorPushforward F S) = S :=
  (Sieve.fullyFaithfulFunctorGaloisCoinsertion _ _).u_l_eq _

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Sieve.functorPushforward_functor** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Sieve`。
形式化陈述：functorPushforward_functor (S : Sieve X) (e : C ≌ D) : S.functorPushforwar
d e.functor = (S.pullback (e.unitInv.app X)).functorPullback e.inverse
参数：S : Sieve X；e : C ≌ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.inv_fun_map`：inv_fun_map (e : C ≌ D) (X Y : C
) (f : X ⟶ Y) : e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.a
pp Y
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Equivalence.fun_inv_map`：fun_inv_map (e : C ≌ D) (X Y : D
) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitI
nv.app Y
· 使用定理 `CategoryTheory.Equivalence.counitInv_functor_comp`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   (e : C ≌ D) (X : C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorPushforward_functor (S : Sieve X) (e : C ≌ D) :
    S.functorPushforward e.functor = (S.pullback (e.unitInv.app X)).functorPullback e.inverse := by
  ext Y iYX
  constructor
  · rintro ⟨Z, iZX, iYZ, hiZX, rfl⟩
    simpa using S.downward_closed hiZX (e.inverse.map iYZ ≫ e.unitInv.app Z)
  · intro H
    exact ⟨_, e.inverse.map iYX ≫ e.unitInv.app X, e.counitInv.app Y, by simpa using H, by simp⟩

@[simp]
/-
**CategoryTheory.Sieve.mem_functorPushforward_functor** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Sieve`。
形式化陈述：mem_functorPushforward_functor {Y : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ 
e.functor.obj X} : S.functorPushforward e.functor f ↔ S (e.inverse.map f ≫ e.uni
tInv.app X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.functorPushforward_functor`：functorPushforward_func
tor (S : Sieve X) (e : C ≌ D) : S.functorPushforward e.functor = (S.pullback (e.
unitInv.app X)).functorPullback e.inv…
-/
lemma mem_functorPushforward_functor {Y : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ e.functor.obj X} :
    S.functorPushforward e.functor f ↔ S (e.inverse.map f ≫ e.unitInv.app X) :=
  congr($(S.functorPushforward_functor e).arrows f)
/-
**CategoryTheory.Sieve.functorPushforward_inverse** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Sieve`。
形式化陈述：functorPushforward_inverse {X : D} (S : Sieve X) (e : C ≌ D) : S.functorPu
shforward e.inverse = (S.pullback (e.counit.app X)).functorPullback e.functor
参数：S : Sieve X；e : C ≌ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Sieve.functorPushforward_functor`：functorPushforward_func
tor (S : Sieve X) (e : C ≌ D) : S.functorPushforward e.functor = (S.pullback (e.
unitInv.app X)).functorPullback e.inv…
-/
lemma functorPushforward_inverse {X : D} (S : Sieve X) (e : C ≌ D) :
    S.functorPushforward e.inverse = (S.pullback (e.counit.app X)).functorPullback e.functor :=
  Sieve.functorPushforward_functor S e.symm

@[simp]
/-
**CategoryTheory.Sieve.mem_functorPushforward_inverse** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Sieve`。
形式化陈述：mem_functorPushforward_inverse {X : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ 
e.inverse.obj X} : S.functorPushforward e.inverse f ↔ S (e.functor.map f ≫ e.cou
nit.app X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.functorPushforward_inverse`：functorPushforward_inve
rse {X : D} (S : Sieve X) (e : C ≌ D) : S.functorPushforward e.inverse = (S.pull
back (e.counit.app X)).functorPullbac…
-/
lemma mem_functorPushforward_inverse {X : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ e.inverse.obj X} :
    S.functorPushforward e.inverse f ↔ S (e.functor.map f ≫ e.counit.app X) :=
  congr($(S.functorPushforward_inverse e).arrows f)

variable (e : C ≌ D)
/-
**CategoryTheory.Sieve.functorPushforward_equivalence_eq_pullback** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：functorPushforward_equivalence_eq_pullback {U : C} (S : Sieve U) : Sieve.f
unctorPushforward e.inverse (Sieve.functorPushforward e.functor S) = Sieve.pullb
ack (e.unitInv.app U) S
参数：S : Sieve U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.inv_fun_map`：inv_fun_map (e : C ≌ D) (X Y : C
) (f : X ⟶ Y) : e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.a
pp Y
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Equivalence.unit_inverse_comp`：unit_inverse_comp (e : C ≌
 D) (Y : D) : dsimp% e.unit.app (e.inverse.obj Y) ≫ e.inverse.map (e.counit.app 
Y) = 𝟙 (e.inverse.obj Y)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma functorPushforward_equivalence_eq_pullback {U : C} (S : Sieve U) :
    Sieve.functorPushforward e.inverse (Sieve.functorPushforward e.functor S) =
      Sieve.pullback (e.unitInv.app U) S := by ext; simp
/-
**CategoryTheory.Sieve.pullback_functorPushforward_equivalence_eq** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：pullback_functorPushforward_equivalence_eq {X : C} (S : Sieve X) : Sieve.p
ullback (e.unit.app X) (Sieve.functorPushforward e.inverse (Sieve.functorPushfor
ward e.functor S)) = S
参数：S : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Equivalence.functor_unit_comp`：functor_unit_comp (e : C ≌
 D) (X : C) : dsimp% e.functor.map (e.unit.app X) ≫ e.counit.app (e.functor.obj 
X) = 𝟙 (e.functor.obj X)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Equivalence.inv_fun_map`：inv_fun_map (e : C ≌ D) (X Y : C
) (f : X ⟶ Y) : e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.a
pp Y
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pullback_functorPushforward_equivalence_eq {X : C} (S : Sieve X) :
    Sieve.pullback (e.unit.app X) (Sieve.functorPushforward e.inverse
      (Sieve.functorPushforward e.functor S)) = S := by ext; simp
/-
**CategoryTheory.Sieve.mem_functorPushforward_iff_of_full** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Sieve`。
形式化陈述：mem_functorPushforward_iff_of_full [F.Full] {X Y : C} (R : Sieve X) (f : F
.obj Y ⟶ F.obj X) : (R.arrows.functorPushforward F) f ↔ exists (g : Y ⟶ X), F.ma
p g = f ∧ R g
参数：R : Sieve X；f : F.obj Y ⟶ F.obj X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma mem_functorPushforward_iff_of_full [F.Full] {X Y : C} (R : Sieve X) (f : F.obj Y ⟶ F.obj X) :
    (R.arrows.functorPushforward F) f ↔ ∃ (g : Y ⟶ X), F.map g = f ∧ R g := by
  refine ⟨fun ⟨Z, g, h, hg, hcomp⟩ ↦ ?_, fun ⟨g, hcomp, hg⟩ ↦ ?_⟩
  · obtain ⟨h', hh'⟩ := F.map_surjective h
    use h' ≫ g
    simp only [Functor.map_comp, hh', hcomp, true_and]
    apply R.downward_closed hg
  · use Y, g, 𝟙 _, hg
    simp [hcomp]
/-
**CategoryTheory.Sieve.mem_functorPushforward_iff_of_full_of_faithful** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：mem_functorPushforward_iff_of_full_of_faithful [F.Full] [F.Faithful] {X Y 
: C} (R : Sieve X) (f : Y ⟶ X) : (R.arrows.functorPushforward F) (F.map f) ↔ R f
参数：R : Sieve X；f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.mem_functorPushforward_iff_of_full`：mem_functorPush
forward_iff_of_full [F.Full] {X Y : C} (R : Sieve X) (f : F.obj Y ⟶ F.obj X) : (
R.arrows.functorPushforward F) f ↔ exists (g …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
-/
lemma mem_functorPushforward_iff_of_full_of_faithful [F.Full] [F.Faithful]
    {X Y : C} (R : Sieve X) (f : Y ⟶ X) :
    (R.arrows.functorPushforward F) (F.map f) ↔ R f := by
  rw [Sieve.mem_functorPushforward_iff_of_full]
  refine ⟨fun ⟨g, hcomp, hg⟩ ↦ ?_, fun hf ↦ ⟨f, rfl, hf⟩⟩
  rwa [← F.map_injective hcomp]
/-
**CategoryTheory.Sieve.functorPushforward_ofObjects_le** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Sieve`。
形式化陈述：functorPushforward_ofObjects_le {I : Type*} (X : I -> C) (Y : C) : (ofObje
cts X Y).functorPushforward F <= ofObjects (F.obj ∘ X) (F.obj Y)
参数：X : I -> C；Y : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorPushforward_ofObjects_le
    {I : Type*} (X : I → C) (Y : C) :
    (ofObjects X Y).functorPushforward F ≤ ofObjects (F.obj ∘ X) (F.obj Y) := by
  rintro Z f ⟨W, g₁, g₂, ⟨i, ⟨g₃⟩⟩, hf⟩
  exact ⟨i, ⟨g₂ ≫ F.map g₃⟩⟩

end Functor

/-- A sieve induces a presheaf. -/
@[simps obj map]
/-
**CategoryTheory.Sieve.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：functor (S : Sieve X) : Cᵒᵖ ⥤ Type v₁ where obj Y
参数：S : Sieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sieve induces a presheaf.
-/
def functor (S : Sieve X) : Cᵒᵖ ⥤ Type v₁ where
  obj Y := { g : Y.unop ⟶ X // S g }
  map f := ↾fun g ↦ ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩

/-- If a sieve S is contained in a sieve T, then we have a morphism of presheaves on their induced
presheaves.
-/
@[simps]
/-
**CategoryTheory.Sieve.natTransOfLe** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Si
eve`。
形式化陈述：natTransOfLe {S T : Sieve X} (h : S <= T) : S.functor ⟶ T.functor where ap
p _
参数：h : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a sieve S is contained in a sieve T, then we have a morphism of presheaves on
 their induced
presheaves.
-/
def natTransOfLe {S T : Sieve X} (h : S ≤ T) : S.functor ⟶ T.functor where
  app _ := ↾fun f ↦ ⟨f.1, h _ f.2⟩

/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simps]
/-
**CategoryTheory.Sieve.functorInclusion** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Sieve`。
形式化陈述：functorInclusion (S : Sieve X) : S.functor ⟶ yoneda.obj X where app _
参数：S : Sieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion from the functor induced by a sieve to the yoneda embeddin
g.
-/
def functorInclusion (S : Sieve X) : S.functor ⟶ yoneda.obj X where
  app _ := ↾fun f ↦ f.1

set_option backward.isDefEq.respectTransparency.types false in
/-- Any component `f : Y ⟶ X` of the sieve `S` induces a natural transformation from `yoneda.obj Y`
to the presheaf induced by `S`. -/
@[simps]
/-
**CategoryTheory.Sieve.toFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve
`。
形式化陈述：toFunctor (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f) : yoneda.obj Y ⟶ S.
functor where app Z
参数：S : Sieve X；f : Y ⟶ X；hf : S f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any component `f : Y ⟶ X` of the sieve `S` induces a natural transformation from
 `yoneda.obj Y`
to the presheaf induced by `S`.
-/
def toFunctor (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f) : yoneda.obj Y ⟶ S.functor where
  app Z := ↾fun g ↦ ⟨g ≫ f, S.downward_closed hf g⟩
/-
**CategoryTheory.Sieve.natTransOfLe_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：natTransOfLe_comm {S T : Sieve X} (h : S <= T) : natTransOfLe h ≫ functorI
nclusion _ = functorInclusion _
参数：h : S <= T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natTransOfLe_comm {S T : Sieve X} (h : S ≤ T) :
    natTransOfLe h ≫ functorInclusion _ = functorInclusion _ :=
  rfl

open ConcreteCategory

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
/-
**CategoryTheory.Sieve.functorInclusion_is_mono** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Sieve`。
形式化陈述：functorInclusion_is_mono : Mono S.functorInclusion
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X

--- 原说明 ---
The presheaf induced by a sieve is a subobject of the yoneda embedding.
-/
instance functorInclusion_is_mono : Mono S.functorInclusion :=
  ⟨fun f g h => by
    ext Y y
    simpa [Subtype.ext_iff] using congr_hom (NatTrans.congr_app h Y) y⟩

-- TODO: Show that when `f` is mono, this is right inverse to `functorInclusion` up to isomorphism.
/-- A natural transformation to a representable functor induces a sieve. This is the left inverse of
`functorInclusion`, shown in `sieveOfSubfunctor_functorInclusion`.
-/
@[simps]
/-
**CategoryTheory.Sieve.sieveOfSubfunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：sieveOfSubfunctor {R} (f : R ⟶ yoneda.obj X) : Sieve X where arrows Y g
参数：f : R ⟶ yoneda.obj X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation to a representable functor induces a sieve. This is the
 left inverse of
`functorInclusion`, shown in `sieveOfSubfunctor_functorInclusion`.
-/
def sieveOfSubfunctor {R} (f : R ⟶ yoneda.obj X) : Sieve X where
  arrows Y g := ∃ t, f.app (Opposite.op Y) t = g
  downward_closed := by
    rintro Y Z _ ⟨t, rfl⟩ g
    refine ⟨R.map g.op t, ?_⟩
    simp
/-
**CategoryTheory.Sieve.sieveOfSubfunctor_functorInclusion** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Sieve`。
形式化陈述：sieveOfSubfunctor_functorInclusion : sieveOfSubfunctor S.functorInclusion 
= S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sieve.sieveOfSubfunctor_apply`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X : C} {R : CategoryTheory.Functor Cᵒᵖ (Type 
v₁)}   (f : R ⟶ CategoryTheory.yon…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Sieve.functorInclusion_app`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {X : C} (S : CategoryTheory.Sieve X) (x : Cᵒᵖ),  
 S.functorInclusion.app x = Typ…
-/
theorem sieveOfSubfunctor_functorInclusion : sieveOfSubfunctor S.functorInclusion = S := by
  ext
  simp only [functorInclusion_app, sieveOfSubfunctor_apply]
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact hf
  · intro hf
    exact ⟨⟨_, hf⟩, rfl⟩
/-
**CategoryTheory.Sieve.functorInclusion_top_isIso** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Sieve`。
形式化陈述：functorInclusion_top_isIso : IsIso (⊤ : Sieve X).functorInclusion
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functorInclusion_top_isIso : IsIso (⊤ : Sieve X).functorInclusion :=
  ⟨⟨{ app := fun _ => ↾fun a => ⟨a, ⟨⟩⟩ }, rfl, rfl⟩⟩

/-- A variant of `Sieve.functor` with universe lifting. -/
/-
**CategoryTheory.Sieve.uliftFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Sieve`。
形式化陈述：uliftFunctor (S : Sieve X) : Cᵒᵖ ⥤ Type (max w v₁)
参数：S : Sieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `Sieve.functor` with universe lifting.
-/
abbrev uliftFunctor (S : Sieve X) : Cᵒᵖ ⥤ Type (max w v₁) :=
  S.functor ⋙ CategoryTheory.uliftFunctor

/-- A variant of `Sieve.natTransOfLe` with universe lifting. -/
@[simps]
/-
**CategoryTheory.Sieve.uliftNatTransOfLe** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：uliftNatTransOfLe {S T : Sieve X} (h : S <= T) : Sieve.uliftFunctor.{w} S 
⟶ Sieve.uliftFunctor.{w} T where app _
参数：h : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `Sieve.natTransOfLe` with universe lifting.
-/
def uliftNatTransOfLe {S T : Sieve X} (h : S ≤ T) :
    Sieve.uliftFunctor.{w} S ⟶ Sieve.uliftFunctor.{w} T where
  app _ := ↾fun f ↦ ⟨f.down.1, h _ f.down.2⟩

/-- A variant of `Sieve.functorInclusion` with universe lifting. -/
@[simps! app]
/-
**CategoryTheory.Sieve.uliftFunctorInclusion** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Sieve`。
形式化陈述：uliftFunctorInclusion (S : Sieve X) : S.uliftFunctor ⟶ uliftYoneda.{w}.obj
 X
参数：S : Sieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `Sieve.functorInclusion` with universe lifting.
-/
def uliftFunctorInclusion (S : Sieve X) :
    S.uliftFunctor ⟶ uliftYoneda.{w}.obj X :=
  Functor.whiskerRight S.functorInclusion CategoryTheory.uliftFunctor

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `Sieve.toFunctor` with universe lifting. -/
@[simps]
/-
**CategoryTheory.Sieve.toUliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Sieve`。
形式化陈述：toUliftFunctor (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f) : uliftYoneda.
{w}.obj Y ⟶ Sieve.uliftFunctor.{w} S where app Z
参数：S : Sieve X；f : Y ⟶ X；hf : S f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `Sieve.toFunctor` with universe lifting.
-/
def toUliftFunctor (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f) :
    uliftYoneda.{w}.obj Y ⟶ Sieve.uliftFunctor.{w} S where
  app Z := ↾fun g ↦ ⟨g.down ≫ f, S.downward_closed hf g.down⟩
/-
**CategoryTheory.Sieve.uliftNatTransOfLe_comm** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Sieve`。
形式化陈述：uliftNatTransOfLe_comm {S T : Sieve X} (h : S <= T) : uliftNatTransOfLe.{w
} h ≫ uliftFunctorInclusion.{w} _ = uliftFunctorInclusion.{w} _
参数：h : S <= T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uliftNatTransOfLe_comm {S T : Sieve X} (h : S ≤ T) :
    uliftNatTransOfLe.{w} h ≫ uliftFunctorInclusion.{w} _ = uliftFunctorInclusion.{w} _ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
/-
**CategoryTheory.Sieve.uliftFunctorInclusion_is_mono** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Sieve`。
形式化陈述：uliftFunctorInclusion_is_mono (S : Sieve X) : Mono (Sieve.uliftFunctorIncl
usion.{w} S)
参数：S : Sieve X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `ULift.up.injEq`：∀ {α : Type s} (down down_1 : α), ({ down := down } = { 
down := down_1 }) = (down = down_1)
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X

--- 原说明 ---
The presheaf induced by a sieve is a subobject of the yoneda embedding.
-/
instance uliftFunctorInclusion_is_mono (S : Sieve X) :
    Mono (Sieve.uliftFunctorInclusion.{w} S) :=
  ⟨fun _ _ h => by
    ext Y y
    refine ULift.ext _ _ (Subtype.ext_iff.2 ?_)
    simpa using congr_hom (NatTrans.congr_app h Y) y⟩

/-- A variant of `Sieve.sieveOfSubfunctor` with universe lifting. -/
@[simps]
/-
**CategoryTheory.Sieve.sieveOfUliftSubfunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Sieve`。
形式化陈述：sieveOfUliftSubfunctor {R : Cᵒᵖ ⥤ Type max w v₁} (f : R ⟶ uliftYoneda.{w}.
obj X) : Sieve X where arrows Y g
参数：f : R ⟶ uliftYoneda.{w}.obj X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `Sieve.sieveOfSubfunctor` with universe lifting.
-/
def sieveOfUliftSubfunctor {R : Cᵒᵖ ⥤ Type max w v₁} (f : R ⟶ uliftYoneda.{w}.obj X) :
    Sieve X where
  arrows Y g := ∃ t, f.app (Opposite.op Y) t = { down := g }
  downward_closed := by
    intro Y Z _ ⟨t, ht⟩ g
    refine ⟨R.map g.op t, ?_⟩
    simp [ht]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Sieve.sieveOfUliftSubfunctor_uliftFunctorInclusion** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：sieveOfUliftSubfunctor_uliftFunctorInclusion {S : Sieve X} : Sieve.sieveOf
UliftSubfunctor.{w} (S.uliftFunctorInclusion) = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ULift.up.injEq`：∀ {α : Type s} (down down_1 : α), ({ down := down } = { 
down := down_1 }) = (down = down_1)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sieveOfUliftSubfunctor_uliftFunctorInclusion {S : Sieve X} :
    Sieve.sieveOfUliftSubfunctor.{w} (S.uliftFunctorInclusion) = S := by
  cat_disch
/-
**CategoryTheory.Sieve.uliftFunctorInclusion_top_isIso** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Sieve`。
形式化陈述：uliftFunctorInclusion_top_isIso : IsIso (Sieve.uliftFunctorInclusion.{w} (
⊤ : Sieve X))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uliftFunctorInclusion_top_isIso : IsIso (Sieve.uliftFunctorInclusion.{w} (⊤ : Sieve X)) :=
  ⟨⟨{ app := fun _ ↦ ↾fun a ↦ ⟨a.down, ⟨⟩⟩ }, rfl, rfl⟩⟩
/-
**CategoryTheory.Sieve.ofArrows_eq_pullback_of_isPullback** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Sieve`。
形式化陈述：ofArrows_eq_pullback_of_isPullback {ι : Type*} {S : C} {X : ι -> C} (f : (
i : ι) -> X i ⟶ S) {Y : C} {g : Y ⟶ S} {P : ι -> C} {p₁ : (i : ι) -> P i ⟶ Y} {p
₂ : (i : ι) -> P i ⟶ X i} (h : forall (i : ι), IsPullback (p₁ i) (p₂ i) g (f i))
 : Sieve.ofArrows P p₁ = Sieve.pullback g (Sieve.ofArrows X f)
参数：f : (i : ι) -> X i ⟶ S；i : ι；i : ι；h : forall (i : ι), IsPullback (p₁ i) (p₂ 
i) g (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.ofArrows.eq_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {I : Type u_1} {X : C} (Y : I → C) (f : (i : I) → Y i ⟶ 
X),   CategoryTheory.Sie…
· 使用定理 `CategoryTheory.Sieve.generate_le_iff`：generate_le_iff (R : Presieve X) (
S : Sieve X) : generate R <= S ↔ R <= S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.IsPullback.lift_fst`：lift_fst (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofArrows_eq_pullback_of_isPullback {ι : Type*} {S : C} {X : ι → C} (f : (i : ι) → X i ⟶ S)
    {Y : C} {g : Y ⟶ S} {P : ι → C} {p₁ : (i : ι) → P i ⟶ Y} {p₂ : (i : ι) → P i ⟶ X i}
    (h : ∀ (i : ι), IsPullback (p₁ i) (p₂ i) g (f i)) :
    Sieve.ofArrows P p₁ = Sieve.pullback g (Sieve.ofArrows X f) := by
  refine le_antisymm ?_ ?_
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    use X i, p₂ i, f i, ⟨i⟩
    exact (h i).w.symm
  · rintro W u ⟨Z, v, s, ⟨i⟩, heq⟩
    use P i, (h i).lift u v heq.symm, p₁ i, ⟨i⟩
    simp

/-- If `C` is `w`-locally small, any sieve induces a subfunctor of `shrinkYoneda.{w}.obj X`. -/
@[simps, pp_with_univ]
/-
**CategoryTheory.Sieve.shrinkFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
ieve`。
形式化陈述：shrinkFunctor [LocallySmall.{w} C] {X : C} (S : Sieve X) : Subfunctor (shr
inkYoneda.{w}.obj X) where obj Y
参数：S : Sieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is `w`-locally small, any sieve induces a subfunctor of `shrinkYoneda.{w}
.obj X`.
-/
def shrinkFunctor [LocallySmall.{w} C] {X : C} (S : Sieve X) :
    Subfunctor (shrinkYoneda.{w}.obj X) where
  obj Y := { f | S (shrinkYonedaObjObjEquiv f) }
  map {Y Z} g f hf := by
    simpa [shrinkYonedaObjObjEquiv_obj_map] using S.downward_closed hf _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (S) in
/-- `Sieve.shrinkFunctor` is compatible with universe lifting. -/
noncomputable
/-
**CategoryTheory.Sieve.shrinkFunctorUliftFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Sieve`。
形式化陈述：shrinkFunctorUliftFunctorIso [LocallySmall.{w} C] [LocallySmall.{max w' w}
 C] : (shrinkFunctor.{w} S).toFunctor ⋙ CategoryTheory.uliftFunctor.{w', w} ≅ (s
hrinkFunctor.{max w' w} S).toFunctor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def shrinkFunctorUliftFunctorIso [LocallySmall.{w} C] [LocallySmall.{max w' w} C] :
    (shrinkFunctor.{w} S).toFunctor ⋙ CategoryTheory.uliftFunctor.{w', w} ≅
      (shrinkFunctor.{max w' w} S).toFunctor :=
  NatIso.ofComponents
    (fun X ↦ Equiv.toIso
      (.trans Equiv.ulift
        (Equiv.subtypeEquiv (shrinkYonedaObjObjEquiv.trans shrinkYonedaObjObjEquiv.symm)
        fun a ↦ by simp)))
    fun {U V} f ↦ by
      dsimp
      ext
      dsimp [Equiv.subtypeEquiv_apply]
      rw [shrinkYonedaObjObjEquiv_obj_map, shrinkYonedaObjObjEquiv_symm_comp]
      simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Sieve.shrinkFunctorUliftFunctorIso_inv_** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Sieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shrinkFunctorUliftFunctorIso_inv_ι [LocallySmall.{w} C] [LocallySmall.{max w' w} C] :
    (shrinkFunctorUliftFunctorIso.{w, w'} S).inv ≫
      Functor.whiskerRight (shrinkFunctor.{w} _).ι CategoryTheory.uliftFunctor.{w', w} =
    (shrinkFunctor.{max w' w} S).ι ≫
      shrinkYonedaUliftFunctorIso.{w, w'}.inv.app X :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (S) in
/-- Shrinking does nothing for the same universe level. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.Sieve.shrinkFunctorIsoFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Sieve`。
形式化陈述：shrinkFunctorIsoFunctor : (shrinkFunctor.{v₁} S).toFunctor ≅ S.functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C

--- 原说明 ---
Shrinking does nothing for the same universe level.
-/
noncomputable def shrinkFunctorIsoFunctor : (shrinkFunctor.{v₁} S).toFunctor ≅ S.functor :=
  NatIso.ofComponents (fun Y ↦ Equiv.toIso <| Equiv.subtypeEquiv shrinkYonedaObjObjEquiv (by simp))
    fun {U V} f ↦ by
      dsimp [Equiv.subtypeEquiv_apply]
      ext
      simp [shrinkYonedaObjObjEquiv_obj_map]

end Sieve

/-
**CategoryTheory.Presieve.functorPullback_arrows** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Presieve`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 {X : C} (S : CategoryTheory.Sieve (F.obj X)),   CategoryTheory.Presieve.functor
Pullback F S.arrows = (CategoryTheory.Sieve.functorPullback F S).arrows
参数：F : CategoryTheory.Functor C D；S : CategoryTheory.Sieve (F.obj X)；CategoryThe
ory.Sieve.functorPullback F S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Presieve.functorPullback_arrows {X : C} (S : Sieve (F.obj X)) :
    Presieve.functorPullback F S.arrows = Sieve.functorPullback F S :=
  rfl
/-
**CategoryTheory.Presieve.map_le_functorPushforward** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Presieve`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 {X : C} (S : CategoryTheory.Presieve X),   CategoryTheory.Presieve.map F S ≤ Ca
tegoryTheory.Presieve.functorPushforward F S
参数：F : CategoryTheory.Functor C D；S : CategoryTheory.Presieve X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.arrows_generate_map_eq_functorPushforward`：arrows_g
enerate_map_eq_functorPushforward {s : Presieve X} : (generate (s.map F)).arrows
 = s.functorPushforward F
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
-/
theorem Presieve.map_le_functorPushforward (S : Presieve X) : S.map F ≤ S.functorPushforward F := by
  grw [← Sieve.arrows_generate_map_eq_functorPushforward, ← Sieve.le_generate]
/-
**CategoryTheory.Presieve.bind_ofArrows_le_bindOfArrows** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Presieve`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {ι : Type u_1}
 {X : C} (Z : ι → C) (f : (i : ι) → Z i ⟶ X)   (R : (i : ι) → CategoryTheory.Pre
sieve (Z i)),   (CategoryTheory.Sieve.bind (CategoryTheory.Sieve.ofArrows Z f).a
rrows fun x x_1 hg =>       CategoryTheory.Sieve.pullback (CategoryTheory.Sieve.
ofArrows.h hg)         (CategoryTheory.Sieve.generate (R (CategoryTheory.Sieve.o
fArrows.i hg)))) ≤     CategoryTheory.Sieve.generate (CategoryTheory.Presieve.bi
ndOfArrows Z f R)
参数：Z : ι → C；f : (i : ι) → Z i ⟶ X；R : (i : ι) → CategoryTheory.Presieve (Z i)；C
ategoryTheory.Sieve.bind (CategoryTheory.Sieve.ofArrows Z f).arrows fun x x_1 hg
 =>       CategoryTheory.Sieve.pullback (CategoryTheory.Sieve.ofArrows.h hg)    
     (CategoryTheory.Sieve.generate (R (CategoryTheory.Sieve.ofArrows.i hg)))；Ca
tegoryTheory.Presieve.bindOfArrows Z f R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.ofArrows.fac`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {I : Type u_1} {X : C} {Y : I → C} {f : (i : I) → Y i ⟶ X
}   {W : C} {g : W ⟶ X}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
lemma Presieve.bind_ofArrows_le_bindOfArrows {ι : Type*} {X : C} (Z : ι → C)
    (f : ∀ i, Z i ⟶ X) (R : ∀ i, Presieve (Z i)) :
    Sieve.bind (Sieve.ofArrows Z f)
      (fun _ _ hg ↦ Sieve.pullback
        (Sieve.ofArrows.h hg) (.generate <| R (Sieve.ofArrows.i hg))) ≤
    Sieve.generate (Presieve.bindOfArrows Z f R) := by
  rintro T g ⟨W, v, v', hv', ⟨S, u, u', h, hu⟩, rfl⟩
  rw [← Sieve.ofArrows.fac hv', ← reassoc_of% hu]
  exact ⟨S, u, u' ≫ f _, ⟨_, _, h⟩, rfl⟩

@[deprecated "Use Sieve.arrows_generate_map_eq_functorPushforward instead." (since := "2026-07-09")]
/-
**CategoryTheory.Presieve.functorPushforward_overForget** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Presieve`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {S : C} {X : C
ategoryTheory.Over S}   (R : CategoryTheory.Presieve X),   CategoryTheory.Presie
ve.functorPushforward (CategoryTheory.Over.forget S) R =     (CategoryTheory.Sie
ve.generate (CategoryTheory.Presieve.map (CategoryTheory.Over.forget S) R)).arro
ws
参数：R : CategoryTheory.Presieve X；CategoryTheory.Over.forget S；CategoryTheory.Sie
ve.generate (CategoryTheory.Presieve.map (CategoryTheory.Over.forget S) R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.arrows_generate_map_eq_functorPushforward`：arrows_g
enerate_map_eq_functorPushforward {s : Presieve X} : (generate (s.map F)).arrows
 = s.functorPushforward F
-/
lemma Presieve.functorPushforward_overForget
    {S : C} {X : Over S} (R : Presieve X) :
    Presieve.functorPushforward (Over.forget S) R =
      (Sieve.generate (Presieve.map (Over.forget S) R)).arrows :=
  (Sieve.arrows_generate_map_eq_functorPushforward (Over.forget S)).symm

end CategoryTheory

-- pushed over the edge in `nightly-testing`, should be split after landing on master
set_option linter.style.longFile 1600

