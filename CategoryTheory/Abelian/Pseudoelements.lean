/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Pseudoelements in abelian categories

A *pseudoelement* of an object `X` in an abelian category `C` is an equivalence class of arrows
ending in `X`, where two arrows are considered equivalent if we can find two epimorphisms with a
common domain making a commutative square with the two arrows. While the construction shows that
pseudoelements are actually subobjects of `X` rather than "elements", it is possible to chase these
pseudoelements through commutative diagrams in an abelian category to prove exactness properties.
This is done using some "diagram-chasing metatheorems" proved in this file. In many cases, a proof
in the category of abelian groups can more or less directly be converted into a proof using
pseudoelements.

A classic application of pseudoelements is diagram lemmas like the four lemma or the snake lemma.

Pseudoelements are in some ways weaker than actual elements in a concrete category. The most
important limitation is that there is no extensionality principle: If `f g : X ⟶ Y`, then
`∀ x ∈ X, f x = g x` does not necessarily imply that `f = g` (however, if `f = 0` or `g = 0`,
it does). A corollary of this is that we cannot define arrows in abelian categories by dictating
their action on pseudoelements. Thus, a usual style of proofs in abelian categories is this:
First, we construct some morphism using universal properties, and then we use diagram chasing
of pseudoelements to verify that it has some desirable property such as exactness.

It should be noted that the Freyd-Mitchell embedding theorem
(see `CategoryTheory.Abelian.FreydMitchell`) gives a vastly stronger notion of
pseudoelement (in particular one that gives extensionality) and this file should be updated to
go use that instead!

## Main results

We define the type of pseudoelements of an object and, in particular, the zero pseudoelement.

We prove that every morphism maps the zero pseudoelement to the zero pseudoelement (`apply_zero`)
and that a zero morphism maps every pseudoelement to the zero pseudoelement (`zero_apply`).

Here are the metatheorems we provide:
* A morphism `f` is zero if and only if it is the zero function on pseudoelements.
* A morphism `f` is an epimorphism if and only if it is surjective on pseudoelements.
* A morphism `f` is a monomorphism if and only if it is injective on pseudoelements
  if and only if `∀ a, f a = 0 → f = 0`.
* A sequence `f, g` of morphisms is exact if and only if
  `∀ a, g (f a) = 0` and `∀ b, g b = 0 → ∃ a, f a = b`.
* If `f` is a morphism and `a, a'` are such that `f a = f a'`, then there is some
  pseudoelement `a''` such that `f a'' = 0` and for every `g` we have
  `g a' = 0 → g a = g a''`. We can think of `a''` as `a - a'`, but don't get too carried away
  by that: pseudoelements of an object do not form an abelian group.

## Notation

We introduce coercions from an object of an abelian category to the set of its pseudoelements
and from a morphism to the function it induces on pseudoelements.

These coercions must be explicitly enabled via local instances:
`attribute [local instance] objectToSort homToFun`

## Implementation notes

It appears that sometimes the coercion from morphisms to functions does not work, i.e.,
writing `g a` raises a "function expected" error. This error can be fixed by writing
`(g : X ⟶ Y) a`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

@[expose] public section


open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Abelian

open CategoryTheory.Preadditive

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C]

attribute [local instance] Over.coeFromHom

/-- This is just composition of morphisms in `C`. Another way to express this would be
`(Over.map f).obj a`, but our definition has nicer definitional properties. -/
/-
**CategoryTheory.Abelian.app** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：app {P Q : C} (f : P ⟶ Q) (a : Over P) : Over Q
参数：f : P ⟶ Q；a : Over P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is just composition of morphisms in `C`. Another way to express this would 
be
`(Over.map f).obj a`, but our definition has nicer definitional properties.
-/
def app {P Q : C} (f : P ⟶ Q) (a : Over P) : Over Q :=
  a.hom ≫ f

@[simp]
/-
**CategoryTheory.Abelian.app_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Abeli
an`。
形式化陈述：app_hom {P Q : C} (f : P ⟶ Q) (a : Over P) : (app f a).hom = a.hom ≫ f
参数：f : P ⟶ Q；a : Over P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_hom {P Q : C} (f : P ⟶ Q) (a : Over P) : (app f a).hom = a.hom ≫ f := rfl

/-- Two arrows `f : X ⟶ P` and `g : Y ⟶ P` are called pseudo-equal if there is some object
`R` and epimorphisms `p : R ⟶ X` and `q : R ⟶ Y` such that `p ≫ f = q ≫ g`. -/
/-
**CategoryTheory.Abelian.PseudoEqual** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.A
belian`。
形式化陈述：PseudoEqual (P : C) (f g : Over P) : Prop
参数：P : C；f g : Over P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two arrows `f : X ⟶ P` and `g : Y ⟶ P` are called pseudo-equal if there is some 
object
`R` and epimorphisms `p : R ⟶ X` and `q : R ⟶ Y` such that `p ≫ f = q ≫ g`.
-/
def PseudoEqual (P : C) (f g : Over P) : Prop :=
  ∃ (R : C) (p : R ⟶ f.1) (q : R ⟶ g.1) (_ : Epi p) (_ : Epi q), p ≫ f.hom = q ≫ g.hom
/-
**CategoryTheory.Abelian.pseudoEqual_refl** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Abelian`。
形式化陈述：pseudoEqual_refl {P : C} : Std.Refl (PseudoEqual P) where refl f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance pseudoEqual_refl {P : C} : Std.Refl (PseudoEqual P) where
  refl f := ⟨f.1, 𝟙 f.1, 𝟙 f.1, inferInstance, inferInstance, by simp⟩
/-
**CategoryTheory.Abelian.pseudoEqual_symm** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Abelian`。
形式化陈述：pseudoEqual_symm {P : C} : Std.Symm (PseudoEqual P) where symm _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance pseudoEqual_symm {P : C} : Std.Symm (PseudoEqual P) where
  symm _ _ := fun ⟨R, p, q, ep, Eq, comm⟩ ↦ ⟨R, q, p, Eq, ep, comm.symm⟩

variable [Abelian.{v} C]

section

/-- Pseudoequality is transitive: Just take the pullback. The pullback morphisms will
be epimorphisms since in an abelian category, pullbacks of epimorphisms are epimorphisms. -/
/-
**CategoryTheory.Abelian.pseudoEqual_trans** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Abelian`。
形式化陈述：pseudoEqual_trans {P : C} : IsTrans (Over P) (PseudoEqual P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…

--- 原说明 ---
Pseudoequality is transitive: Just take the pullback. The pullback morphisms wil
l
be epimorphisms since in an abelian category, pullbacks of epimorphisms are epim
orphisms.
-/
instance pseudoEqual_trans {P : C} : IsTrans (Over P) (PseudoEqual P) := by
  refine ⟨fun f g h ⟨R, p, q, ep, Eq, comm⟩ ⟨R', p', q', ep', eq', comm'⟩ ↦ ?_⟩
  refine ⟨pullback q p', pullback.fst _ _ ≫ p, pullback.snd _ _ ≫ q',
    epi_comp _ _, epi_comp _ _, ?_⟩
  rw [Category.assoc, comm, ← Category.assoc, pullback.condition, Category.assoc, comm',
    Category.assoc]

end

/-- The arrows with codomain `P` equipped with the equivalence relation of being pseudo-equal. -/
@[instance_reducible]
/-
**CategoryTheory.Abelian.Pseudoelement.setoid** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Abelian.Pseudoelement`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheo
ry.Abelian C] → (P : C) → Setoid (CategoryTheory.Over P)
参数：P : C；CategoryTheory.Over P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The arrows with codomain `P` equipped with the equivalence relation of being pse
udo-equal.
-/
def Pseudoelement.setoid (P : C) : Setoid (Over P) :=
  ⟨_, ⟨pseudoEqual_refl.refl, pseudoEqual_symm.symm _ _, pseudoEqual_trans.trans _ _ _⟩⟩

attribute [local instance] Pseudoelement.setoid

/-- A `Pseudoelement` of `P` is just an equivalence class of arrows ending in `P` by being
pseudo-equal. -/
/-
**CategoryTheory.Abelian.Pseudoelement** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Abelian`。
形式化陈述：Pseudoelement (P : C) : Type max u v
参数：P : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Pseudoelement` of `P` is just an equivalence class of arrows ending in `P` by
 being
pseudo-equal.
-/
def Pseudoelement (P : C) : Type max u v :=
  Quotient (Pseudoelement.setoid P)

namespace Pseudoelement

/-- A coercion from an object of an abelian category to its pseudoelements. -/
@[instance_reducible]
/-
**CategoryTheory.Abelian.Pseudoelement.objectToSort** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Abelian.Pseudoelement`。
形式化陈述：objectToSort : CoeSort C (Type max u v)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coercion from an object of an abelian category to its pseudoelements.
-/
def objectToSort : CoeSort C (Type max u v) :=
  ⟨fun P => Pseudoelement P⟩

attribute [local instance] objectToSort

scoped[Pseudoelement] attribute [instance] CategoryTheory.Abelian.Pseudoelement.objectToSort

/-- A coercion from an arrow with codomain `P` to its associated pseudoelement. -/
@[instance_reducible]
/-
**CategoryTheory.Abelian.Pseudoelement.overToSort** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Abelian.Pseudoelement`。
形式化陈述：overToSort {P : C} : Coe (Over P) (Pseudoelement P)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coercion from an arrow with codomain `P` to its associated pseudoelement.
-/
def overToSort {P : C} : Coe (Over P) (Pseudoelement P) :=
  ⟨Quot.mk (PseudoEqual P)⟩

attribute [local instance] overToSort
/-
**CategoryTheory.Abelian.Pseudoelement.over_coe_def** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Abelian.Pseudoelement`。
形式化陈述：over_coe_def {P Q : C} (a : Q ⟶ P) : (a : Pseudoelement P) = ⟦↑a⟧
参数：a : Q ⟶ P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem over_coe_def {P Q : C} (a : Q ⟶ P) : (a : Pseudoelement P) = ⟦↑a⟧ := rfl

/-- If two elements are pseudo-equal, then their composition with a morphism is, too. -/
/-
**CategoryTheory.Abelian.Pseudoelement.pseudoApply_aux** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：pseudoApply_aux {P Q : C} (f : P ⟶ Q) (a b : Over P) : a ≈ b -> app f a ≈ 
app f b
参数：f : P ⟶ Q；a b : Over P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h

--- 原说明 ---
If two elements are pseudo-equal, then their composition with a morphism is, too
.
-/
theorem pseudoApply_aux {P Q : C} (f : P ⟶ Q) (a b : Over P) : a ≈ b → app f a ≈ app f b :=
  fun ⟨R, p, q, ep, Eq, comm⟩ =>
  ⟨R, p, q, ep, Eq, show p ≫ a.hom ≫ f = q ≫ b.hom ≫ f by rw [reassoc_of% comm]⟩

/-- A morphism `f` induces a function `pseudoApply f` on pseudoelements. -/
/-
**CategoryTheory.Abelian.Pseudoelement.pseudoApply** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Abelian.Pseudoelement`。
形式化陈述：pseudoApply {P Q : C} (f : P ⟶ Q) : P -> Q
参数：f : P ⟶ Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.pseudoApply_aux`：pseudoApply_aux {P
 Q : C} (f : P ⟶ Q) (a b : Over P) : a ≈ b -> app f a ≈ app f b

--- 原说明 ---
A morphism `f` induces a function `pseudoApply f` on pseudoelements.
-/
def pseudoApply {P Q : C} (f : P ⟶ Q) : P → Q :=
  Quotient.map (fun g : Over P => app f g) (pseudoApply_aux f)

/-- A coercion from morphisms to functions on pseudoelements. -/
@[instance_reducible]
/-
**CategoryTheory.Abelian.Pseudoelement.homToFun** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Abelian.Pseudoelement`。
形式化陈述：homToFun {P Q : C} : CoeFun (P ⟶ Q) fun _ => P -> Q
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coercion from morphisms to functions on pseudoelements.
-/
def homToFun {P Q : C} : CoeFun (P ⟶ Q) fun _ => P → Q :=
  ⟨pseudoApply⟩

attribute [local instance] homToFun

scoped[Pseudoelement] attribute [instance] CategoryTheory.Abelian.Pseudoelement.homToFun
/-
**CategoryTheory.Abelian.Pseudoelement.pseudoApply_mk'** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：pseudoApply_mk' {P Q : C} (f : P ⟶ Q) (a : Over P) : f ⟦a⟧ = ⟦↑(a.hom ≫ f)
⟧
参数：f : P ⟶ Q；a : Over P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pseudoApply_mk' {P Q : C} (f : P ⟶ Q) (a : Over P) : f ⟦a⟧ = ⟦↑(a.hom ≫ f)⟧ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying a pseudoelement to a composition of morphisms is the same as composing
with each morphism. Sadly, this is not a definitional equality, but at least it is true. -/
/-
**CategoryTheory.Abelian.Pseudoelement.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Abelian.Pseudoelement`。
形式化陈述：comp_apply {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (a : P) : (f ≫ g) a = g (f 
a)
参数：f : P ⟶ Q；g : Q ⟶ R；a : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Over.coe_hom`：coe_hom {X Y : T} (f : Y ⟶ X) : (f : Over X
).hom = f
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a

--- 原说明 ---
Applying a pseudoelement to a composition of morphisms is the same as composing
with each morphism. Sadly, this is not a definitional equality, but at least it 
is true.
-/
theorem comp_apply {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (a : P) : (f ≫ g) a = g (f a) :=
  Quotient.inductionOn a fun x =>
    Quotient.sound <| by
      simp only [app]
      rw [← Category.assoc, Over.coe_hom]

/-- Composition of functions on pseudoelements is composition of morphisms. -/
/-
**CategoryTheory.Abelian.Pseudoelement.comp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Abelian.Pseudoelement`。
形式化陈述：comp_comp {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : g ∘ f = f ≫ g
参数：f : P ⟶ Q；g : Q ⟶ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.comp_apply`：comp_apply {P Q R : C} 
(f : P ⟶ Q) (g : Q ⟶ R) (a : P) : (f ≫ g) a = g (f a)

--- 原说明 ---
Composition of functions on pseudoelements is composition of morphisms.
-/
theorem comp_comp {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : g ∘ f = f ≫ g :=
  funext fun _ => (comp_apply _ _ _).symm

section Zero

/-!
In this section we prove that for every `P` there is an equivalence class that contains
precisely all the zero morphisms ending in `P` and use this to define *the* zero
pseudoelement.
-/


section

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

set_option backward.isDefEq.respectTransparency false in
/-- The arrows pseudo-equal to a zero morphism are precisely the zero morphisms. -/
/-
**CategoryTheory.Abelian.Pseudoelement.pseudoZero_aux** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：pseudoZero_aux {P : C} (Q : C) (f : Over P) : f ≈ (0 : Q ⟶ P) ↔ f.hom = 0
参数：Q : C；f : Over P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.zero_of_epi_comp`：zero_of_epi_comp {X Y Z : C} (f 
: X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0) : g = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadd
itive C]   [CategoryTheory.Limits.HasBinaryProducts …
· 使用定理 `CategoryTheory.Abelian.has_finite_products`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory
.Limits.HasFiniteProducts C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsRegularEpi`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {B X : C} {f : X ⟶ B} [h : CategoryTheory.IsR
egularEpi f],   CategoryTheory.Effe…
· 使用定理 `CategoryTheory.instIsRegularEpiOfIsSplitEpi`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplitEp
i f],   CategoryTheory.IsRegularE…
· 使用定理 `CategoryTheory.Limits.biprod.fst_epi`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Limits.biprod.snd_epi`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y : C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Over.coe_hom`：coe_hom {X Y : T} (f : Y ⟶ X) : (f : Over X
).hom = f
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.comp_zero`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) (Z : C), …

--- 原说明 ---
The arrows pseudo-equal to a zero morphism are precisely the zero morphisms.
-/
theorem pseudoZero_aux {P : C} (Q : C) (f : Over P) : f ≈ (0 : Q ⟶ P) ↔ f.hom = 0 :=
  ⟨fun ⟨R, p, q, _, _, comm⟩ => zero_of_epi_comp p (by simp [comm]), fun hf =>
    ⟨biprod f.1 Q, biprod.fst, biprod.snd, inferInstance, inferInstance, by
      rw [hf, Over.coe_hom, HasZeroMorphisms.comp_zero, HasZeroMorphisms.comp_zero]⟩⟩

end

/-
**CategoryTheory.Abelian.Pseudoelement.zero_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：zero_eq_zero' {P Q R : C} : (⟦((0 : Q ⟶ P) : Over P)⟧ : Pseudoelement P) =
 ⟦((0 : R ⟶ P) : Over P)⟧
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.pseudoZero_aux`：pseudoZero_aux {P :
 C} (Q : C) (f : Over P) : f ≈ (0 : Q ⟶ P) ↔ f.hom = 0
-/
theorem zero_eq_zero' {P Q R : C} :
    (⟦((0 : Q ⟶ P) : Over P)⟧ : Pseudoelement P) = ⟦((0 : R ⟶ P) : Over P)⟧ :=
  Quotient.sound <| (pseudoZero_aux R _).2 rfl

/-- The zero pseudoelement is the class of a zero morphism. -/
/-
**CategoryTheory.Abelian.Pseudoelement.pseudoZero** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Abelian.Pseudoelement`。
形式化陈述：pseudoZero {P : C} : P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero pseudoelement is the class of a zero morphism.
-/
def pseudoZero {P : C} : P :=
  ⟦(0 : P ⟶ P)⟧
/-
**CategoryTheory.Abelian.Pseudoelement.hasZero** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Abelian.Pseudoelement`。
形式化陈述：hasZero {P : C} : Zero P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasZero {P : C} : Zero P :=
  ⟨pseudoZero⟩
/-
**CategoryTheory.Abelian.Pseudoelement.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Abelian.Pseudoelement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : C} : Inhabited P :=
  ⟨0⟩
/-
**CategoryTheory.Abelian.Pseudoelement.pseudoZero_def** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：pseudoZero_def {P : C} : (0 : Pseudoelement P) = ⟦↑(0 : P ⟶ P)⟧
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pseudoZero_def {P : C} : (0 : Pseudoelement P) = ⟦↑(0 : P ⟶ P)⟧ := rfl

@[simp]
/-
**CategoryTheory.Abelian.Pseudoelement.zero_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Abelian.Pseudoelement`。
形式化陈述：zero_eq_zero {P Q : C} : ⟦((0 : Q ⟶ P) : Over P)⟧ = (0 : Pseudoelement P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.zero_eq_zero'`：zero_eq_zero' {P Q R
 : C} : (⟦((0 : Q ⟶ P) : Over P)⟧ : Pseudoelement P) = ⟦((0 : R ⟶ P) : Over P)⟧
-/
theorem zero_eq_zero {P Q : C} : ⟦((0 : Q ⟶ P) : Over P)⟧ = (0 : Pseudoelement P) :=
  zero_eq_zero'

/-- The pseudoelement induced by an arrow is zero precisely when that arrow is zero. -/
/-
**CategoryTheory.Abelian.Pseudoelement.pseudoZero_iff** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：pseudoZero_iff {P : C} (a : Over P) : a = (0 : P) ↔ a.hom = 0
参数：a : Over P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.pseudoZero_aux`：pseudoZero_aux {P :
 C} (Q : C) (f : Over P) : f ≈ (0 : Q ⟶ P) ↔ f.hom = 0
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b

--- 原说明 ---
The pseudoelement induced by an arrow is zero precisely when that arrow is zero.
-/
theorem pseudoZero_iff {P : C} (a : Over P) : a = (0 : P) ↔ a.hom = 0 := by
  rw [← pseudoZero_aux P a]
  exact Quotient.eq'

end Zero


set_option backward.defeqAttrib.useBackward true in
/-- Morphisms map the zero pseudoelement to the zero pseudoelement. -/
@[simp]
/-
**CategoryTheory.Abelian.Pseudoelement.apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Abelian.Pseudoelement`。
形式化陈述：apply_zero {P Q : C} (f : P ⟶ Q) : f 0 = 0
参数：f : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.pseudoZero_def`：pseudoZero_def {P :
 C} : (0 : Pseudoelement P) = ⟦↑(0 : P ⟶ P)⟧
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.pseudoApply_mk'`：pseudoApply_mk' {P
 Q : C} (f : P ⟶ Q) (a : Over P) : f ⟦a⟧ = ⟦↑(a.hom ≫ f)⟧
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.zero_eq_zero`：zero_eq_zero {P Q : C
} : ⟦((0 : Q ⟶ P) : Over P)⟧ = (0 : Pseudoelement P)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Morphisms map the zero pseudoelement to the zero pseudoelement.
-/
theorem apply_zero {P Q : C} (f : P ⟶ Q) : f 0 = 0 := by
  rw [pseudoZero_def, pseudoApply_mk']
  simp

/-- The zero morphism maps every pseudoelement to 0. -/
@[simp]
/-
**CategoryTheory.Abelian.Pseudoelement.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Abelian.Pseudoelement`。
形式化陈述：zero_apply {P : C} (Q : C) (a : P) : (0 : P ⟶ Q) a = 0
参数：Q : C；a : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.pseudoZero_def`：pseudoZero_def {P :
 C} : (0 : Pseudoelement P) = ⟦↑(0 : P ⟶ P)⟧
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.pseudoApply_mk'`：pseudoApply_mk' {P
 Q : C} (f : P ⟶ Q) (a : Over P) : f ⟦a⟧ = ⟦↑(a.hom ≫ f)⟧
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.zero_eq_zero`：zero_eq_zero {P Q : C
} : ⟦((0 : Q ⟶ P) : Over P)⟧ = (0 : Pseudoelement P)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The zero morphism maps every pseudoelement to 0.
-/
theorem zero_apply {P : C} (Q : C) (a : P) : (0 : P ⟶ Q) a = 0 :=
  Quotient.inductionOn a fun a' => by
    rw [pseudoZero_def, pseudoApply_mk']
    simp

/-- An extensionality lemma for being the zero arrow. -/
/-
**CategoryTheory.Abelian.Pseudoelement.zero_morphism_ext** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：zero_morphism_ext {P Q : C} (f : P ⟶ Q) : (forall a, f a = 0) -> f = 0
参数：f : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.pseudoZero_iff`：pseudoZero_iff {P :
 C} (a : Over P) : a = (0 : P) ↔ a.hom = 0

--- 原说明 ---
An extensionality lemma for being the zero arrow.
-/
theorem zero_morphism_ext {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0) → f = 0 := fun h => by
  rw [← Category.id_comp f]
  exact (pseudoZero_iff (𝟙 P ≫ f : Over Q)).1 (h (𝟙 P))
/-
**CategoryTheory.Abelian.Pseudoelement.zero_morphism_ext'** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：zero_morphism_ext' {P Q : C} (f : P ⟶ Q) : (forall a, f a = 0) -> 0 = f
参数：f : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.zero_morphism_ext`：zero_morphism_ex
t {P Q : C} (f : P ⟶ Q) : (forall a, f a = 0) -> f = 0
-/
theorem zero_morphism_ext' {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0) → 0 = f :=
  Eq.symm ∘ zero_morphism_ext f
/-
**CategoryTheory.Abelian.Pseudoelement.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Abelian.Pseudoelement`。
形式化陈述：eq_zero_iff {P Q : C} (f : P ⟶ Q) : f = 0 ↔ forall a, f a = 0
参数：f : P ⟶ Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.zero_apply`：zero_apply {P : C} (Q :
 C) (a : P) : (0 : P ⟶ Q) a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.zero_morphism_ext`：zero_morphism_ex
t {P Q : C} (f : P ⟶ Q) : (forall a, f a = 0) -> f = 0
-/
theorem eq_zero_iff {P Q : C} (f : P ⟶ Q) : f = 0 ↔ ∀ a, f a = 0 :=
  ⟨fun h a => by simp [h], zero_morphism_ext _⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A monomorphism is injective on pseudoelements. -/
/-
**CategoryTheory.Abelian.Pseudoelement.pseudo_injective_of_mono** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：pseudo_injective_of_mono {P Q : C} (f : P ⟶ Q) [Mono f] : Function.Injecti
ve f
参数：f : P ⟶ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
A monomorphism is injective on pseudoelements.
-/
theorem pseudo_injective_of_mono {P Q : C} (f : P ⟶ Q) [Mono f] : Function.Injective f := by
  intro abar abar'
  induction abar, abar' using Quotient.inductionOn₂ with | _ a a'
  refine fun ha ↦ Quotient.sound ?_
  have : (⟦(a.hom ≫ f : Over Q)⟧ : Quotient (setoid Q)) = ⟦↑(a'.hom ≫ f)⟧ := by convert!
    ha
  have ⟨R, p, q, ep, Eq, comm⟩ := Quotient.exact this
  exact ⟨R, p, q, ep, Eq, (cancel_mono f).1 <| by
    simp only [Category.assoc]
    exact comm⟩

/-- A morphism that is injective on pseudoelements only maps the zero element to zero. -/
/-
**CategoryTheory.Abelian.Pseudoelement.zero_of_map_zero** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：zero_of_map_zero {P Q : C} (f : P ⟶ Q) : Function.Injective f -> forall a,
 f a = 0 -> a = 0
参数：f : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.apply_zero`：apply_zero {P Q : C} (f
 : P ⟶ Q) : f 0 = 0

--- 原说明 ---
A morphism that is injective on pseudoelements only maps the zero element to zer
o.
-/
theorem zero_of_map_zero {P Q : C} (f : P ⟶ Q) : Function.Injective f → ∀ a, f a = 0 → a = 0 :=
  fun h a ha => by
  rw [← apply_zero f] at ha
  exact h ha

/-- A morphism that only maps the zero pseudoelement to zero is a monomorphism. -/
/-
**CategoryTheory.Abelian.Pseudoelement.mono_of_zero_of_map_zero** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：mono_of_zero_of_map_zero {P Q : C} (f : P ⟶ Q) : (forall a, f a = 0 -> a =
 0) -> Mono f
参数：f : P ⟶ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Preadditive.mono_iff_cancel_zero`：mono_iff_cancel_zero {Q
 R : C} (f : Q ⟶ R) : Mono f ↔ forall (P : C) (g : P ⟶ Q), g ≫ f = 0 -> g = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.pseudoZero_iff`：pseudoZero_iff {P :
 C} (a : Over P) : a = (0 : P) ↔ a.hom = 0

--- 原说明 ---
A morphism that only maps the zero pseudoelement to zero is a monomorphism.
-/
theorem mono_of_zero_of_map_zero {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0 → a = 0) → Mono f :=
  fun h => (mono_iff_cancel_zero _).2 fun _ g hg =>
    (pseudoZero_iff (g : Over P)).1 <|
      h _ <| show f g = 0 from (pseudoZero_iff (g ≫ f : Over Q)).2 hg

section

set_option backward.isDefEq.respectTransparency false in
/-- An epimorphism is surjective on pseudoelements. -/
/-
**CategoryTheory.Abelian.Pseudoelement.pseudo_surjective_of_epi** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：pseudo_surjective_of_epi {P Q : C} (f : P ⟶ Q) [Epi f] : Function.Surjecti
ve f
参数：f : P ⟶ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Abelian.app_hom`：app_hom {P Q : C} (f : P ⟶ Q) (a : Over 
P) : (app f a).hom = a.hom ≫ f
· 使用定理 `CategoryTheory.Over.coe_hom`：coe_hom {X Y : T} (f : Y ⟶ X) : (f : Over X
).hom = f

--- 原说明 ---
An epimorphism is surjective on pseudoelements.
-/
theorem pseudo_surjective_of_epi {P Q : C} (f : P ⟶ Q) [Epi f] : Function.Surjective f :=
  fun qbar =>
  Quotient.inductionOn qbar fun q =>
    ⟨(pullback.fst f q.hom : Over P),
      Quotient.sound <|
        ⟨pullback f q.hom, 𝟙 (pullback f q.hom), pullback.snd _ _, inferInstance, inferInstance, by
          rw [Category.id_comp, ← pullback.condition, app_hom, Over.coe_hom]⟩⟩

end

set_option backward.isDefEq.respectTransparency false in
/-- A morphism that is surjective on pseudoelements is an epimorphism. -/
/-
**CategoryTheory.Abelian.Pseudoelement.epi_of_pseudo_surjective** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：epi_of_pseudo_surjective {P Q : C} (f : P ⟶ Q) : Function.Surjective f -> 
Epi f
参数：f : P ⟶ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
A morphism that is surjective on pseudoelements is an epimorphism.
-/
theorem epi_of_pseudo_surjective {P Q : C} (f : P ⟶ Q) : Function.Surjective f → Epi f := by
  intro h
  have ⟨pbar, hpbar⟩ := h (𝟙 Q)
  have ⟨p, hp⟩ := Quotient.exists_rep pbar
  have : (⟦(p.hom ≫ f : Over Q)⟧ : Quotient (setoid Q)) = ⟦↑(𝟙 Q)⟧ := by
    rw [← hp] at hpbar
    exact hpbar
  have ⟨R, x, y, _, ey, comm⟩ := Quotient.exact this
  apply @epi_of_epi_fac _ _ _ _ _ (x ≫ p.hom) f y ey
  dsimp at comm
  rw [Category.assoc, comm]
  apply Category.comp_id

section

set_option backward.isDefEq.respectTransparency false in
/-- Two morphisms in an exact sequence are exact on pseudoelements. -/
/-
**CategoryTheory.Abelian.Pseudoelement.pseudo_exact_of_exact** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：pseudo_exact_of_exact {S : ShortComplex C} (hS : S.Exact) : forall b, S.g 
b = 0 -> exists a, S.f a = b
参数：hS : S.Exact。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.pseudoZero_iff`：pseudoZero_iff {P :
 C} (a : Over P) : a = (0 : P) ↔ a.hom = 0
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Abelian.image_ι_comp_eq_zero`：image_ι_comp_eq_zero {R : C
} {g : Q ⟶ R} (h : f ≫ g = 0) : Abelian.image.ι f ≫ g = 0
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Abelian.instEpiFactorThruImage`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {P Q : C} (f
 : P ⟶ Q),   CategoryTheory.Epi (Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.image.fac`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {P Q : C}
   (f : P ⟶ Q) [inst_2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…

--- 原说明 ---
Two morphisms in an exact sequence are exact on pseudoelements.
-/
theorem pseudo_exact_of_exact {S : ShortComplex C} (hS : S.Exact) :
    ∀ b, S.g b = 0 → ∃ a, S.f a = b :=
  fun b' =>
    Quotient.inductionOn b' fun b hb => by
      have hb' : b.hom ≫ S.g = 0 := (pseudoZero_iff _).1 hb
      -- By exactness, `b` factors through `im f = ker g` via some `c`.
      obtain ⟨c, hc⟩ := KernelFork.IsLimit.lift' hS.isLimitImage _ hb'
      -- We compute the pullback of the map into the image and `c`.
      -- The pseudoelement induced by the first pullback map will be our preimage.
      use pullback.fst (Abelian.factorThruImage S.f) c
      -- It remains to show that the image of this element under `f` is pseudo-equal to `b`.
      apply Quotient.sound
      refine ⟨pullback (Abelian.factorThruImage S.f) c, 𝟙 _,
              pullback.snd _ _, inferInstance, inferInstance, ?_⟩
      -- Now we can verify that the diagram commutes.
      calc
        𝟙 (pullback (Abelian.factorThruImage S.f) c) ≫ pullback.fst _ _ ≫ S.f =
          pullback.fst _ _ ≫ S.f :=
          Category.id_comp _
        _ = pullback.fst _ _ ≫ Abelian.factorThruImage S.f ≫ kernel.ι (cokernel.π S.f) := by
          rw [Abelian.image.fac]
        _ = (pullback.snd _ _ ≫ c) ≫ kernel.ι (cokernel.π S.f) := by
          rw [← Category.assoc, pullback.condition]
        _ = pullback.snd _ _ ≫ b.hom := by
          rw [Category.assoc]
          congr

end

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.Pseudoelement.apply_eq_zero_of_comp_eq_zero** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：apply_eq_zero_of_comp_eq_zero {P Q R : C} (f : Q ⟶ R) (a : P ⟶ Q) : a ≫ f 
= 0 -> f a = 0
参数：f : Q ⟶ R；a : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.zero_eq_zero`：zero_eq_zero {P Q : C
} : ⟦((0 : Q ⟶ P) : Over P)⟧ = (0 : Pseudoelement P)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem apply_eq_zero_of_comp_eq_zero {P Q R : C} (f : Q ⟶ R) (a : P ⟶ Q) : a ≫ f = 0 → f a = 0 :=
  fun h => by simp [over_coe_def, pseudoApply_mk', h]

section

set_option backward.isDefEq.respectTransparency false in
/-- If two morphisms are exact on pseudoelements, they are exact. -/
/-
**CategoryTheory.Abelian.Pseudoelement.exact_of_pseudo_exact** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：exact_of_pseudo_exact (S : ShortComplex C) (hS : forall b, S.g b = 0 -> ex
ists a, S.f a = b) : S.Exact
参数：S : ShortComplex C；hS : forall b, S.g b = 0 -> exists a, S.f a = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero`：exa
ct_iff_kernel_ι_comp_cokernel_π_zero [S.HasHomology] [HasKernel S.g] [HasCokerne
l S.f] : S.Exact ↔ kernel.ι S.g ≫ cokernel.π S.f = 0
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.apply_eq_zero_of_comp_eq_zero`：appl
y_eq_zero_of_comp_eq_zero {P Q R : C} (f : Q ⟶ R) (a : P ⟶ Q) : a ≫ f = 0 -> f a
 = 0
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Abelian.image.fac`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {P Q : C}
   (f : P ⟶ Q) [inst_2…
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.Limits.pullback.snd_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If two morphisms are exact on pseudoelements, they are exact.
-/
theorem exact_of_pseudo_exact (S : ShortComplex C)
    (hS : ∀ b, S.g b = 0 → ∃ a, S.f a = b) : S.Exact :=
  (S.exact_iff_kernel_ι_comp_cokernel_π_zero).2 (by
      -- If we apply `g` to the pseudoelement induced by its kernel, we get 0 (of course!).
      have : S.g (kernel.ι S.g) = 0 := apply_eq_zero_of_comp_eq_zero _ _ (kernel.condition _)
      -- By pseudo-exactness, we get a preimage.
      obtain ⟨a', ha⟩ := hS _ this
      obtain ⟨a, ha'⟩ := Quotient.exists_rep a'
      rw [← ha'] at ha
      obtain ⟨Z, r, q, _, eq, comm⟩ := Quotient.exact ha
      -- Consider the pullback of `kernel.ι (cokernel.π f)` and `kernel.ι g`.
      -- The commutative diagram given by the pseudo-equality `f a = b` induces
      -- a cone over this pullback, so we get a factorization `z`.
      obtain ⟨z, _, hz₂⟩ := @pullback.lift' _ _ _ _ _ _ (kernel.ι (cokernel.π S.f))
        (kernel.ι S.g) _ (r ≫ a.hom ≫ Abelian.factorThruImage S.f) q (by
          simp only [Category.assoc, Abelian.image.fac]
          exact comm)
      -- Let's give a name to the second pullback morphism.
      let j : pullback (kernel.ι (cokernel.π S.f)) (kernel.ι S.g) ⟶ kernel S.g := pullback.snd _ _
      -- Since `q` is an epimorphism, in particular this means that `j` is an epimorphism.
      have pe : Epi j := epi_of_epi_fac hz₂
      -- But it is also a monomorphism, because `kernel.ι (cokernel.π f)` is: A kernel is
      -- always a monomorphism and the pullback of a monomorphism is a monomorphism.
      -- But mono + epi = iso, so `j` is an isomorphism.
      have : IsIso j := isIso_of_mono_of_epi _
      -- But then `kernel.ι g` can be expressed using all of the maps of the pullback square, and we
      -- are done.
      rw [(Iso.eq_inv_comp (asIso j)).2 pullback.condition.symm]
      simp only [Category.assoc, kernel.condition, HasZeroMorphisms.comp_zero])

end

set_option backward.isDefEq.respectTransparency false in
/-- If two pseudoelements `x` and `y` have the same image under some morphism `f`, then we can form
their "difference" `z`. This pseudoelement has the properties that `f z = 0` and for all
morphisms `g`, if `g y = 0` then `g z = g x`. -/
/-
**CategoryTheory.Abelian.Pseudoelement.sub_of_eq_image** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：sub_of_eq_image {P Q : C} (f : P ⟶ Q) (x y : P) : f x = f y -> exists z, f
 z = 0 ∧ forall (R : C) (g : P ⟶ R), (g : P ⟶ R) y = 0 -> g z = g x
参数：f : P ⟶ Q；x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `CategoryTheory.Abelian.Pseudoelement.zero_eq_zero`：zero_eq_zero {P Q : C
} : ⟦((0 : Q ⟶ P) : Over P)⟧ = (0 : Pseudoelement P)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Preadditive.epi_iff_cancel_zero`：epi_iff_cancel_zero {P Q
 : C} (f : P ⟶ Q) : Epi f ↔ forall (R : C) (g : Q ⟶ R), f ≫ g = 0 -> g = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
If two pseudoelements `x` and `y` have the same image under some morphism `f`, t
hen we can form
their "difference" `z`. This pseudoelement has the properties that `f z = 0` and
 for all
morphisms `g`, if `g y = 0` then `g z = g x`.
-/
theorem sub_of_eq_image {P Q : C} (f : P ⟶ Q) (x y : P) :
    f x = f y → ∃ z, f z = 0 ∧ ∀ (R : C) (g : P ⟶ R), (g : P ⟶ R) y = 0 → g z = g x :=
  Quotient.inductionOn₂ x y fun a a' h =>
    match Quotient.exact h with
    | ⟨R, p, q, ep, _, comm⟩ =>
      let a'' : R ⟶ P := (p ≫ a.hom : R ⟶ P) - (q ≫ a'.hom : R ⟶ P)
      ⟨a'',
        ⟨show ⟦(a'' ≫ f : Over Q)⟧ = ⟦↑(0 : Q ⟶ Q)⟧ by
            dsimp at comm
            simp [a'', sub_eq_zero.2 comm],
          fun Z g hh => by
          obtain ⟨X, p', q', ep', _, comm'⟩ := Quotient.exact hh
          have : a'.hom ≫ g = 0 := by
            apply (epi_iff_cancel_zero _).1 ep' _ (a'.hom ≫ g)
            simpa using comm'
          apply Quotient.sound
          -- Can we prevent quotient.sound from giving us this weird `coe_b` thingy?
          change app g (a'' : Over P) ≈ app g a
          exact ⟨R, 𝟙 R, p, inferInstance, ep, by simp [a'', sub_eq_add_neg, this]⟩⟩⟩

variable [Limits.HasPullbacks C]

set_option backward.isDefEq.respectTransparency false in
/-- If `f : P ⟶ R` and `g : Q ⟶ R` are morphisms and `p : P` and `q : Q` are pseudoelements such
that `f p = g q`, then there is some `s : pullback f g` such that `fst s = p` and `snd s = q`.

Remark: Borceux claims that `s` is unique, but this is false. See
`Counterexamples/Pseudoelement.lean` for details. -/
/-
**CategoryTheory.Abelian.Pseudoelement.pseudo_pullback** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Abelian.Pseudoelement`。
形式化陈述：pseudo_pullback {P Q R : C} {f : P ⟶ R} {g : Q ⟶ R} {p : P} {q : Q} : f p 
= g q -> exists s, pullback.fst f g s = p ∧ pullback.snd f g s = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
If `f : P ⟶ R` and `g : Q ⟶ R` are morphisms and `p : P` and `q : Q` are pseudoe
lements such
that `f p = g q`, then there is some `s : pullback f g` such that `fst s = p` an
d `snd s = q`.

Remark: Borceux claims that `s` is unique, but this is false. See
`Counterexamples/Pseudoelement.lean` for details.
-/
theorem pseudo_pullback {P Q R : C} {f : P ⟶ R} {g : Q ⟶ R} {p : P} {q : Q} :
    f p = g q →
      ∃ s, pullback.fst f g s = p ∧ pullback.snd f g s = q :=
  Quotient.inductionOn₂ p q fun x y h => by
    obtain ⟨Z, a, b, ea, eb, comm⟩ := Quotient.exact h
    obtain ⟨l, hl₁, hl₂⟩ := @pullback.lift' _ _ _ _ _ _ f g _ (a ≫ x.hom) (b ≫ y.hom) (by
      simp only [Category.assoc]
      exact comm)
    exact ⟨l, ⟨Quotient.sound ⟨Z, 𝟙 Z, a, inferInstance, ea, by rwa [Category.id_comp]⟩,
      Quotient.sound ⟨Z, 𝟙 Z, b, inferInstance, eb, by rwa [Category.id_comp]⟩⟩⟩

section Module

/-- In the category `ModuleCat R`, if `x` and `y` are pseudoequal, then the range of the associated
morphisms is the same. -/
/-
**CategoryTheory.Abelian.Pseudoelement.ModuleCat.eq_range_of_pseudoequal** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Abelian.Pseudoelement.ModuleCat`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {G : ModuleCat R} {x y : CategoryTheory.O
ver G},   CategoryTheory.Abelian.PseudoEqual G x y → (ModuleCat.Hom.hom x.hom).r
ange = (ModuleCat.Hom.hom y.hom).range
参数：ModuleCat.Hom.hom x.hom；ModuleCat.Hom.hom y.hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用引理 `ModuleCat.hom_comp`：hom_comp {M N O : ModuleCat.{v} R} (f : M ⟶ N) (g : 
N ⟶ O) : (f ≫ g).hom = g.hom.comp f.hom

--- 原说明 ---
In the category `ModuleCat R`, if `x` and `y` are pseudoequal, then the range of
 the associated
morphisms is the same.
-/
theorem ModuleCat.eq_range_of_pseudoequal {R : Type*} [Ring R] {G : ModuleCat R} {x y : Over G}
    (h : PseudoEqual G x y) : LinearMap.range x.hom.hom = LinearMap.range y.hom.hom := by
  obtain ⟨P, p, q, hp, hq, H⟩ := h
  refine Submodule.ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨a', ha'⟩ := ha
    obtain ⟨a'', ha''⟩ := (ModuleCat.epi_iff_surjective p).1 hp a'
    refine ⟨q a'', ?_⟩
    dsimp at ha' ⊢
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← H,
      ModuleCat.hom_comp, LinearMap.comp_apply, ha'', ha']
  · obtain ⟨a', ha'⟩ := ha
    obtain ⟨a'', ha''⟩ := (ModuleCat.epi_iff_surjective q).1 hq a'
    refine ⟨p a'', ?_⟩
    dsimp at ha' ⊢
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, H, ModuleCat.hom_comp, LinearMap.comp_apply,
      ha'', ha']

end Module

end Pseudoelement

end CategoryTheory.Abelian

