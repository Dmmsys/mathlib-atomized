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

/--
Definition of `app` / `app` 的定义

English:
definition app
  signature: {P Q : C} (f : P ⟶ Q) (a : Over P)
  body: a.hom ≫ f

@[simp]

中文:
定义 app
  签名: {P Q : C} (f : P ⟶ Q) (a : Over P)
  定义体: a.hom ≫ f

@[simp]

Depends on / 依赖: a.hom
-/
def app {P Q : C} (f : P ⟶ Q) (a : Over P) : Over Q :=
  a.hom ≫ f

@[simp]
/--
theorem `app_hom` / 定理 `app_hom`

English:
theorem app_hom
  given: {P Q : C} (f : P ⟶ Q) (a : Over P)
  statement: (app f a).hom = a.hom ≫ f
  proof: rfl

中文:
定理 app_hom
  条件: {P Q : C} (f : P ⟶ Q) (a : Over P)
  结论: (app f a).hom = a.hom ≫ f
  证明: rfl
-/
theorem app_hom {P Q : C} (f : P ⟶ Q) (a : Over P) : (app f a).hom = a.hom ≫ f := rfl

/--
Definition of `PseudoEqual` / `PseudoEqual` 的定义

English:
definition PseudoEqual
  signature: (P : C) (f g : Over P)
  body: exists (R : C) (p : R ⟶ f.1) (q : R ⟶ g.1) (_ : Epi p) (_ : Epi q), p ≫ f.hom = q ≫ g.hom

中文:
定义 PseudoEqual
  签名: (P : C) (f g : Over P)
  定义体: exists (R : C) (p : R ⟶ f.1) (q : R ⟶ g.1) (_ : Epi p) (_ : Epi q), p ≫ f.hom = q ≫ g.hom

Depends on / 依赖: f.hom, g.hom
-/
def PseudoEqual (P : C) (f g : Over P) : Prop :=
  exists (R : C) (p : R ⟶ f.1) (q : R ⟶ g.1) (_ : Epi p) (_ : Epi q), p ≫ f.hom = q ≫ g.hom

/--
Instance `pseudoEqual_refl` / 实例 `pseudoEqual_refl`

English:
instance pseudoEqual_refl
  signature: {P : C}
  body: ⟨f.1, 𝟙 f.1, 𝟙 f.1, inferInstance, inferInstance, by simp⟩

中文:
实例 pseudoEqual_refl
  签名: {P : C}
  定义体: ⟨f.1, 𝟙 f.1, 𝟙 f.1, inferInstance, inferInstance, by simp⟩
-/
instance pseudoEqual_refl {P : C} : Std.Refl (PseudoEqual P) where
  refl f := ⟨f.1, 𝟙 f.1, 𝟙 f.1, inferInstance, inferInstance, by simp⟩

/--
Instance `pseudoEqual_symm` / 实例 `pseudoEqual_symm`

English:
instance pseudoEqual_symm
  signature: {P : C}
  body: fun ⟨R, p, q, ep, Eq, comm⟩ => ⟨R, q, p, Eq, ep, comm.symm⟩

中文:
实例 pseudoEqual_symm
  签名: {P : C}
  定义体: fun ⟨R, p, q, ep, Eq, comm⟩ => ⟨R, q, p, Eq, ep, comm.symm⟩

Depends on / 依赖: comm.symm
-/
instance pseudoEqual_symm {P : C} : Std.Symm (PseudoEqual P) where
  symm _ _ := fun ⟨R, p, q, ep, Eq, comm⟩ => ⟨R, q, p, Eq, ep, comm.symm⟩

variable [Abelian.{v} C]

section

/--
Instance `pseudoEqual_trans` / 实例 `pseudoEqual_trans`

English:
instance pseudoEqual_trans
  signature: {P : C}
  body: by
  refine ⟨fun f g h ⟨R, p, q, ep, Eq, comm⟩ ⟨R', p', q', ep', eq', comm'⟩ => ?_⟩
  refine ⟨pullback q p', pullback.fst _ _ ≫ p, pullback.snd _ _ ≫ q',
    epi_comp _ _, epi_comp _ _, ?_⟩
  rw [Category.assoc]; rw [comm]; rw [← Category.assoc]; rw [pullback.condition]; rw [Category.assoc]; rw [com

中文:
实例 pseudoEqual_trans
  签名: {P : C}
  定义体: by
  refine ⟨fun f g h ⟨R, p, q, ep, Eq, comm⟩ ⟨R', p', q', ep', eq', comm'⟩ => ?_⟩
  refine ⟨pullback q p', pullback.fst _ _ ≫ p, pullback.snd _ _ ≫ q',
    epi_comp _ _, epi_comp _ _, ?_⟩
  rw [Category.assoc]; rw [comm]; rw [← Category.assoc]; rw [pullback.condition]; rw [Category.assoc]; rw [com

Depends on / 依赖: Category, Category.assoc, condition, epi_comp, pullback, pullback.condition, pullback.fst, pullback.snd
-/
instance pseudoEqual_trans {P : C} : IsTrans (Over P) (PseudoEqual P) := by
  refine ⟨fun f g h ⟨R, p, q, ep, Eq, comm⟩ ⟨R', p', q', ep', eq', comm'⟩ => ?_⟩
  refine ⟨pullback q p', pullback.fst _ _ ≫ p, pullback.snd _ _ ≫ q',
    epi_comp _ _, epi_comp _ _, ?_⟩
  rw [Category.assoc]; rw [comm]; rw [← Category.assoc]; rw [pullback.condition]; rw [Category.assoc]; rw [comm']; rw [Category.assoc]

end

/-- The arrows with codomain `P` equipped with the equivalence relation of being pseudo-equal. -/
@[instance_reducible]
/--
Definition of `Pseudoelement.setoid` / `Pseudoelement.setoid` 的定义

English:
definition Pseudoelement.setoid
  signature: (P : C)
  body: ⟨_, ⟨pseudoEqual_refl.refl, pseudoEqual_symm.symm _ _, pseudoEqual_trans.trans _ _ _⟩⟩

中文:
定义 Pseudoelement.setoid
  签名: (P : C)
  定义体: ⟨_, ⟨pseudoEqual_refl.refl, pseudoEqual_symm.symm _ _, pseudoEqual_trans.trans _ _ _⟩⟩

Depends on / 依赖: pseudoEqual_refl, pseudoEqual_refl.refl, pseudoEqual_symm, pseudoEqual_symm.symm, pseudoEqual_trans, pseudoEqual_trans.trans
-/
def Pseudoelement.setoid (P : C) : Setoid (Over P) :=
  ⟨_, ⟨pseudoEqual_refl.refl, pseudoEqual_symm.symm _ _, pseudoEqual_trans.trans _ _ _⟩⟩

attribute [local instance] Pseudoelement.setoid

/--
Definition of `Pseudoelement` / `Pseudoelement` 的定义

English:
definition Pseudoelement
  signature: (P : C)
  body: Quotient (Pseudoelement.setoid P)

中文:
定义 Pseudoelement
  签名: (P : C)
  定义体: Quotient (Pseudoelement.setoid P)

Depends on / 依赖: Pseudoelement, Pseudoelement.setoid, Quotient, setoid
-/
def Pseudoelement (P : C) : Type max u v :=
  Quotient (Pseudoelement.setoid P)

namespace Pseudoelement

/-- A coercion from an object of an abelian category to its pseudoelements. -/
@[instance_reducible]
/--
Definition of `objectToSort` / `objectToSort` 的定义

English:
definition objectToSort
  signature: : CoeSort C (Type max u v)
  body: ⟨fun P => Pseudoelement P⟩

中文:
定义 objectToSort
  签名: : CoeSort C (类型 最大值 u v)
  定义体: ⟨fun P => Pseudoelement P⟩

Depends on / 依赖: Pseudoelement
-/
def objectToSort : CoeSort C (Type max u v) :=
  ⟨fun P => Pseudoelement P⟩

attribute [local instance] objectToSort

scoped[Pseudoelement] attribute [instance] CategoryTheory.Abelian.Pseudoelement.objectToSort

/-- A coercion from an arrow with codomain `P` to its associated pseudoelement. -/
@[instance_reducible]
/--
Definition of `overToSort` / `overToSort` 的定义

English:
definition overToSort
  signature: {P : C}
  body: ⟨Quot.mk (PseudoEqual P)⟩

中文:
定义 overToSort
  签名: {P : C}
  定义体: ⟨Quot.mk (PseudoEqual P)⟩

Depends on / 依赖: PseudoEqual, Quot.mk
-/
def overToSort {P : C} : Coe (Over P) (Pseudoelement P) :=
  ⟨Quot.mk (PseudoEqual P)⟩

attribute [local instance] overToSort

/--
theorem `over_coe_def` / 定理 `over_coe_def`

English:
theorem over_coe_def
  given: {P Q : C} (a : Q ⟶ P)
  statement: (a : Pseudoelement P) = ⟦↑a⟧
  proof: rfl

中文:
定理 over_coe_def
  条件: {P Q : C} (a : Q ⟶ P)
  结论: (a : Pseudoelement P) = ⟦↑a⟧
  证明: rfl
-/
theorem over_coe_def {P Q : C} (a : Q ⟶ P) : (a : Pseudoelement P) = ⟦↑a⟧ := rfl

/--
theorem `pseudoApply_aux` / 定理 `pseudoApply_aux`

English:
theorem pseudoApply_aux
  given: {P Q : C} (f : P ⟶ Q) (a b : Over P)
  statement: a ≈ b -> app f a ≈ app f b
  proof: fun ⟨R, p, q, ep, Eq, comm⟩ =>
  ⟨R, p, q, ep, Eq, show p ≫ a.hom ≫ f = q ≫ b.hom ≫ f by rw [reassoc_of% comm]⟩

中文:
定理 pseudoApply_aux
  条件: {P Q : C} (f : P ⟶ Q) (a b : Over P)
  结论: a ≈ b -> app f a ≈ app f b
  证明: fun ⟨R, p, q, ep, Eq, comm⟩ =>
  ⟨R, p, q, ep, Eq, show p ≫ a.hom ≫ f = q ≫ b.hom ≫ f by rw [reassoc_of% comm]⟩

Depends on / 依赖: a.hom, b.hom, reassoc_of
-/
theorem pseudoApply_aux {P Q : C} (f : P ⟶ Q) (a b : Over P) : a ≈ b -> app f a ≈ app f b :=
  fun ⟨R, p, q, ep, Eq, comm⟩ =>
  ⟨R, p, q, ep, Eq, show p ≫ a.hom ≫ f = q ≫ b.hom ≫ f by rw [reassoc_of% comm]⟩

/--
Definition of `pseudoApply` / `pseudoApply` 的定义

English:
definition pseudoApply
  signature: {P Q : C} (f : P ⟶ Q)
  body: Quotient.map (fun g : Over P => app f g) (pseudoApply_aux f)

中文:
定义 pseudoApply
  签名: {P Q : C} (f : P ⟶ Q)
  定义体: Quotient.map (fun g : Over P => app f g) (pseudoApply_aux f)

Depends on / 依赖: Quotient, Quotient.map, pseudoApply_aux
-/
def pseudoApply {P Q : C} (f : P ⟶ Q) : P -> Q :=
  Quotient.map (fun g : Over P => app f g) (pseudoApply_aux f)

/-- A coercion from morphisms to functions on pseudoelements. -/
@[instance_reducible]
/--
Definition of `homToFun` / `homToFun` 的定义

English:
definition homToFun
  signature: {P Q : C}
  body: ⟨pseudoApply⟩

中文:
定义 homToFun
  签名: {P Q : C}
  定义体: ⟨pseudoApply⟩

Depends on / 依赖: pseudoApply
-/
def homToFun {P Q : C} : CoeFun (P ⟶ Q) fun _ => P -> Q :=
  ⟨pseudoApply⟩

attribute [local instance] homToFun

scoped[Pseudoelement] attribute [instance] CategoryTheory.Abelian.Pseudoelement.homToFun

/--
theorem `pseudoApply_mk'` / 定理 `pseudoApply_mk'`

English:
theorem pseudoApply_mk'
  given: {P Q : C} (f : P ⟶ Q) (a : Over P)
  statement: f ⟦a⟧ = ⟦↑(a.hom ≫ f)⟧
  proof: rfl

中文:
定理 pseudoApply_mk'
  条件: {P Q : C} (f : P ⟶ Q) (a : Over P)
  结论: f ⟦a⟧ = ⟦↑(a.hom ≫ f)⟧
  证明: rfl
-/
theorem pseudoApply_mk' {P Q : C} (f : P ⟶ Q) (a : Over P) : f ⟦a⟧ = ⟦↑(a.hom ≫ f)⟧ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (a : P)
  statement: (f ≫ g) a = g (f a)
  proof: Quotient.inductionOn a fun x =>
Quotient.sound by
      simp only [app]
      rw [← Category.assoc]; rw [Over.coe_hom]

中文:
定理 comp_apply
  条件: {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (a : P)
  结论: (f ≫ g) a = g (f a)
  证明: Quotient.inductionOn a fun x =>
Quotient.sound by
      simp only [app]
      rw [← Category.assoc]; rw [Over.coe_hom]

Depends on / 依赖: Category, Category.assoc, Over.coe_hom, Quotient, Quotient.inductionOn, Quotient.sound, coe_hom, inductionOn
-/
theorem comp_apply {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (a : P) : (f ≫ g) a = g (f a) :=
  Quotient.inductionOn a fun x =>
Quotient.sound by
      simp only [app]
      rw [← Category.assoc]; rw [Over.coe_hom]

/--
theorem `comp_comp` / 定理 `comp_comp`

English:
theorem comp_comp
  given: {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R)
  statement: g ∘ f = f ≫ g
  proof: funext fun _ => (comp_apply _ _ _).symm

中文:
定理 comp_comp
  条件: {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R)
  结论: g ∘ f = f ≫ g
  证明: funext fun _ => (comp_apply _ _ _).symm

Depends on / 依赖: comp_apply
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
/--
theorem `pseudoZero_aux` / 定理 `pseudoZero_aux`

English:
theorem pseudoZero_aux
  given: {P : C} (Q : C) (f : Over P)
  statement: f ≈ (0 : Q ⟶ P) ↔ f.hom = 0
  proof: ⟨fun ⟨R, p, q, _, _, comm⟩ => zero_of_epi_comp p (by simp [comm]), fun hf =>
    ⟨biprod f.1 Q, biprod.fst, biprod.snd, inferInstance, inferInstance, by
      rw [hf]; rw [Over.coe_hom]; rw [HasZeroMorphisms.comp_zero]; rw [HasZeroMorphisms.comp_zero]⟩⟩

中文:
定理 pseudoZero_aux
  条件: {P : C} (Q : C) (f : Over P)
  结论: f ≈ (0 : Q ⟶ P) ↔ f.hom = 0
  证明: ⟨fun ⟨R, p, q, _, _, comm⟩ => zero_of_epi_comp p (by simp [comm]), fun hf =>
    ⟨biprod f.1 Q, biprod.fst, biprod.snd, inferInstance, inferInstance, by
      rw [hf]; rw [Over.coe_hom]; rw [HasZeroMorphisms.comp_zero]; rw [HasZeroMorphisms.comp_zero]⟩⟩

Depends on / 依赖: HasZeroMorphisms, HasZeroMorphisms.comp_zero, Over.coe_hom, biprod, biprod.fst, biprod.snd, coe_hom, comp_zero, zero_of_epi_comp
-/
theorem pseudoZero_aux {P : C} (Q : C) (f : Over P) : f ≈ (0 : Q ⟶ P) ↔ f.hom = 0 :=
  ⟨fun ⟨R, p, q, _, _, comm⟩ => zero_of_epi_comp p (by simp [comm]), fun hf =>
    ⟨biprod f.1 Q, biprod.fst, biprod.snd, inferInstance, inferInstance, by
      rw [hf]; rw [Over.coe_hom]; rw [HasZeroMorphisms.comp_zero]; rw [HasZeroMorphisms.comp_zero]⟩⟩

end

/--
theorem `zero_eq_zero'` / 定理 `zero_eq_zero'`

English:
theorem zero_eq_zero'
  given: {P Q R : C}
  proof: Quotient.sound (pseudoZero_aux R _).2 rfl

中文:
定理 zero_eq_zero'
  条件: {P Q R : C}
  证明: Quotient.sound (pseudoZero_aux R _).2 rfl

Depends on / 依赖: Quotient, Quotient.sound, pseudoZero_aux
-/
theorem zero_eq_zero' {P Q R : C} :
    (⟦((0 : Q ⟶ P) : Over P)⟧ : Pseudoelement P) = ⟦((0 : R ⟶ P) : Over P)⟧ :=
Quotient.sound (pseudoZero_aux R _).2 rfl

/--
Definition of `pseudoZero` / `pseudoZero` 的定义

English:
definition pseudoZero
  signature: {P : C}
  body: ⟦(0 : P ⟶ P)⟧

中文:
定义 pseudoZero
  签名: {P : C}
  定义体: ⟦(0 : P ⟶ P)⟧
-/
def pseudoZero {P : C} : P :=
  ⟦(0 : P ⟶ P)⟧

/--
Instance `hasZero` / 实例 `hasZero`

English:
instance hasZero
  signature: {P : C}
  body: ⟨pseudoZero⟩

中文:
实例 hasZero
  签名: {P : C}
  定义体: ⟨pseudoZero⟩

Depends on / 依赖: pseudoZero
-/
instance hasZero {P : C} : Zero P :=
  ⟨pseudoZero⟩

instance {P : C} : Inhabited P :=
  ⟨0⟩

/--
theorem `pseudoZero_def` / 定理 `pseudoZero_def`

English:
theorem pseudoZero_def
  given: {P : C}
  statement: (0 : Pseudoelement P) = ⟦↑(0 : P ⟶ P)⟧
  proof: rfl

@[simp]

中文:
定理 pseudoZero_def
  条件: {P : C}
  结论: (0 : Pseudoelement P) = ⟦↑(0 : P ⟶ P)⟧
  证明: rfl

@[simp]
-/
theorem pseudoZero_def {P : C} : (0 : Pseudoelement P) = ⟦↑(0 : P ⟶ P)⟧ := rfl

@[simp]
/--
theorem `zero_eq_zero` / 定理 `zero_eq_zero`

English:
theorem zero_eq_zero
  given: {P Q : C}
  statement: ⟦((0 : Q ⟶ P) : Over P)⟧ = (0 : Pseudoelement P)
  proof: zero_eq_zero'

中文:
定理 zero_eq_zero
  条件: {P Q : C}
  结论: ⟦((0 : Q ⟶ P) : Over P)⟧ = (0 : Pseudoelement P)
  证明: zero_eq_zero'

Depends on / 依赖: zero_eq_zero
-/
theorem zero_eq_zero {P Q : C} : ⟦((0 : Q ⟶ P) : Over P)⟧ = (0 : Pseudoelement P) :=
  zero_eq_zero'

/--
theorem `pseudoZero_iff` / 定理 `pseudoZero_iff`

English:
theorem pseudoZero_iff
  given: {P : C} (a : Over P)
  statement: a = (0 : P) ↔ a.hom = 0
  proof: by
  rw [← pseudoZero_aux P a]
  exact Quotient.eq'

中文:
定理 pseudoZero_iff
  条件: {P : C} (a : Over P)
  结论: a = (0 : P) ↔ a.hom = 0
  证明: by
  rw [← pseudoZero_aux P a]
  exact Quotient.eq'

Depends on / 依赖: Quotient, Quotient.eq, pseudoZero_aux
-/
theorem pseudoZero_iff {P : C} (a : Over P) : a = (0 : P) ↔ a.hom = 0 := by
  rw [← pseudoZero_aux P a]
  exact Quotient.eq'

end Zero


set_option backward.defeqAttrib.useBackward true in
/-- Morphisms map the zero pseudoelement to the zero pseudoelement. -/
@[simp]
/--
theorem `apply_zero` / 定理 `apply_zero`

English:
theorem apply_zero
  given: {P Q : C} (f : P ⟶ Q)
  statement: f 0 = 0
  proof: by
  rw [pseudoZero_def]; rw [pseudoApply_mk']
  simp

中文:
定理 apply_zero
  条件: {P Q : C} (f : P ⟶ Q)
  结论: f 0 = 0
  证明: by
  rw [pseudoZero_def]; rw [pseudoApply_mk']
  simp

Depends on / 依赖: pseudoApply_mk, pseudoZero_def
-/
theorem apply_zero {P Q : C} (f : P ⟶ Q) : f 0 = 0 := by
  rw [pseudoZero_def]; rw [pseudoApply_mk']
  simp

/-- The zero morphism maps every pseudoelement to 0. -/
@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: {P : C} (Q : C) (a : P)
  statement: (0 : P ⟶ Q) a = 0
  proof: Quotient.inductionOn a fun a' => by
    rw [pseudoZero_def]; rw [pseudoApply_mk']
    simp

中文:
定理 zero_apply
  条件: {P : C} (Q : C) (a : P)
  结论: (0 : P ⟶ Q) a = 0
  证明: Quotient.inductionOn a fun a' => by
    rw [pseudoZero_def]; rw [pseudoApply_mk']
    simp

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, pseudoApply_mk, pseudoZero_def
-/
theorem zero_apply {P : C} (Q : C) (a : P) : (0 : P ⟶ Q) a = 0 :=
  Quotient.inductionOn a fun a' => by
    rw [pseudoZero_def]; rw [pseudoApply_mk']
    simp

/--
theorem `zero_morphism_ext` / 定理 `zero_morphism_ext`

English:
theorem zero_morphism_ext
  given: {P Q : C} (f : P ⟶ Q)
  statement: (forall a, f a = 0) -> f = 0
  proof: fun h => by
  rw [← Category.id_comp f]
  exact (pseudoZero_iff (𝟙 P ≫ f : Over Q)).1 (h (𝟙 P))

中文:
定理 zero_morphism_ext
  条件: {P Q : C} (f : P ⟶ Q)
  结论: (对任意 a, f a = 0) -> f = 0
  证明: fun h => by
  rw [← Category.id_comp f]
  exact (pseudoZero_iff (𝟙 P ≫ f : Over Q)).1 (h (𝟙 P))

Depends on / 依赖: Category, Category.id_comp, id_comp, pseudoZero_iff
-/
theorem zero_morphism_ext {P Q : C} (f : P ⟶ Q) : (forall a, f a = 0) -> f = 0 := fun h => by
  rw [← Category.id_comp f]
  exact (pseudoZero_iff (𝟙 P ≫ f : Over Q)).1 (h (𝟙 P))

/--
theorem `zero_morphism_ext'` / 定理 `zero_morphism_ext'`

English:
theorem zero_morphism_ext'
  given: {P Q : C} (f : P ⟶ Q)
  statement: (forall a, f a = 0) -> 0 = f
  proof: Eq.symm ∘ zero_morphism_ext f

中文:
定理 zero_morphism_ext'
  条件: {P Q : C} (f : P ⟶ Q)
  结论: (对任意 a, f a = 0) -> 0 = f
  证明: Eq.symm ∘ zero_morphism_ext f

Depends on / 依赖: Eq.symm, zero_morphism_ext
-/
theorem zero_morphism_ext' {P Q : C} (f : P ⟶ Q) : (forall a, f a = 0) -> 0 = f :=
  Eq.symm ∘ zero_morphism_ext f

/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  given: {P Q : C} (f : P ⟶ Q)
  statement: f = 0 ↔ forall a, f a = 0
  proof: ⟨fun h a => by simp [h], zero_morphism_ext _⟩

中文:
定理 eq_zero_iff
  条件: {P Q : C} (f : P ⟶ Q)
  结论: f = 0 ↔ 对任意 a, f a = 0
  证明: ⟨fun h a => by simp [h], zero_morphism_ext _⟩

Depends on / 依赖: zero_morphism_ext
-/
theorem eq_zero_iff {P Q : C} (f : P ⟶ Q) : f = 0 ↔ forall a, f a = 0 :=
  ⟨fun h a => by simp [h], zero_morphism_ext _⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `pseudo_injective_of_mono` / 定理 `pseudo_injective_of_mono`

English:
theorem pseudo_injective_of_mono
  given: {P Q : C} (f : P ⟶ Q) [Mono f]
  statement: Function.Injective f
  proof: by
  intro abar abar'
  induction abar, abar' using Quotient.inductionOn₂ with | _ a a'
  refine fun ha => Quotient.sound ?_
  have : (⟦(a.hom ≫ f : Over Q)⟧ : Quotient (setoid Q)) = ⟦↑(a'.hom ≫ f)⟧ := by convert!
    ha
  have ⟨R, p, q, ep, Eq, comm⟩ := Quotient.exact this
exact ⟨R, p, q, ep, Eq, (

中文:
定理 pseudo_injective_of_mono
  条件: {P Q : C} (f : P ⟶ Q) [单态射 f]
  结论: 函数.单射 f
  证明: by
  intro abar abar'
  induction abar, abar' using Quotient.inductionOn₂ with | _ a a'
  refine fun ha => Quotient.sound ?_
  have : (⟦(a.hom ≫ f : Over Q)⟧ : Quotient (setoid Q)) = ⟦↑(a'.hom ≫ f)⟧ := by convert!
    ha
  have ⟨R, p, q, ep, Eq, comm⟩ := Quotient.exact this
exact ⟨R, p, q, ep, Eq, (

Depends on / 依赖: Category, Category.assoc, IsColimit, Quotient, Quotient.exact, Quotient.inductionOn, Quotient.sound, Subsingleton, a.hom, cancel_mono, convert, setoid
-/
theorem pseudo_injective_of_mono {P Q : C} (f : P ⟶ Q) [Mono f] : Function.Injective f := by
  intro abar abar'
  induction abar, abar' using Quotient.inductionOn₂ with | _ a a'
  refine fun ha => Quotient.sound ?_
  have : (⟦(a.hom ≫ f : Over Q)⟧ : Quotient (setoid Q)) = ⟦↑(a'.hom ≫ f)⟧ := by convert!
    ha
  have ⟨R, p, q, ep, Eq, comm⟩ := Quotient.exact this
exact ⟨R, p, q, ep, Eq, (cancel_mono f).1 by
    simp only [Category.assoc]
    exact comm⟩

/--
theorem `zero_of_map_zero` / 定理 `zero_of_map_zero`

English:
theorem zero_of_map_zero
  given: {P Q : C} (f : P ⟶ Q)
  statement: Function.Injective f -> forall a, f a = 0 -> a = 0
  proof: fun h a ha => by
  rw [← apply_zero f] at ha
  exact h ha

中文:
定理 zero_of_map_zero
  条件: {P Q : C} (f : P ⟶ Q)
  结论: 函数.单射 f -> 对任意 a, f a = 0 -> a = 0
  证明: fun h a ha => by
  rw [← apply_zero f] at ha
  exact h ha

Depends on / 依赖: apply_zero
-/
theorem zero_of_map_zero {P Q : C} (f : P ⟶ Q) : Function.Injective f -> forall a, f a = 0 -> a = 0 :=
  fun h a ha => by
  rw [← apply_zero f] at ha
  exact h ha

/--
theorem `mono_of_zero_of_map_zero` / 定理 `mono_of_zero_of_map_zero`

English:
theorem mono_of_zero_of_map_zero
  given: {P Q : C} (f : P ⟶ Q)
  statement: (forall a, f a = 0 -> a = 0) -> Mono f
  proof: fun h => (mono_iff_cancel_zero _).2 fun _ g hg =>
(pseudoZero_iff (g : Over P)).1
h _ show f g = 0 from (pseudoZero_iff (g ≫ f : Over Q)).2 hg

中文:
定理 mono_of_zero_of_map_zero
  条件: {P Q : C} (f : P ⟶ Q)
  结论: (对任意 a, f a = 0 -> a = 0) -> 单态射 f
  证明: fun h => (mono_iff_cancel_zero _).2 fun _ g hg =>
(pseudoZero_iff (g : Over P)).1
h _ show f g = 0 from (pseudoZero_iff (g ≫ f : Over Q)).2 hg

Depends on / 依赖: mono_iff_cancel_zero, pseudoZero_iff
-/
theorem mono_of_zero_of_map_zero {P Q : C} (f : P ⟶ Q) : (forall a, f a = 0 -> a = 0) -> Mono f :=
  fun h => (mono_iff_cancel_zero _).2 fun _ g hg =>
(pseudoZero_iff (g : Over P)).1
h _ show f g = 0 from (pseudoZero_iff (g ≫ f : Over Q)).2 hg

section

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pseudo_surjective_of_epi` / 定理 `pseudo_surjective_of_epi`

English:
theorem pseudo_surjective_of_epi
  given: {P Q : C} (f : P ⟶ Q) [Epi f]
  statement: Function.Surjective f
  proof: fun qbar =>
  Quotient.inductionOn qbar fun q =>
    ⟨(pullback.fst f q.hom : Over P),
Quotient.sound
        ⟨pullback f q.hom, 𝟙 (pullback f q.hom), pullback.snd _ _, inferInstance, inferInstance, by
          rw [Category.id_comp]; rw [← pullback.condition]; rw [app_hom]; rw [Over.coe_hom]⟩⟩

中文:
定理 pseudo_surjective_of_epi
  条件: {P Q : C} (f : P ⟶ Q) [满态射 f]
  结论: 函数.满射 f
  证明: fun qbar =>
  Quotient.inductionOn qbar fun q =>
    ⟨(pullback.fst f q.hom : Over P),
Quotient.sound
        ⟨pullback f q.hom, 𝟙 (pullback f q.hom), pullback.snd _ _, inferInstance, inferInstance, by
          rw [Category.id_comp]; rw [← pullback.condition]; rw [app_hom]; rw [Over.coe_hom]⟩⟩

Depends on / 依赖: Category, Category.id_comp, Over.coe_hom, Quotient, Quotient.inductionOn, Quotient.sound, app_hom, coe_hom, condition, id_comp, inductionOn, pullback, pullback.condition, pullback.fst, pullback.snd, q.hom
-/
theorem pseudo_surjective_of_epi {P Q : C} (f : P ⟶ Q) [Epi f] : Function.Surjective f :=
  fun qbar =>
  Quotient.inductionOn qbar fun q =>
    ⟨(pullback.fst f q.hom : Over P),
Quotient.sound
        ⟨pullback f q.hom, 𝟙 (pullback f q.hom), pullback.snd _ _, inferInstance, inferInstance, by
          rw [Category.id_comp]; rw [← pullback.condition]; rw [app_hom]; rw [Over.coe_hom]⟩⟩

end

set_option backward.isDefEq.respectTransparency false in
/--
theorem `epi_of_pseudo_surjective` / 定理 `epi_of_pseudo_surjective`

English:
theorem epi_of_pseudo_surjective
  given: {P Q : C} (f : P ⟶ Q)
  statement: Function.Surjective f -> Epi f
  proof: by
  intro h
  have ⟨pbar, hpbar⟩ := h (𝟙 Q)
  have ⟨p, hp⟩ := Quotient.exists_rep pbar
  have : (⟦(p.hom ≫ f : Over Q)⟧ : Quotient (setoid Q)) = ⟦↑(𝟙 Q)⟧ := by
    rw [← hp] at hpbar
    exact hpbar
  have ⟨R, x, y, _, ey, comm⟩ := Quotient.exact this
  apply @epi_of_epi_fac _ _ _ _ _ (x ≫ p.hom) f

中文:
定理 epi_of_pseudo_surjective
  条件: {P Q : C} (f : P ⟶ Q)
  结论: 函数.满射 f -> 满态射 f
  证明: by
  intro h
  have ⟨pbar, hpbar⟩ := h (𝟙 Q)
  have ⟨p, hp⟩ := Quotient.exists_rep pbar
  have : (⟦(p.hom ≫ f : Over Q)⟧ : Quotient (setoid Q)) = ⟦↑(𝟙 Q)⟧ := by
    rw [← hp] at hpbar
    exact hpbar
  have ⟨R, x, y, _, ey, comm⟩ := Quotient.exact this
  apply @epi_of_epi_fac _ _ _ _ _ (x ≫ p.hom) f

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Quotient, Quotient.exact, Quotient.exists_rep, comp_id, epi_of_epi_fac, exists_rep, p.hom, setoid
-/
theorem epi_of_pseudo_surjective {P Q : C} (f : P ⟶ Q) : Function.Surjective f -> Epi f := by
  intro h
  have ⟨pbar, hpbar⟩ := h (𝟙 Q)
  have ⟨p, hp⟩ := Quotient.exists_rep pbar
  have : (⟦(p.hom ≫ f : Over Q)⟧ : Quotient (setoid Q)) = ⟦↑(𝟙 Q)⟧ := by
    rw [← hp] at hpbar
    exact hpbar
  have ⟨R, x, y, _, ey, comm⟩ := Quotient.exact this
  apply @epi_of_epi_fac _ _ _ _ _ (x ≫ p.hom) f y ey
  dsimp at comm
  rw [Category.assoc]; rw [comm]
  apply Category.comp_id

section

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pseudo_exact_of_exact` / 定理 `pseudo_exact_of_exact`

English:
theorem pseudo_exact_of_exact
  given: {S : ShortComplex C} (hS : S.Exact)
  proof: fun b' =>
    Quotient.inductionOn b' fun b hb => by
      have hb' : b.hom ≫ S.g = 0 := (pseudoZero_iff _).1 hb
      -- By exactness, `b` factors through `im f = ker g` via some `c`.
      obtain ⟨c, hc⟩ := KernelFork.IsLimit.lift' hS.isLimitImage _ hb'
      -- We compute the pullback of the map 

中文:
定理 pseudo_exact_of_exact
  条件: {S : 短复形 C} (hS : S.正合)
  证明: fun b' =>
    Quotient.inductionOn b' fun b hb => by
      have hb' : b.hom ≫ S.g = 0 := (pseudoZero_iff _).1 hb
      -- By exactness, `b` factors through `im f = ker g` via some `c`.
      obtain ⟨c, hc⟩ := KernelFork.IsLimit.lift' hS.isLimitImage _ hb'
      -- We compute the pullback of the map 

Depends on / 依赖: Quotient, Quotient.inductionOn, b.hom, inductionOn, pseudoZero_iff
-/
theorem pseudo_exact_of_exact {S : ShortComplex C} (hS : S.Exact) :
    forall b, S.g b = 0 -> exists a, S.f a = b :=
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
          rw [← Category.assoc]; rw [pullback.condition]
        _ = pullback.snd _ _ ≫ b.hom := by
          rw [Category.assoc]
          congr

end

set_option backward.defeqAttrib.useBackward true in
/--
theorem `apply_eq_zero_of_comp_eq_zero` / 定理 `apply_eq_zero_of_comp_eq_zero`

English:
theorem apply_eq_zero_of_comp_eq_zero
  given: {P Q R : C} (f : Q ⟶ R) (a : P ⟶ Q)
  statement: a ≫ f = 0 -> f a = 0
  proof: fun h => by simp [over_coe_def, pseudoApply_mk', h]

中文:
定理 apply_eq_zero_of_comp_eq_zero
  条件: {P Q R : C} (f : Q ⟶ R) (a : P ⟶ Q)
  结论: a ≫ f = 0 -> f a = 0
  证明: fun h => by simp [over_coe_def, pseudoApply_mk', h]

Depends on / 依赖: over_coe_def, pseudoApply_mk
-/
theorem apply_eq_zero_of_comp_eq_zero {P Q R : C} (f : Q ⟶ R) (a : P ⟶ Q) : a ≫ f = 0 -> f a = 0 :=
  fun h => by simp [over_coe_def, pseudoApply_mk', h]

section

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exact_of_pseudo_exact` / 定理 `exact_of_pseudo_exact`

English:
theorem exact_of_pseudo_exact
  statement: (S : ShortComplex C)
  proof: (S.exact_iff_kernel_ι_comp_cokernel_π_zero).2 (by
      -- If we apply `g` to the pseudoelement induced by its kernel, we get 0 (of course!).
      have : S.g (kernel.ι S.g) = 0 := apply_eq_zero_of_comp_eq_zero _ _ (kernel.condition _)
      -- By pseudo-exactness, we get a preimage.
      obtain ⟨a

中文:
定理 exact_of_pseudo_exact
  结论: (S : 短复形 C)
  证明: (S.exact_iff_kernel_ι_comp_cokernel_π_zero).2 (by
      -- If we apply `g` to the pseudoelement induced by its kernel, we get 0 (of course!).
      have : S.g (kernel.ι S.g) = 0 := apply_eq_zero_of_comp_eq_zero _ _ (kernel.condition _)
      -- By pseudo-exactness, we get a preimage.
      obtain ⟨a

Depends on / 依赖: S.exact_iff_kernel_
-/
theorem exact_of_pseudo_exact (S : ShortComplex C)
    (hS : forall b, S.g b = 0 -> exists a, S.f a = b) : S.Exact :=
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
/--
theorem `sub_of_eq_image` / 定理 `sub_of_eq_image`

English:
theorem sub_of_eq_image
  given: {P Q : C} (f : P ⟶ Q) (x y : P)
  proof: Quotient.inductionOn₂ x y fun a a' h =>
    match Quotient.exact h with
    | ⟨R, p, q, ep, _, comm⟩ =>
      let a'' : R ⟶ P := (p ≫ a.hom : R ⟶ P) - (q ≫ a'.hom : R ⟶ P)
      ⟨a'',
        ⟨show ⟦(a'' ≫ f : Over Q)⟧ = ⟦↑(0 : Q ⟶ Q)⟧ by
            dsimp at comm
            simp [a'', sub_eq_zero.

中文:
定理 sub_of_eq_image
  条件: {P Q : C} (f : P ⟶ Q) (x y : P)
  证明: Quotient.inductionOn₂ x y fun a a' h =>
    match Quotient.exact h with
    | ⟨R, p, q, ep, _, comm⟩ =>
      let a'' : R ⟶ P := (p ≫ a.hom : R ⟶ P) - (q ≫ a'.hom : R ⟶ P)
      ⟨a'',
        ⟨show ⟦(a'' ≫ f : Over Q)⟧ = ⟦↑(0 : Q ⟶ Q)⟧ by
            dsimp at comm
            simp [a'', sub_eq_zero.

Depends on / 依赖: Quotient, Quotient.exact, Quotient.inductionOn, Quotient.sound, a.hom, epi_iff_cancel_zero, sub_eq_zero
-/
theorem sub_of_eq_image {P Q : C} (f : P ⟶ Q) (x y : P) :
    f x = f y -> exists z, f z = 0 ∧ forall (R : C) (g : P ⟶ R), (g : P ⟶ R) y = 0 -> g z = g x :=
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
/--
theorem `pseudo_pullback` / 定理 `pseudo_pullback`

English:
theorem pseudo_pullback
  given: {P Q R : C} {f : P ⟶ R} {g : Q ⟶ R} {p : P} {q : Q}
  proof: Quotient.inductionOn₂ p q fun x y h => by
    obtain ⟨Z, a, b, ea, eb, comm⟩ := Quotient.exact h
    obtain ⟨l, hl₁, hl₂⟩ := @pullback.lift' _ _ _ _ _ _ f g _ (a ≫ x.hom) (b ≫ y.hom) (by
      simp only [Category.assoc]
      exact comm)
    exact ⟨l, ⟨Quotient.sound ⟨Z, 𝟙 Z, a, inferInstance, ea, b

中文:
定理 pseudo_pullback
  条件: {P Q R : C} {f : P ⟶ R} {g : Q ⟶ R} {p : P} {q : Q}
  证明: Quotient.inductionOn₂ p q fun x y h => by
    obtain ⟨Z, a, b, ea, eb, comm⟩ := Quotient.exact h
    obtain ⟨l, hl₁, hl₂⟩ := @pullback.lift' _ _ _ _ _ _ f g _ (a ≫ x.hom) (b ≫ y.hom) (by
      simp only [Category.assoc]
      exact comm)
    exact ⟨l, ⟨Quotient.sound ⟨Z, 𝟙 Z, a, inferInstance, ea, b

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Quotient, Quotient.exact, Quotient.inductionOn, Quotient.sound, id_comp, pullback, pullback.lift, x.hom, y.hom
-/
theorem pseudo_pullback {P Q R : C} {f : P ⟶ R} {g : Q ⟶ R} {p : P} {q : Q} :
    f p = g q ->
      exists s, pullback.fst f g s = p ∧ pullback.snd f g s = q :=
  Quotient.inductionOn₂ p q fun x y h => by
    obtain ⟨Z, a, b, ea, eb, comm⟩ := Quotient.exact h
    obtain ⟨l, hl₁, hl₂⟩ := @pullback.lift' _ _ _ _ _ _ f g _ (a ≫ x.hom) (b ≫ y.hom) (by
      simp only [Category.assoc]
      exact comm)
    exact ⟨l, ⟨Quotient.sound ⟨Z, 𝟙 Z, a, inferInstance, ea, by rwa [Category.id_comp]⟩,
      Quotient.sound ⟨Z, 𝟙 Z, b, inferInstance, eb, by rwa [Category.id_comp]⟩⟩⟩

section Module

/--
theorem `ModuleCat.eq_range_of_pseudoequal` / 定理 `ModuleCat.eq_range_of_pseudoequal`

English:
theorem ModuleCat.eq_range_of_pseudoequal
  statement: {R : Type*} [Ring R] {G : ModuleCat R} {x y : Over G}
  proof: by
  obtain ⟨P, p, q, hp, hq, H⟩ := h
  refine Submodule.ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨a', ha'⟩ := ha
    obtain ⟨a'', ha''⟩ := (ModuleCat.epi_iff_surjective p).1 hp a'
    refine ⟨q a'', ?_⟩
    dsimp at ha' ⊢
    rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [←

中文:
定理 模范畴.eq_range_of_pseudoequal
  结论: {R : 类型} [环 R] {G : 模范畴 R} {x y : Over G}
  证明: by
  obtain ⟨P, p, q, hp, hq, H⟩ := h
  refine Submodule.ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨a', ha'⟩ := ha
    obtain ⟨a'', ha''⟩ := (ModuleCat.epi_iff_surjective p).1 hp a'
    refine ⟨q a'', ?_⟩
    dsimp at ha' ⊢
    rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [←

Depends on / 依赖: LinearMap, LinearMap.comp_ap, LinearMap.comp_apply, ModuleCat, ModuleCat.epi_iff_surjective, ModuleCat.hom_comp, Submodule, Submodule.ext, comp_ap, comp_apply, epi_iff_surjective, hom_comp
-/
theorem ModuleCat.eq_range_of_pseudoequal {R : Type*} [Ring R] {G : ModuleCat R} {x y : Over G}
    (h : PseudoEqual G x y) : LinearMap.range x.hom.hom = LinearMap.range y.hom.hom := by
  obtain ⟨P, p, q, hp, hq, H⟩ := h
  refine Submodule.ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨a', ha'⟩ := ha
    obtain ⟨a'', ha''⟩ := (ModuleCat.epi_iff_surjective p).1 hp a'
    refine ⟨q a'', ?_⟩
    dsimp at ha' ⊢
    rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [← H]; rw [ModuleCat.hom_comp]; rw [LinearMap.comp_apply]; rw [ha'']; rw [ha']
  · obtain ⟨a', ha'⟩ := ha
    obtain ⟨a'', ha''⟩ := (ModuleCat.epi_iff_surjective q).1 hq a'
    refine ⟨p a'', ?_⟩
    dsimp at ha' ⊢
    rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [H]; rw [ModuleCat.hom_comp]; rw [LinearMap.comp_apply]; rw [ha'']; rw [ha']

end Module

end Pseudoelement

end CategoryTheory.Abelian
