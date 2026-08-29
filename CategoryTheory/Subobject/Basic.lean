/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Skeleton
public import Mathlib.CategoryTheory.Subobject.MonoOver
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.Tactic.ApplyFun
public import Mathlib.Tactic.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Subobjects

We define `Subobject X` as the quotient (by isomorphisms) of
`MonoOver X := {f : Over X // Mono f.hom}`.

Here `MonoOver X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not a partial order.

There is a coercion from `Subobject X` back to the ambient category `C`
(using choice to pick a representative), and for `P : Subobject X`,
`P.arrow : (P : C) ⟶ X` is the inclusion morphism.

We provide
* `def pullback [HasPullbacks C] (f : X ⟶ Y) : Subobject Y ⥤ Subobject X`
* `def map (f : X ⟶ Y) [Mono f] : Subobject X ⥤ Subobject Y`
* `def «exists_» [HasImages C] (f : X ⟶ Y) : Subobject X ⥤ Subobject Y`

and prove their basic properties and relationships.
These are all easy consequences of the earlier development
of the corresponding functors for `MonoOver`.

The subobjects of `X` form a preorder making them into a category. We have `X ≤ Y` if and only if
`X.arrow` factors through `Y.arrow`: see `ofLE`/`ofLEMk`/`ofMkLE`/`ofMkLEMk` and
`le_of_comm`. Similarly, to show that two subobjects are equal, we can supply an isomorphism between
the underlying objects that commutes with the arrows (`eq_of_comm`).

See also

* `CategoryTheory.Subobject.factorThru` :
  an API describing factorization of morphisms through subobjects.
* `CategoryTheory.Subobject.lattice` :
  the lattice structures on subobjects.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Kim Morrison.

### Implementation note

Currently we describe `pullback`, `map`, etc., as functors.
It may be better to just say that they are monotone functions,
and even avoid using categorical language entirely when describing `Subobject X`.
(It's worth keeping this in mind in future use; it should be a relatively easy change here
if it looks preferable.)

### Relation to pseudoelements

There is a separate development of pseudoelements in `CategoryTheory.Abelian.Pseudoelements`,
as a quotient (but not by isomorphism) of `Over X`.

When a morphism `f` has an image, the image represents the same pseudoelement.
In a category with images `Pseudoelements X` could be constructed as a quotient of `MonoOver X`.
In fact, in an abelian category (I'm not sure in what generality beyond that),
`Pseudoelements X` agrees with `Subobject X`, but we haven't developed this in mathlib yet.

-/

@[expose] public section


universe w' w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}
variable {D : Type u₂} [Category.{v₂} D]

/-!
We now construct the subobject lattice for `X : C`,
as the quotient by isomorphisms of `MonoOver X`.

Since `MonoOver X` is a thin category, we use `ThinSkeleton` to take the quotient.

Essentially all the structure defined above on `MonoOver X` descends to `Subobject X`,
with morphisms becoming inequalities, and isomorphisms becoming equations.
-/


/-- The category of subobjects of `X : C`, defined as isomorphism classes of monomorphisms into `X`.
-/
@[implicit_reducible]
/--
Definition of `Subobject` / `Subobject` 的定义

English:
definition Subobject
  signature: (X : C)
  body: ThinSkeleton (MonoOver X)

中文:
定义 Subobject
  签名: (X : C)
  定义体: ThinSkeleton (MonoOver X)

Depends on / 依赖: MonoOver, ThinSkeleton
-/
def Subobject (X : C) :=
  ThinSkeleton (MonoOver X)

instance (X : C) : PartialOrder (Subobject X) :=
inferInstanceAs PartialOrder (ThinSkeleton (MonoOver X))

namespace Subobject

/--
lemma `skeletal` / 引理 `skeletal`

English:
lemma skeletal
  given: (X : C)
  statement: Skeletal (Subobject X)
  proof: ThinSkeleton.skeletal

中文:
引理 skeletal
  条件: (X : C)
  结论: Skeletal (Subobject X)
  证明: ThinSkeleton.skeletal

Depends on / 依赖: ThinSkeleton, ThinSkeleton.skeletal, skeletal
-/
lemma skeletal (X : C) : Skeletal (Subobject X) := ThinSkeleton.skeletal

/-- Convenience constructor for a subobject. -/
@[implicit_reducible]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {X A : C} (f : A ⟶ X) [Mono f]
  body: (toThinSkeleton _).obj (MonoOver.mk f)

中文:
定义 mk
  签名: {X A : C} (f : A ⟶ X) [Mono f]
  定义体: (toThinSkeleton _).obj (MonoOver.mk f)

Depends on / 依赖: MonoOver, MonoOver.mk, toThinSkeleton
-/
def mk {X A : C} (f : A ⟶ X) [Mono f] : Subobject X :=
  (toThinSkeleton _).obj (MonoOver.mk f)

section

attribute [local ext] CategoryTheory.Comma

/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  statement: {X : C} (p : Subobject X -> Prop)
  proof: by
  induction P using Quotient.inductionOn' with | _ a
  exact h a.arrow

中文:
定理 ind
  结论: {X : C} (p : Subobject X -> 命题)
  证明: by
  induction P using Quotient.inductionOn' with | _ a
  exact h a.arrow
-/
protected theorem ind {X : C} (p : Subobject X -> Prop)
    (h : forall ⦃A : C⦄ (f : A ⟶ X) [Mono f], p (Subobject.mk f)) (P : Subobject X) : p P := by
  induction P using Quotient.inductionOn' with | _ a
  exact h a.arrow

/--
theorem `ind₂` / 定理 `ind₂`

English:
theorem ind₂
  statement: {X : C} (p : Subobject X -> Subobject X -> Prop)
  proof: by
  induction P, Q using Quotient.inductionOn₂' with | _ a b
  exact h a.arrow b.arrow

中文:
定理 ind₂
  结论: {X : C} (p : Subobject X -> Subobject X -> 命题)
  证明: by
  induction P, Q using Quotient.inductionOn₂' with | _ a b
  exact h a.arrow b.arrow
-/
protected theorem ind₂ {X : C} (p : Subobject X -> Subobject X -> Prop)
    (h : forall ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g],
      p (Subobject.mk f) (Subobject.mk g))
    (P Q : Subobject X) : p P Q := by
  induction P, Q using Quotient.inductionOn₂' with | _ a b
  exact h a.arrow b.arrow

end

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {α : Sort*} {X : C} (F : forall ⦃A : C⦄ (f : A ⟶ X) [Mono f], α)
  body: fun P =>
  Quotient.liftOn' P (fun m => F m.arrow) fun m n ⟨i⟩ =>
    h m.arrow n.arrow ((MonoOver.forget X ⋙ Over.forget X).mapIso i) (Over.w i.hom.hom)

@[simp]

中文:
定义 lift
  签名: {α : Sort*} {X : C} (F : 对任意 ⦃A : C⦄ (f : A ⟶ X) [Mono f], α)
  定义体: fun P =>
  Quotient.liftOn' P (fun m => F m.arrow) fun m n ⟨i⟩ =>
    h m.arrow n.arrow ((MonoOver.forget X ⋙ Over.forget X).mapIso i) (Over.w i.hom.hom)

@[simp]
-/
protected def lift {α : Sort*} {X : C} (F : forall ⦃A : C⦄ (f : A ⟶ X) [Mono f], α)
    (h :
      forall ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g] (i : A ≅ B),
        i.hom ≫ g = f -> F f = F g) :
    Subobject X -> α := fun P =>
  Quotient.liftOn' P (fun m => F m.arrow) fun m n ⟨i⟩ =>
    h m.arrow n.arrow ((MonoOver.forget X ⋙ Over.forget X).mapIso i) (Over.w i.hom.hom)

@[simp]
/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  statement: {α : Sort*} {X : C} (F : forall ⦃A : C⦄ (f : A ⟶ X) [Mono f], α) {h A}
  proof: rfl

中文:
定理 lift_mk
  结论: {α : Sort*} {X : C} (F : 对任意 ⦃A : C⦄ (f : A ⟶ X) [Mono f], α) {h A}
  证明: rfl
-/
protected theorem lift_mk {α : Sort*} {X : C} (F : forall ⦃A : C⦄ (f : A ⟶ X) [Mono f], α) {h A}
    (f : A ⟶ X) [Mono f] : Subobject.lift F h (Subobject.mk f) = F f :=
  rfl

/--
Definition of `equivMonoOver` / `equivMonoOver` 的定义

English:
definition equivMonoOver
  signature: (X : C)
  body: ThinSkeleton.equivalence _

中文:
定义 equivMonoOver
  签名: (X : C)
  定义体: ThinSkeleton.equivalence _

Depends on / 依赖: ThinSkeleton, ThinSkeleton.equivalence, equivalence
-/
noncomputable def equivMonoOver (X : C) : Subobject X ≌ MonoOver X :=
  ThinSkeleton.equivalence _

/--
Definition of `representative` / `representative` 的定义

English:
definition representative
  signature: {X : C}
  body: (equivMonoOver X).functor

中文:
定义 representative
  签名: {X : C}
  定义体: (equivMonoOver X).functor

Depends on / 依赖: equivMonoOver, functor
-/
noncomputable def representative {X : C} : Subobject X ⥤ MonoOver X :=
  (equivMonoOver X).functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (representative (X := X)).IsEquivalence
  body: (equivMonoOver X).isEquivalence_functor

中文:
实例 :
  签名: (representative (X := X)).IsEquivalence
  定义体: (equivMonoOver X).isEquivalence_functor

Depends on / 依赖: IsEquivalence
-/
instance : (representative (X := X)).IsEquivalence :=
  (equivMonoOver X).isEquivalence_functor

/--
Definition of `representativeIso` / `representativeIso` 的定义

English:
definition representativeIso
  signature: {X : C} (A : MonoOver X)
  body: (equivMonoOver X).counitIso.app A

@[simp]

中文:
定义 representativeIso
  签名: {X : C} (A : MonoOver X)
  定义体: (equivMonoOver X).counitIso.app A

@[simp]

Depends on / 依赖: counitIso, counitIso.app, equivMonoOver
-/
noncomputable def representativeIso {X : C} (A : MonoOver X) :
    representative.obj ((toThinSkeleton _).obj A) ≅ A :=
  (equivMonoOver X).counitIso.app A

@[simp]
/--
lemma `thinSkeleton_mk_representative_eq_self` / 引理 `thinSkeleton_mk_representative_eq_self`

English:
lemma thinSkeleton_mk_representative_eq_self
  given: {X : C} (A : Subobject X)
  proof: Subobject.skeletal _ ⟨((equivMonoOver X).unitIso.app _).symm⟩

中文:
引理 thinSkeleton_mk_representative_eq_self
  条件: {X : C} (A : Subobject X)
  证明: Subobject.skeletal _ ⟨((equivMonoOver X).unitIso.app _).symm⟩

Depends on / 依赖: Subobject, Subobject.skeletal, equivMonoOver, skeletal, unitIso, unitIso.app
-/
lemma thinSkeleton_mk_representative_eq_self {X : C} (A : Subobject X) :
    ThinSkeleton.mk (representative.obj A) = A :=
  Subobject.skeletal _ ⟨((equivMonoOver X).unitIso.app _).symm⟩

/--
Definition of `underlying` / `underlying` 的定义

English:
definition underlying
  signature: {X : C}
  body: representative ⋙ MonoOver.forget _ ⋙ Over.forget _

中文:
定义 underlying
  签名: {X : C}
  定义体: representative ⋙ MonoOver.forget _ ⋙ Over.forget _

Depends on / 依赖: MonoOver, MonoOver.forget, Over.forget, forget, representative
-/
noncomputable def underlying {X : C} : Subobject X ⥤ C :=
  representative ⋙ MonoOver.forget _ ⋙ Over.forget _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (Subobject X) C
  body: underlying.obj Y

中文:
实例 :
  签名: CoeOut (Subobject X) C
  定义体: underlying.obj Y

Depends on / 依赖: underlying, underlying.obj
-/
instance : CoeOut (Subobject X) C where coe Y := underlying.obj Y

/--
Definition of `underlyingIso` / `underlyingIso` 的定义

English:
definition underlyingIso
  signature: {X Y : C} (f : X ⟶ Y) [Mono f]
  body: (MonoOver.forget _ ⋙ Over.forget _).mapIso (representativeIso (MonoOver.mk f))

中文:
定义 underlyingIso
  签名: {X Y : C} (f : X ⟶ Y) [Mono f]
  定义体: (MonoOver.forget _ ⋙ Over.forget _).mapIso (representativeIso (MonoOver.mk f))

Depends on / 依赖: MonoOver, MonoOver.forget, MonoOver.mk, Over.forget, forget, mapIso, representativeIso
-/
noncomputable def underlyingIso {X Y : C} (f : X ⟶ Y) [Mono f] : (Subobject.mk f : C) ≅ X :=
  (MonoOver.forget _ ⋙ Over.forget _).mapIso (representativeIso (MonoOver.mk f))

/--
Definition of `arrow` / `arrow` 的定义

English:
definition arrow
  signature: {X : C} (Y : Subobject X)
  body: (representative.obj Y).obj.hom

中文:
定义 arrow
  签名: {X : C} (Y : Subobject X)
  定义体: (representative.obj Y).obj.hom

Depends on / 依赖: obj.hom, representative, representative.obj
-/
noncomputable def arrow {X : C} (Y : Subobject X) : (Y : C) ⟶ X :=
  (representative.obj Y).obj.hom

/--
Instance `arrow_mono` / 实例 `arrow_mono`

English:
instance arrow_mono
  signature: {X : C} (Y : Subobject X)
  body: (representative.obj Y).property

@[simp]

中文:
实例 arrow_mono
  签名: {X : C} (Y : Subobject X)
  定义体: (representative.obj Y).property

@[simp]

Depends on / 依赖: property, representative, representative.obj
-/
instance arrow_mono {X : C} (Y : Subobject X) : Mono Y.arrow :=
  (representative.obj Y).property

@[simp]
/--
theorem `arrow_congr` / 定理 `arrow_congr`

English:
theorem arrow_congr
  given: {A : C} (X Y : Subobject A) (h : X = Y)
  proof: by
  induction h
  simp

@[simp]

中文:
定理 arrow_congr
  条件: {A : C} (X Y : Subobject A) (h : X = Y)
  证明: by
  induction h
  simp

@[simp]
-/
theorem arrow_congr {A : C} (X Y : Subobject A) (h : X = Y) :
    eqToHom (congr_arg (fun X : Subobject A => (X : C)) h) ≫ Y.arrow = X.arrow := by
  induction h
  simp

@[simp]
/--
theorem `representative_coe` / 定理 `representative_coe`

English:
theorem representative_coe
  given: (Y : Subobject X)
  statement: (representative.obj Y : C) = (Y : C)
  proof: rfl

@[simp]

中文:
定理 representative_coe
  条件: (Y : Subobject X)
  结论: (representative.obj Y : C) = (Y : C)
  证明: rfl

@[simp]
-/
theorem representative_coe (Y : Subobject X) : (representative.obj Y : C) = (Y : C) :=
  rfl

@[simp]
/--
theorem `representative_arrow` / 定理 `representative_arrow`

English:
theorem representative_arrow
  given: (Y : Subobject X)
  statement: (representative.obj Y).arrow = Y.arrow
  proof: rfl

@[reassoc (attr := simp)]

中文:
定理 representative_arrow
  条件: (Y : Subobject X)
  结论: (representative.obj Y).arrow = Y.arrow
  证明: rfl

@[reassoc (attr := simp)]
-/
theorem representative_arrow (Y : Subobject X) : (representative.obj Y).arrow = Y.arrow :=
  rfl

@[reassoc (attr := simp)]
/--
theorem `underlying_arrow` / 定理 `underlying_arrow`

English:
theorem underlying_arrow
  given: {X : C} {Y Z : Subobject X} (f : Y ⟶ Z)
  proof: Over.w (representative.map f).hom

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定理 underlying_arrow
  条件: {X : C} {Y Z : Subobject X} (f : Y ⟶ Z)
  证明: Over.w (representative.map f).hom

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: Over.w, representative, representative.map
-/
theorem underlying_arrow {X : C} {Y Z : Subobject X} (f : Y ⟶ Z) :
    underlying.map f ≫ arrow Z = arrow Y :=
  Over.w (representative.map f).hom

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `underlyingIso_arrow` / 定理 `underlyingIso_arrow`

English:
theorem underlyingIso_arrow
  given: {X Y : C} (f : X ⟶ Y) [Mono f]
  proof: Over.w _

@[reassoc (attr := simp)]

中文:
定理 underlyingIso_arrow
  条件: {X Y : C} (f : X ⟶ Y) [Mono f]
  证明: Over.w _

@[reassoc (attr := simp)]

Depends on / 依赖: Over.w
-/
theorem underlyingIso_arrow {X Y : C} (f : X ⟶ Y) [Mono f] :
    (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f :=
  Over.w _

@[reassoc (attr := simp)]
/--
theorem `underlyingIso_hom_comp_eq_mk` / 定理 `underlyingIso_hom_comp_eq_mk`

English:
theorem underlyingIso_hom_comp_eq_mk
  given: {X Y : C} (f : X ⟶ Y) [Mono f]
  proof: (Iso.eq_inv_comp _).1 (underlyingIso_arrow f).symm

中文:
定理 underlyingIso_hom_comp_eq_mk
  条件: {X Y : C} (f : X ⟶ Y) [Mono f]
  证明: (Iso.eq_inv_comp _).1 (underlyingIso_arrow f).symm

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp, underlyingIso_arrow
-/
theorem underlyingIso_hom_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] :
    (underlyingIso f).hom ≫ f = (mk f).arrow :=
  (Iso.eq_inv_comp _).1 (underlyingIso_arrow f).symm

/-- Two morphisms into a subobject are equal exactly if
the morphisms into the ambient object are equal -/
@[ext]
/--
theorem `eq_of_comp_arrow_eq` / 定理 `eq_of_comp_arrow_eq`

English:
theorem eq_of_comp_arrow_eq
  statement: {X Y : C} {P : Subobject Y} {f g : X ⟶ P}
  proof: (cancel_mono P.arrow).mp h

中文:
定理 eq_of_comp_arrow_eq
  结论: {X Y : C} {P : Subobject Y} {f g : X ⟶ P}
  证明: (cancel_mono P.arrow).mp h

Depends on / 依赖: P.arrow, cancel_mono
-/
theorem eq_of_comp_arrow_eq {X Y : C} {P : Subobject Y} {f g : X ⟶ P}
    (h : f ≫ P.arrow = g ≫ P.arrow) : f = g :=
  (cancel_mono P.arrow).mp h

/--
theorem `mk_le_mk_of_comm` / 定理 `mk_le_mk_of_comm`

English:
theorem mk_le_mk_of_comm
  statement: {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂)
  proof: ⟨MonoOver.homMk _ w⟩

@[simp]

中文:
定理 mk_le_mk_of_comm
  结论: {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂)
  证明: ⟨MonoOver.homMk _ w⟩

@[simp]

Depends on / 依赖: MonoOver, MonoOver.homMk
-/
theorem mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂)
    (w : g ≫ f₂ = f₁) : mk f₁ <= mk f₂ :=
  ⟨MonoOver.homMk _ w⟩

@[simp]
/--
theorem `mk_arrow` / 定理 `mk_arrow`

English:
theorem mk_arrow
  given: (P : Subobject X)
  statement: mk P.arrow = P
  proof: Quotient.inductionOn' P fun Q => by
    obtain ⟨e⟩ := @Quotient.mk_out' _ (isIsomorphicSetoid _) Q
    exact Quotient.sound' ⟨MonoOver.isoMk (Iso.refl _) ≪≫ e⟩

中文:
定理 mk_arrow
  条件: (P : Subobject X)
  结论: mk P.arrow = P
  证明: Quotient.inductionOn' P fun Q => by
    obtain ⟨e⟩ := @Quotient.mk_out' _ (isIsomorphicSetoid _) Q
    exact Quotient.sound' ⟨MonoOver.isoMk (Iso.refl _) ≪≫ e⟩

Depends on / 依赖: Iso.refl, MonoOver, MonoOver.isoMk, Quotient, Quotient.inductionOn, Quotient.mk_out, Quotient.sound, inductionOn, isIsomorphicSetoid, mk_out
-/
theorem mk_arrow (P : Subobject X) : mk P.arrow = P :=
  Quotient.inductionOn' P fun Q => by
    obtain ⟨e⟩ := @Quotient.mk_out' _ (isIsomorphicSetoid _) Q
    exact Quotient.sound' ⟨MonoOver.isoMk (Iso.refl _) ≪≫ e⟩

/--
theorem `le_of_comm` / 定理 `le_of_comm`

English:
theorem le_of_comm
  given: {B : C} {X Y : Subobject B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow)
  proof: by
  convert! mk_le_mk_of_comm _ w <;> simp

中文:
定理 le_of_comm
  条件: {B : C} {X Y : Subobject B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow)
  证明: by
  convert! mk_le_mk_of_comm _ w <;> simp

Depends on / 依赖: convert, mk_le_mk_of_comm
-/
theorem le_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) :
    X <= Y := by
  convert! mk_le_mk_of_comm _ w <;> simp

/--
theorem `le_mk_of_comm` / 定理 `le_mk_of_comm`

English:
theorem le_mk_of_comm
  statement: {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : (X : C) ⟶ A)
  proof: le_of_comm (g ≫ (underlyingIso f).inv) by simp [w]

中文:
定理 le_mk_of_comm
  结论: {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : (X : C) ⟶ A)
  证明: le_of_comm (g ≫ (underlyingIso f).inv) by simp [w]

Depends on / 依赖: le_of_comm, underlyingIso
-/
theorem le_mk_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : (X : C) ⟶ A)
    (w : g ≫ f = X.arrow) : X <= mk f :=
le_of_comm (g ≫ (underlyingIso f).inv) by simp [w]

/--
theorem `mk_le_of_comm` / 定理 `mk_le_of_comm`

English:
theorem mk_le_of_comm
  statement: {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : A ⟶ (X : C))
  proof: le_of_comm ((underlyingIso f).hom ≫ g) by simp [w]

中文:
定理 mk_le_of_comm
  结论: {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : A ⟶ (X : C))
  证明: le_of_comm ((underlyingIso f).hom ≫ g) by simp [w]

Depends on / 依赖: le_of_comm, underlyingIso
-/
theorem mk_le_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : A ⟶ (X : C))
    (w : g ≫ X.arrow = f) : mk f <= X :=
le_of_comm ((underlyingIso f).hom ≫ g) by simp [w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
the arrows. -/
@[ext (iff := false)]
/--
theorem `eq_of_comm` / 定理 `eq_of_comm`

English:
theorem eq_of_comm
  statement: {B : C} {X Y : Subobject B} (f : (X : C) ≅ (Y : C))
  proof: le_antisymm (le_of_comm f.hom w) le_of_comm f.inv f.inv_comp_eq.2 w.symm

中文:
定理 eq_of_comm
  结论: {B : C} {X Y : Subobject B} (f : (X : C) ≅ (Y : C))
  证明: le_antisymm (le_of_comm f.hom w) le_of_comm f.inv f.inv_comp_eq.2 w.symm

Depends on / 依赖: f.hom, f.inv, f.inv_comp_eq, inv_comp_eq, le_antisymm, le_of_comm, w.symm
-/
theorem eq_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ≅ (Y : C))
    (w : f.hom ≫ Y.arrow = X.arrow) : X = Y :=
le_antisymm (le_of_comm f.hom w) le_of_comm f.inv f.inv_comp_eq.2 w.symm

/--
theorem `eq_mk_of_comm` / 定理 `eq_mk_of_comm`

English:
theorem eq_mk_of_comm
  statement: {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : (X : C) ≅ A)
  proof: eq_of_comm (i.trans (underlyingIso f).symm) by simp [w]

中文:
定理 eq_mk_of_comm
  结论: {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : (X : C) ≅ A)
  证明: eq_of_comm (i.trans (underlyingIso f).symm) by simp [w]

Depends on / 依赖: eq_of_comm, i.trans, underlyingIso
-/
theorem eq_mk_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : (X : C) ≅ A)
    (w : i.hom ≫ f = X.arrow) : X = mk f :=
eq_of_comm (i.trans (underlyingIso f).symm) by simp [w]

/--
theorem `mk_eq_of_comm` / 定理 `mk_eq_of_comm`

English:
theorem mk_eq_of_comm
  statement: {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : A ≅ (X : C))
  proof: Eq.symm eq_mk_of_comm _ i.symm by rw [Iso.symm_hom, Iso.inv_comp_eq, w]

中文:
定理 mk_eq_of_comm
  结论: {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : A ≅ (X : C))
  证明: Eq.symm eq_mk_of_comm _ i.symm by rw [Iso.symm_hom, Iso.inv_comp_eq, w]

Depends on / 依赖: Eq.symm, Iso.inv_comp_eq, Iso.symm_hom, eq_mk_of_comm, i.symm, inv_comp_eq, symm_hom
-/
theorem mk_eq_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : A ≅ (X : C))
    (w : i.hom ≫ X.arrow = f) : mk f = X :=
Eq.symm eq_mk_of_comm _ i.symm by rw [Iso.symm_hom, Iso.inv_comp_eq, w]

/--
theorem `mk_eq_mk_of_comm` / 定理 `mk_eq_mk_of_comm`

English:
theorem mk_eq_mk_of_comm
  statement: {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂)
  proof: eq_mk_of_comm _ ((underlyingIso f).trans i) by simp [w]

中文:
定理 mk_eq_mk_of_comm
  结论: {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂)
  证明: eq_mk_of_comm _ ((underlyingIso f).trans i) by simp [w]

Depends on / 依赖: eq_mk_of_comm, underlyingIso
-/
theorem mk_eq_mk_of_comm {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂)
    (w : i.hom ≫ g = f) : mk f = mk g :=
eq_mk_of_comm _ ((underlyingIso f).trans i) by simp [w]

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: {X : C} (S : Subobject X)
  proof: ⟨_, S.arrow, inferInstance, by simp⟩

中文:
引理 mk_surjective
  条件: {X : C} (S : Subobject X)
  证明: ⟨_, S.arrow, inferInstance, by simp⟩

Depends on / 依赖: S.arrow
-/
lemma mk_surjective {X : C} (S : Subobject X) :
    exists (A : C) (i : A ⟶ X) (_ : Mono i), S = Subobject.mk i :=
  ⟨_, S.arrow, inferInstance, by simp⟩

-- We make `X` and `Y` explicit arguments here so that when `ofLE` appears in goal statements
-- it is possible to see its source and target
-- (`h` will just display as `_`, because it is in `Prop`).
/--
Definition of `ofLE` / `ofLE` 的定义

English:
definition ofLE
  signature: {B : C} (X Y : Subobject B) (h : X <= Y)
  body: underlying.map h.hom

@[reassoc (attr := simp)]

中文:
定义 ofLE
  签名: {B : C} (X Y : Subobject B) (h : X <= Y)
  定义体: underlying.map h.hom

@[reassoc (attr := simp)]

Depends on / 依赖: h.hom, underlying, underlying.map
-/
def ofLE {B : C} (X Y : Subobject B) (h : X <= Y) : (X : C) ⟶ (Y : C) :=
underlying.map h.hom

@[reassoc (attr := simp)]
/--
theorem `ofLE_arrow` / 定理 `ofLE_arrow`

English:
theorem ofLE_arrow
  given: {B : C} {X Y : Subobject B} (h : X <= Y)
  statement: ofLE X Y h ≫ Y.arrow = X.arrow
  proof: underlying_arrow _

中文:
定理 ofLE_arrow
  条件: {B : C} {X Y : Subobject B} (h : X <= Y)
  结论: ofLE X Y h ≫ Y.arrow = X.arrow
  证明: underlying_arrow _

Depends on / 依赖: underlying_arrow
-/
theorem ofLE_arrow {B : C} {X Y : Subobject B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow :=
  underlying_arrow _

instance {B : C} (X Y : Subobject B) (h : X <= Y) : Mono (ofLE X Y h) := by
  fconstructor
  intro Z f g w
  replace w := w =≫ Y.arrow
  ext
  simpa using w

/--
theorem `ofLE_mk_le_mk_of_comm` / 定理 `ofLE_mk_le_mk_of_comm`

English:
theorem ofLE_mk_le_mk_of_comm
  statement: {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂]
  proof: by
  ext
  simp [w]

中文:
定理 ofLE_mk_le_mk_of_comm
  结论: {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂]
  证明: by
  ext
  simp [w]
-/
theorem ofLE_mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂]
    (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁) :
    ofLE _ _ (mk_le_mk_of_comm g w) = (underlyingIso _).hom ≫ g ≫ (underlyingIso _).inv := by
  ext
  simp [w]

/--
Definition of `ofLEMk` / `ofLEMk` 的定义

English:
definition ofLEMk
  signature: {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X <= mk f)
  body: ofLE X (mk f) h ≫ (underlyingIso f).hom

中文:
定义 ofLEMk
  签名: {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X <= mk f)
  定义体: ofLE X (mk f) h ≫ (underlyingIso f).hom

Depends on / 依赖: underlyingIso
-/
def ofLEMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X <= mk f) : (X : C) ⟶ A :=
  ofLE X (mk f) h ≫ (underlyingIso f).hom

instance {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X <= mk f) :
    Mono (ofLEMk X f h) := by
  dsimp only [ofLEMk]
  infer_instance

@[simp]
/--
theorem `ofLEMk_comp` / 定理 `ofLEMk_comp`

English:
theorem ofLEMk_comp
  given: {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (h : X <= mk f)
  proof: by simp [ofLEMk]

中文:
定理 ofLEMk_comp
  条件: {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (h : X <= mk f)
  证明: by simp [ofLEMk]

Depends on / 依赖: ofLEMk
-/
theorem ofLEMk_comp {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (h : X <= mk f) :
    ofLEMk X f h ≫ f = X.arrow := by simp [ofLEMk]

/--
Definition of `ofMkLE` / `ofMkLE` 的定义

English:
definition ofMkLE
  signature: {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f <= X)
  body: (underlyingIso f).inv ≫ ofLE (mk f) X h

中文:
定义 ofMkLE
  签名: {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f <= X)
  定义体: (underlyingIso f).inv ≫ ofLE (mk f) X h

Depends on / 依赖: underlyingIso
-/
def ofMkLE {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f <= X) : A ⟶ (X : C) :=
  (underlyingIso f).inv ≫ ofLE (mk f) X h

instance {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f <= X) :
    Mono (ofMkLE f X h) := by
  dsimp only [ofMkLE]
  infer_instance

@[simp]
/--
theorem `ofMkLE_arrow` / 定理 `ofMkLE_arrow`

English:
theorem ofMkLE_arrow
  given: {B A : C} {f : A ⟶ B} [Mono f] {X : Subobject B} (h : mk f <= X)
  proof: by simp [ofMkLE]

中文:
定理 ofMkLE_arrow
  条件: {B A : C} {f : A ⟶ B} [Mono f] {X : Subobject B} (h : mk f <= X)
  证明: by simp [ofMkLE]

Depends on / 依赖: ofMkLE
-/
theorem ofMkLE_arrow {B A : C} {f : A ⟶ B} [Mono f] {X : Subobject B} (h : mk f <= X) :
    ofMkLE f X h ≫ X.arrow = f := by simp [ofMkLE]

/--
Definition of `ofMkLEMk` / `ofMkLEMk` 的定义

English:
definition ofMkLEMk
  signature: {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f <= mk g)
  body: (underlyingIso f).inv ≫ ofLE (mk f) (mk g) h ≫ (underlyingIso g).hom

中文:
定义 ofMkLEMk
  签名: {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f <= mk g)
  定义体: (underlyingIso f).inv ≫ ofLE (mk f) (mk g) h ≫ (underlyingIso g).hom

Depends on / 依赖: underlyingIso
-/
def ofMkLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f <= mk g) :
    A₁ ⟶ A₂ :=
  (underlyingIso f).inv ≫ ofLE (mk f) (mk g) h ≫ (underlyingIso g).hom

instance {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f <= mk g) :
    Mono (ofMkLEMk f g h) := by
  dsimp only [ofMkLEMk]
  infer_instance

@[simp]
/--
theorem `ofMkLEMk_comp` / 定理 `ofMkLEMk_comp`

English:
theorem ofMkLEMk_comp
  given: {B A₁ A₂ : C} {f : A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f <= mk g)
  proof: by simp [ofMkLEMk]

@[reassoc (attr := simp)]

中文:
定理 ofMkLEMk_comp
  条件: {B A₁ A₂ : C} {f : A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f <= mk g)
  证明: by simp [ofMkLEMk]

@[reassoc (attr := simp)]

Depends on / 依赖: ofMkLEMk
-/
theorem ofMkLEMk_comp {B A₁ A₂ : C} {f : A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f <= mk g) :
    ofMkLEMk f g h ≫ g = f := by simp [ofMkLEMk]

@[reassoc (attr := simp)]
/--
theorem `ofLE_comp_ofLE` / 定理 `ofLE_comp_ofLE`

English:
theorem ofLE_comp_ofLE
  given: {B : C} (X Y Z : Subobject B) (h₁ : X <= Y) (h₂ : Y <= Z)
  proof: by
  simp only [ofLE, ← Functor.map_comp underlying]
  congr 1

@[reassoc (attr := simp)]

中文:
定理 ofLE_comp_ofLE
  条件: {B : C} (X Y Z : Subobject B) (h₁ : X <= Y) (h₂ : Y <= Z)
  证明: by
  simp only [ofLE, ← Functor.map_comp underlying]
  congr 1

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_comp, map_comp, underlying
-/
theorem ofLE_comp_ofLE {B : C} (X Y Z : Subobject B) (h₁ : X <= Y) (h₂ : Y <= Z) :
    ofLE X Y h₁ ≫ ofLE Y Z h₂ = ofLE X Z (h₁.trans h₂) := by
  simp only [ofLE, ← Functor.map_comp underlying]
  congr 1

@[reassoc (attr := simp)]
/--
theorem `ofLE_comp_ofLEMk` / 定理 `ofLE_comp_ofLEMk`

English:
theorem ofLE_comp_ofLEMk
  statement: {B A : C} (X Y : Subobject B) (f : A ⟶ B) [Mono f] (h₁ : X <= Y)
  proof: by
  simp only [ofLEMk, ofLE, ← Functor.map_comp_assoc underlying]
  congr 1

@[reassoc (attr := simp)]

中文:
定理 ofLE_comp_ofLEMk
  结论: {B A : C} (X Y : Subobject B) (f : A ⟶ B) [Mono f] (h₁ : X <= Y)
  证明: by
  simp only [ofLEMk, ofLE, ← Functor.map_comp_assoc underlying]
  congr 1

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_comp_assoc, map_comp_assoc, ofLEMk, underlying
-/
theorem ofLE_comp_ofLEMk {B A : C} (X Y : Subobject B) (f : A ⟶ B) [Mono f] (h₁ : X <= Y)
    (h₂ : Y <= mk f) : ofLE X Y h₁ ≫ ofLEMk Y f h₂ = ofLEMk X f (h₁.trans h₂) := by
  simp only [ofLEMk, ofLE, ← Functor.map_comp_assoc underlying]
  congr 1

@[reassoc (attr := simp)]
/--
theorem `ofLEMk_comp_ofMkLE` / 定理 `ofLEMk_comp_ofMkLE`

English:
theorem ofLEMk_comp_ofMkLE
  statement: {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (Y : Subobject B)
  proof: by
  simp only [ofMkLE, ofLEMk, ofLE, ← Functor.map_comp underlying, assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]

中文:
定理 ofLEMk_comp_ofMkLE
  结论: {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (Y : Subobject B)
  证明: by
  simp only [ofMkLE, ofLEMk, ofLE, ← Functor.map_comp underlying, assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_comp, Iso.hom_inv_id_assoc, hom_inv_id_assoc, map_comp, ofLEMk, ofMkLE, underlying
-/
theorem ofLEMk_comp_ofMkLE {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (Y : Subobject B)
    (h₁ : X <= mk f) (h₂ : mk f <= Y) : ofLEMk X f h₁ ≫ ofMkLE f Y h₂ = ofLE X Y (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ← Functor.map_comp underlying, assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]
/--
theorem `ofLEMk_comp_ofMkLEMk` / 定理 `ofLEMk_comp_ofMkLEMk`

English:
theorem ofLEMk_comp_ofMkLEMk
  statement: {B A₁ A₂ : C} (X : Subobject B) (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B)
  proof: by
  simp only [ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]

中文:
定理 ofLEMk_comp_ofMkLEMk
  结论: {B A₁ A₂ : C} (X : Subobject B) (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B)
  证明: by
  simp only [ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_comp_assoc, Iso.hom_inv_id_assoc, hom_inv_id_assoc, map_comp_assoc, ofLEMk, ofMkLEMk, underlying
-/
theorem ofLEMk_comp_ofMkLEMk {B A₁ A₂ : C} (X : Subobject B) (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B)
    [Mono g] (h₁ : X <= mk f) (h₂ : mk f <= mk g) :
    ofLEMk X f h₁ ≫ ofMkLEMk f g h₂ = ofLEMk X g (h₁.trans h₂) := by
  simp only [ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]
/--
theorem `ofMkLE_comp_ofLE` / 定理 `ofMkLE_comp_ofLE`

English:
theorem ofMkLE_comp_ofLE
  statement: {B A₁ : C} (f : A₁ ⟶ B) [Mono f] (X Y : Subobject B) (h₁ : mk f <= X)
  proof: by
  simp only [ofMkLE, ofLE, ← Functor.map_comp underlying,
    assoc]
  congr 1

@[reassoc (attr := simp)]

中文:
定理 ofMkLE_comp_ofLE
  结论: {B A₁ : C} (f : A₁ ⟶ B) [Mono f] (X Y : Subobject B) (h₁ : mk f <= X)
  证明: by
  simp only [ofMkLE, ofLE, ← Functor.map_comp underlying,
    assoc]
  congr 1

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_comp, map_comp, ofMkLE, underlying
-/
theorem ofMkLE_comp_ofLE {B A₁ : C} (f : A₁ ⟶ B) [Mono f] (X Y : Subobject B) (h₁ : mk f <= X)
    (h₂ : X <= Y) : ofMkLE f X h₁ ≫ ofLE X Y h₂ = ofMkLE f Y (h₁.trans h₂) := by
  simp only [ofMkLE, ofLE, ← Functor.map_comp underlying,
    assoc]
  congr 1

@[reassoc (attr := simp)]
/--
theorem `ofMkLE_comp_ofLEMk` / 定理 `ofMkLE_comp_ofLEMk`

English:
theorem ofMkLE_comp_ofLEMk
  statement: {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (X : Subobject B) (g : A₂ ⟶ B)
  proof: by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc]
  congr 1

@[reassoc (attr := simp)]

中文:
定理 ofMkLE_comp_ofLEMk
  结论: {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (X : Subobject B) (g : A₂ ⟶ B)
  证明: by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc]
  congr 1

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_comp_assoc, map_comp_assoc, ofLEMk, ofMkLE, ofMkLEMk, underlying
-/
theorem ofMkLE_comp_ofLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (X : Subobject B) (g : A₂ ⟶ B)
    [Mono g] (h₁ : mk f <= X) (h₂ : X <= mk g) :
    ofMkLE f X h₁ ≫ ofLEMk X g h₂ = ofMkLEMk f g (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc]
  congr 1

@[reassoc (attr := simp)]
/--
theorem `ofMkLEMk_comp_ofMkLE` / 定理 `ofMkLEMk_comp_ofMkLE`

English:
theorem ofMkLEMk_comp_ofMkLE
  statement: {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
  proof: by
  simp only [ofMkLE, ofLE, ofMkLEMk, ← Functor.map_comp underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]

中文:
定理 ofMkLEMk_comp_ofMkLE
  结论: {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
  证明: by
  simp only [ofMkLE, ofLE, ofMkLEMk, ← Functor.map_comp underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_comp, Iso.hom_inv_id_assoc, hom_inv_id_assoc, map_comp, ofMkLE, ofMkLEMk, underlying
-/
theorem ofMkLEMk_comp_ofMkLE {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
    (X : Subobject B) (h₁ : mk f <= mk g) (h₂ : mk g <= X) :
    ofMkLEMk f g h₁ ≫ ofMkLE g X h₂ = ofMkLE f X (h₁.trans h₂) := by
  simp only [ofMkLE, ofLE, ofMkLEMk, ← Functor.map_comp underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]
/--
theorem `ofMkLEMk_comp_ofMkLEMk` / 定理 `ofMkLEMk_comp_ofMkLEMk`

English:
theorem ofMkLEMk_comp_ofMkLEMk
  statement: {B A₁ A₂ A₃ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
  proof: by
  simp only [ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc,
    Iso.hom_inv_id_assoc]
  congr 1

@[simp]

中文:
定理 ofMkLEMk_comp_ofMkLEMk
  结论: {B A₁ A₂ A₃ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
  证明: by
  simp only [ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc,
    Iso.hom_inv_id_assoc]
  congr 1

@[simp]

Depends on / 依赖: Functor, Functor.map_comp_assoc, Iso.hom_inv_id_assoc, hom_inv_id_assoc, map_comp_assoc, ofMkLEMk, underlying
-/
theorem ofMkLEMk_comp_ofMkLEMk {B A₁ A₂ A₃ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
    (h : A₃ ⟶ B) [Mono h] (h₁ : mk f <= mk g) (h₂ : mk g <= mk h) :
    ofMkLEMk f g h₁ ≫ ofMkLEMk g h h₂ = ofMkLEMk f h (h₁.trans h₂) := by
  simp only [ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc,
    Iso.hom_inv_id_assoc]
  congr 1

@[simp]
/--
theorem `ofLE_refl` / 定理 `ofLE_refl`

English:
theorem ofLE_refl
  given: {B : C} (X : Subobject B)
  statement: ofLE X X le_rfl = 𝟙 _
  proof: by
  apply (cancel_mono X.arrow).mp
  simp

@[simp]

中文:
定理 ofLE_refl
  条件: {B : C} (X : Subobject B)
  结论: ofLE X X le_rfl = 𝟙 _
  证明: by
  apply (cancel_mono X.arrow).mp
  simp

@[simp]

Depends on / 依赖: X.arrow, cancel_mono
-/
theorem ofLE_refl {B : C} (X : Subobject B) : ofLE X X le_rfl = 𝟙 _ := by
  apply (cancel_mono X.arrow).mp
  simp

@[simp]
/--
theorem `ofMkLEMk_refl` / 定理 `ofMkLEMk_refl`

English:
theorem ofMkLEMk_refl
  given: {B A₁ : C} (f : A₁ ⟶ B) [Mono f]
  statement: ofMkLEMk f f le_rfl = 𝟙 _
  proof: by
  apply (cancel_mono f).mp
  simp

中文:
定理 ofMkLEMk_refl
  条件: {B A₁ : C} (f : A₁ ⟶ B) [Mono f]
  结论: ofMkLEMk f f le_rfl = 𝟙 _
  证明: by
  apply (cancel_mono f).mp
  simp

Depends on / 依赖: cancel_mono
-/
theorem ofMkLEMk_refl {B A₁ : C} (f : A₁ ⟶ B) [Mono f] : ofMkLEMk f f le_rfl = 𝟙 _ := by
  apply (cancel_mono f).mp
  simp

-- As with `ofLE`, we have `X` and `Y` as explicit arguments for readability.
/-- An equality of subobjects gives an isomorphism of the corresponding objects.
(One could use `underlying.mapIso (eqToIso h))` here, but this is more readable.) -/
@[simps]
/--
Definition of `isoOfEq` / `isoOfEq` 的定义

English:
definition isoOfEq
  signature: {B : C} (X Y : Subobject B) (h : X = Y)
  body: ofLE _ _ h.le
  inv := ofLE _ _ h.ge

中文:
定义 isoOfEq
  签名: {B : C} (X Y : Subobject B) (h : X = Y)
  定义体: ofLE _ _ h.le
  inv := ofLE _ _ h.ge

Depends on / 依赖: h.le
-/
def isoOfEq {B : C} (X Y : Subobject B) (h : X = Y) : (X : C) ≅ (Y : C) where
  hom := ofLE _ _ h.le
  inv := ofLE _ _ h.ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
/--
Definition of `isoOfEqMk` / `isoOfEqMk` 的定义

English:
definition isoOfEqMk
  signature: {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X = mk f)
  body: ofLEMk X f h.le
  inv := ofMkLE f X h.ge

中文:
定义 isoOfEqMk
  签名: {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X = mk f)
  定义体: ofLEMk X f h.le
  inv := ofMkLE f X h.ge

Depends on / 依赖: h.le, ofLEMk
-/
def isoOfEqMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X = mk f) : (X : C) ≅ A where
  hom := ofLEMk X f h.le
  inv := ofMkLE f X h.ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
/--
Definition of `isoOfMkEq` / `isoOfMkEq` 的定义

English:
definition isoOfMkEq
  signature: {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f = X)
  body: ofMkLE f X h.le
  inv := ofLEMk X f h.ge

中文:
定义 isoOfMkEq
  签名: {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f = X)
  定义体: ofMkLE f X h.le
  inv := ofLEMk X f h.ge

Depends on / 依赖: h.le, ofMkLE
-/
def isoOfMkEq {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f = X) : A ≅ (X : C) where
  hom := ofMkLE f X h.le
  inv := ofLEMk X f h.ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
/--
Definition of `isoOfMkEqMk` / `isoOfMkEqMk` 的定义

English:
definition isoOfMkEqMk
  signature: {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f = mk g)
  body: ofMkLEMk f g h.le
  inv := ofMkLEMk g f h.ge

中文:
定义 isoOfMkEqMk
  签名: {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f = mk g)
  定义体: ofMkLEMk f g h.le
  inv := ofMkLEMk g f h.ge

Depends on / 依赖: h.le, ofMkLEMk
-/
def isoOfMkEqMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f = mk g) :
    A₁ ≅ A₂ where
  hom := ofMkLEMk f g h.le
  inv := ofMkLEMk g f h.ge

/--
lemma `mk_lt_mk_of_comm` / 引理 `mk_lt_mk_of_comm`

English:
lemma mk_lt_mk_of_comm
  statement: {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
  proof: by
  obtain _ | h := (mk_le_mk_of_comm _ fac).lt_or_eq
  · assumption
  · exfalso
    apply hf
    convert! (isoOfMkEqMk i₁ i₂ h).isIso_hom
    rw [← cancel_mono i₂]; rw [isoOfMkEqMk_hom]; rw [ofMkLEMk_comp]; rw [fac]

中文:
引理 mk_lt_mk_of_comm
  结论: {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
  证明: by
  obtain _ | h := (mk_le_mk_of_comm _ fac).lt_or_eq
  · assumption
  · exfalso
    apply hf
    convert! (isoOfMkEqMk i₁ i₂ h).isIso_hom
    rw [← cancel_mono i₂]; rw [isoOfMkEqMk_hom]; rw [ofMkLEMk_comp]; rw [fac]

Depends on / 依赖: cancel_mono, convert, isIso_hom, isoOfMkEqMk, isoOfMkEqMk_hom, lt_or_eq, mk_le_mk_of_comm, ofMkLEMk_comp
-/
lemma mk_lt_mk_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
    (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) (hf : ¬ IsIso f) :
    Subobject.mk i₁ < Subobject.mk i₂ := by
  obtain _ | h := (mk_le_mk_of_comm _ fac).lt_or_eq
  · assumption
  · exfalso
    apply hf
    convert! (isoOfMkEqMk i₁ i₂ h).isIso_hom
    rw [← cancel_mono i₂]; rw [isoOfMkEqMk_hom]; rw [ofMkLEMk_comp]; rw [fac]

/--
lemma `mk_lt_mk_iff_of_comm` / 引理 `mk_lt_mk_iff_of_comm`

English:
lemma mk_lt_mk_iff_of_comm
  statement: {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
  proof: ⟨fun h hf => by simp only [mk_eq_mk_of_comm i₁ i₂ (asIso f) fac, lt_self_iff_false] at h,
    mk_lt_mk_of_comm f fac⟩

中文:
引理 mk_lt_mk_iff_of_comm
  结论: {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
  证明: ⟨fun h hf => by simp only [mk_eq_mk_of_comm i₁ i₂ (asIso f) fac, lt_self_iff_false] at h,
    mk_lt_mk_of_comm f fac⟩

Depends on / 依赖: lt_self_iff_false, mk_eq_mk_of_comm, mk_lt_mk_of_comm
-/
lemma mk_lt_mk_iff_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
    (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) :
    Subobject.mk i₁ < Subobject.mk i₂ ↔ ¬ IsIso f :=
  ⟨fun h hf => by simp only [mk_eq_mk_of_comm i₁ i₂ (asIso f) fac, lt_self_iff_false] at h,
    mk_lt_mk_of_comm f fac⟩

end Subobject

namespace MonoOver

variable {P Q : MonoOver X} (f : P ⟶ Q)

include f in
/--
lemma `subobjectMk_le_mk_of_hom` / 引理 `subobjectMk_le_mk_of_hom`

English:
lemma subobjectMk_le_mk_of_hom
  proof: Subobject.mk_le_mk_of_comm f.hom.left (by simp)

中文:
引理 subobjectMk_le_mk_of_hom
  证明: Subobject.mk_le_mk_of_comm f.hom.left (by simp)

Depends on / 依赖: Subobject, Subobject.mk_le_mk_of_comm, f.hom.left, mk_le_mk_of_comm
-/
lemma subobjectMk_le_mk_of_hom :
    Subobject.mk P.obj.hom <= Subobject.mk Q.obj.hom :=
  Subobject.mk_le_mk_of_comm f.hom.left (by simp)

/--
lemma `isIso_hom_left_iff_subobjectMk_eq` / 引理 `isIso_hom_left_iff_subobjectMk_eq`

English:
lemma isIso_hom_left_iff_subobjectMk_eq
  proof: ⟨fun _ => Subobject.mk_eq_mk_of_comm _ _ (asIso f.hom.left) (by simp),
    fun h => ⟨Subobject.ofMkLEMk _ _ h.symm.le, by simp [← cancel_mono P.1.hom],
      by simp [← cancel_mono Q.1.hom]⟩⟩

中文:
引理 isIso_hom_left_iff_subobjectMk_eq
  证明: ⟨fun _ => Subobject.mk_eq_mk_of_comm _ _ (asIso f.hom.left) (by simp),
    fun h => ⟨Subobject.ofMkLEMk _ _ h.symm.le, by simp [← cancel_mono P.1.hom],
      by simp [← cancel_mono Q.1.hom]⟩⟩

Depends on / 依赖: Subobject, Subobject.mk_eq_mk_of_comm, Subobject.ofMkLEMk, cancel_mono, f.hom.left, h.symm.le, mk_eq_mk_of_comm, ofMkLEMk
-/
lemma isIso_hom_left_iff_subobjectMk_eq :
    IsIso f.hom.left ↔ Subobject.mk P.1.hom = Subobject.mk Q.1.hom :=
  ⟨fun _ => Subobject.mk_eq_mk_of_comm _ _ (asIso f.hom.left) (by simp),
    fun h => ⟨Subobject.ofMkLEMk _ _ h.symm.le, by simp [← cancel_mono P.1.hom],
      by simp [← cancel_mono Q.1.hom]⟩⟩

/--
lemma `isIso_iff_subobjectMk_eq` / 引理 `isIso_iff_subobjectMk_eq`

English:
lemma isIso_iff_subobjectMk_eq
  proof: by
  rw [isIso_iff_isIso_hom_left]; rw [isIso_hom_left_iff_subobjectMk_eq]

中文:
引理 isIso_iff_subobjectMk_eq
  证明: by
  rw [isIso_iff_isIso_hom_left]; rw [isIso_hom_left_iff_subobjectMk_eq]

Depends on / 依赖: isIso_hom_left_iff_subobjectMk_eq, isIso_iff_isIso_hom_left
-/
lemma isIso_iff_subobjectMk_eq :
    IsIso f ↔ Subobject.mk P.1.hom = Subobject.mk Q.1.hom := by
  rw [isIso_iff_isIso_hom_left]; rw [isIso_hom_left_iff_subobjectMk_eq]

end MonoOver

open CategoryTheory.Limits

namespace Subobject

/-- Any functor `MonoOver X ⥤ MonoOver Y` descends to a functor
`Subobject X ⥤ Subobject Y`, because `MonoOver Y` is thin. -/
@[implicit_reducible]
/--
Definition of `lower` / `lower` 的定义

English:
definition lower
  signature: {Y : D} (F : MonoOver X ⥤ MonoOver Y)
  body: ThinSkeleton.map F

中文:
定义 lower
  签名: {Y : D} (F : MonoOver X ⥤ MonoOver Y)
  定义体: ThinSkeleton.map F

Depends on / 依赖: ThinSkeleton, ThinSkeleton.map
-/
def lower {Y : D} (F : MonoOver X ⥤ MonoOver Y) : Subobject X ⥤ Subobject Y :=
  ThinSkeleton.map F

/--
theorem `lower_iso` / 定理 `lower_iso`

English:
theorem lower_iso
  given: (F₁ F₂ : MonoOver X ⥤ MonoOver Y) (h : F₁ ≅ F₂)
  statement: lower F₁ = lower F₂
  proof: ThinSkeleton.map_iso_eq h

中文:
定理 lower_iso
  条件: (F₁ F₂ : MonoOver X ⥤ MonoOver Y) (h : F₁ ≅ F₂)
  结论: lower F₁ = lower F₂
  证明: ThinSkeleton.map_iso_eq h

Depends on / 依赖: ThinSkeleton, ThinSkeleton.map_iso_eq, map_iso_eq
-/
theorem lower_iso (F₁ F₂ : MonoOver X ⥤ MonoOver Y) (h : F₁ ≅ F₂) : lower F₁ = lower F₂ :=
  ThinSkeleton.map_iso_eq h

/--
Definition of `lower₂` / `lower₂` 的定义

English:
definition lower₂
  signature: (F : MonoOver X ⥤ MonoOver Y ⥤ MonoOver Z)
  body: ThinSkeleton.map₂ F

@[simp]

中文:
定义 lower₂
  签名: (F : MonoOver X ⥤ MonoOver Y ⥤ MonoOver Z)
  定义体: ThinSkeleton.map₂ F

@[simp]

Depends on / 依赖: ThinSkeleton, ThinSkeleton.map
-/
def lower₂ (F : MonoOver X ⥤ MonoOver Y ⥤ MonoOver Z) : Subobject X ⥤ Subobject Y ⥤ Subobject Z :=
  ThinSkeleton.map₂ F

@[simp]
/--
theorem `lower_comm` / 定理 `lower_comm`

English:
theorem lower_comm
  given: (F : MonoOver Y ⥤ MonoOver X)
  proof: rfl

中文:
定理 lower_comm
  条件: (F : MonoOver Y ⥤ MonoOver X)
  证明: rfl
-/
theorem lower_comm (F : MonoOver Y ⥤ MonoOver X) :
    toThinSkeleton _ ⋙ lower F = F ⋙ toThinSkeleton _ :=
  rfl

/--
Definition of `lowerCompRepresentativeIso` / `lowerCompRepresentativeIso` 的定义

English:
definition lowerCompRepresentativeIso
  signature: (F : MonoOver Y ⥤ MonoOver X)
  body: ThinSkeleton.mapCompFromThinSkeletonIso _

中文:
定义 lowerCompRepresentativeIso
  签名: (F : MonoOver Y ⥤ MonoOver X)
  定义体: ThinSkeleton.mapCompFromThinSkeletonIso _

Depends on / 依赖: ThinSkeleton, ThinSkeleton.mapCompFromThinSkeletonIso, mapCompFromThinSkeletonIso
-/
def lowerCompRepresentativeIso (F : MonoOver Y ⥤ MonoOver X) :
    lower F ⋙ representative ≅ representative ⋙ F :=
  ThinSkeleton.mapCompFromThinSkeletonIso _

/--
Definition of `lowerAdjunction` / `lowerAdjunction` 的定义

English:
definition lowerAdjunction
  signature: {A : C} {B : D} {L : MonoOver A ⥤ MonoOver B} {R : MonoOver B ⥤ MonoOver A}
  body: ThinSkeleton.lowerAdjunction _ _ h

中文:
定义 lowerAdjunction
  签名: {A : C} {B : D} {L : MonoOver A ⥤ MonoOver B} {R : MonoOver B ⥤ MonoOver A}
  定义体: ThinSkeleton.lowerAdjunction _ _ h

Depends on / 依赖: ThinSkeleton, ThinSkeleton.lowerAdjunction, lowerAdjunction
-/
def lowerAdjunction {A : C} {B : D} {L : MonoOver A ⥤ MonoOver B} {R : MonoOver B ⥤ MonoOver A}
    (h : L ⊣ R) : lower L ⊣ lower R :=
  ThinSkeleton.lowerAdjunction _ _ h

set_option backward.isDefEq.respectTransparency.types false in
/-- An equivalence between `MonoOver A` and `MonoOver B` gives an equivalence
between `Subobject A` and `Subobject B`. -/
@[simps]
/--
Definition of `lowerEquivalence` / `lowerEquivalence` 的定义

English:
definition lowerEquivalence
  signature: {A : C} {B : D} (e : MonoOver A ≌ MonoOver B)
  body: lower e.functor
  inverse := lower e.inverse
  unitIso := by
    apply eqToIso
    convert! ThinSkeleton.map_iso_eq e.unitIso
    · exact ThinSkeleton.map_id_eq.symm
    · exact (ThinSkeleton.map_comp_eq _ _).symm
  counitIso := by
    apply eqToIso
    convert! ThinSkeleton.map_iso_eq e.counitIso
 

中文:
定义 lowerEquivalence
  签名: {A : C} {B : D} (e : MonoOver A ≌ MonoOver B)
  定义体: lower e.functor
  inverse := lower e.inverse
  unitIso := by
    apply eqToIso
    convert! ThinSkeleton.map_iso_eq e.unitIso
    · exact ThinSkeleton.map_id_eq.symm
    · exact (ThinSkeleton.map_comp_eq _ _).symm
  counitIso := by
    apply eqToIso
    convert! ThinSkeleton.map_iso_eq e.counitIso
 

Depends on / 依赖: e.functor, functor
-/
def lowerEquivalence {A : C} {B : D} (e : MonoOver A ≌ MonoOver B) : Subobject A ≌ Subobject B where
  functor := lower e.functor
  inverse := lower e.inverse
  unitIso := by
    apply eqToIso
    convert! ThinSkeleton.map_iso_eq e.unitIso
    · exact ThinSkeleton.map_id_eq.symm
    · exact (ThinSkeleton.map_comp_eq _ _).symm
  counitIso := by
    apply eqToIso
    convert! ThinSkeleton.map_iso_eq e.counitIso
    · exact (ThinSkeleton.map_comp_eq _ _).symm
    · exact ThinSkeleton.map_id_eq.symm

section Limits

variable {J : Type u₃} [Category.{v₃} J]

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [HasLimitsOfShape J (Over X)]
  body: by
  apply hasLimitsOfShape_thinSkeleton

中文:
实例 hasLimitsOfShape
  签名: [HasLimitsOfShape J (Over X)]
  定义体: by
  apply hasLimitsOfShape_thinSkeleton

Depends on / 依赖: hasLimitsOfShape_thinSkeleton
-/
instance hasLimitsOfShape [HasLimitsOfShape J (Over X)] :
    HasLimitsOfShape J (Subobject X) := by
  apply hasLimitsOfShape_thinSkeleton

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: [HasFiniteLimits (Over X)]
  body: by infer_instance

中文:
实例 hasFiniteLimits
  签名: [HasFiniteLimits (Over X)]
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance hasFiniteLimits [HasFiniteLimits (Over X)] : HasFiniteLimits (Subobject X) where
  out _ _ _ := by infer_instance

/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: [HasLimitsOfSize.{w, w'} (Over X)]
  body: by infer_instance

中文:
实例 hasLimitsOfSize
  签名: [HasLimitsOfSize.{w, w'} (Over X)]
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} (Over X)] :
    HasLimitsOfSize.{w, w'} (Subobject X) where
  has_limits_of_shape _ _ := by infer_instance

end Limits

section Colimits

variable [HasCoproducts C] [HasStrongEpiMonoFactorisations C]

/--
Instance `hasColimitsOfSize` / 实例 `hasColimitsOfSize`

English:
instance hasColimitsOfSize
  signature: : HasColimitsOfSize.{w, w'} (Subobject X)
  body: by
  apply hasColimitsOfSize_thinSkeleton

中文:
实例 hasColimitsOfSize
  签名: : HasColimitsOfSize.{w, w'} (Subobject X)
  定义体: by
  apply hasColimitsOfSize_thinSkeleton

Depends on / 依赖: hasColimitsOfSize_thinSkeleton
-/
instance hasColimitsOfSize : HasColimitsOfSize.{w, w'} (Subobject X) := by
  apply hasColimitsOfSize_thinSkeleton

end Colimits

section Pullback

variable [HasPullbacks C]

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: (f : X ⟶ Y)
  body: lower (MonoOver.pullback f)

中文:
定义 pullback
  签名: (f : X ⟶ Y)
  定义体: lower (MonoOver.pullback f)

Depends on / 依赖: MonoOver, MonoOver.pullback, pullback
-/
def pullback (f : X ⟶ Y) : Subobject Y ⥤ Subobject X :=
  lower (MonoOver.pullback f)

/--
theorem `pullback_id` / 定理 `pullback_id`

English:
theorem pullback_id
  given: (x : Subobject X)
  statement: (pullback (𝟙 X)).obj x = x
  proof: by
  induction x using Quotient.inductionOn' with | _ f
  exact Quotient.sound ⟨MonoOver.pullbackId.app f⟩

中文:
定理 pullback_id
  条件: (x : Subobject X)
  结论: (pullback (𝟙 X)).obj x = x
  证明: by
  induction x using Quotient.inductionOn' with | _ f
  exact Quotient.sound ⟨MonoOver.pullbackId.app f⟩

Depends on / 依赖: MonoOver, MonoOver.pullbackId.app, Quotient, Quotient.inductionOn, Quotient.sound, inductionOn, pullbackId
-/
theorem pullback_id (x : Subobject X) : (pullback (𝟙 X)).obj x = x := by
  induction x using Quotient.inductionOn' with | _ f
  exact Quotient.sound ⟨MonoOver.pullbackId.app f⟩

/--
theorem `pullback_comp` / 定理 `pullback_comp`

English:
theorem pullback_comp
  given: (f : X ⟶ Y) (g : Y ⟶ Z) (x : Subobject Z)
  proof: by
  induction x using Quotient.inductionOn' with | _ t
  exact Quotient.sound ⟨(MonoOver.pullbackComp _ _).app t⟩

中文:
定理 pullback_comp
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) (x : Subobject Z)
  证明: by
  induction x using Quotient.inductionOn' with | _ t
  exact Quotient.sound ⟨(MonoOver.pullbackComp _ _).app t⟩

Depends on / 依赖: MonoOver, MonoOver.pullbackComp, Quotient, Quotient.inductionOn, Quotient.sound, inductionOn, pullbackComp
-/
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : Subobject Z) :
    (pullback (f ≫ g)).obj x = (pullback f).obj ((pullback g).obj x) := by
  induction x using Quotient.inductionOn' with | _ t
  exact Quotient.sound ⟨(MonoOver.pullbackComp _ _).app t⟩

/--
theorem `pullback_obj_mk` / 定理 `pullback_obj_mk`

English:
theorem pullback_obj_mk
  statement: {A B X Y : C} {f : Y ⟶ X} {i : A ⟶ X} [Mono i]
  proof: ((equivMonoOver Y).inverse.mapIso
    (MonoOver.pullbackObjIsoOfIsPullback _ _ _ _ h)).to_eq

中文:
定理 pullback_obj_mk
  结论: {A B X Y : C} {f : Y ⟶ X} {i : A ⟶ X} [Mono i]
  证明: ((equivMonoOver Y).inverse.mapIso
    (MonoOver.pullbackObjIsoOfIsPullback _ _ _ _ h)).to_eq

Depends on / 依赖: MonoOver, MonoOver.pullbackObjIsoOfIsPullback, equivMonoOver, inverse, inverse.mapIso, mapIso, pullbackObjIsoOfIsPullback, to_eq
-/
theorem pullback_obj_mk {A B X Y : C} {f : Y ⟶ X} {i : A ⟶ X} [Mono i]
    {j : B ⟶ Y} [Mono j] {f' : B ⟶ A}
    (h : IsPullback f' j i f) :
    (pullback f).obj (mk i) = mk j :=
  ((equivMonoOver Y).inverse.mapIso
    (MonoOver.pullbackObjIsoOfIsPullback _ _ _ _ h)).to_eq

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullback_obj` / 定理 `pullback_obj`

English:
theorem pullback_obj
  given: {X Y : C} (f : Y ⟶ X) (x : Subobject X)
  proof: by
  obtain ⟨Z, i, _, rfl⟩ := mk_surjective x
  rw [pullback_obj_mk (IsPullback.of_hasPullback i f)]
  exact mk_eq_mk_of_comm _ _ (asIso (pullback.map i f (mk i).arrow f
    (underlyingIso i).inv (𝟙 _) (𝟙 _) (by simp) (by simp))) (by simp)

中文:
定理 pullback_obj
  条件: {X Y : C} (f : Y ⟶ X) (x : Subobject X)
  证明: by
  obtain ⟨Z, i, _, rfl⟩ := mk_surjective x
  rw [pullback_obj_mk (IsPullback.of_hasPullback i f)]
  exact mk_eq_mk_of_comm _ _ (asIso (pullback.map i f (mk i).arrow f
    (underlyingIso i).inv (𝟙 _) (𝟙 _) (by simp) (by simp))) (by simp)

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, mk_eq_mk_of_comm, mk_surjective, of_hasPullback, pullback, pullback.map, pullback_obj_mk, underlyingIso
-/
theorem pullback_obj {X Y : C} (f : Y ⟶ X) (x : Subobject X) :
    (pullback f).obj x = mk (pullback.snd x.arrow f) := by
  obtain ⟨Z, i, _, rfl⟩ := mk_surjective x
  rw [pullback_obj_mk (IsPullback.of_hasPullback i f)]
  exact mk_eq_mk_of_comm _ _ (asIso (pullback.map i f (mk i).arrow f
    (underlyingIso i).inv (𝟙 _) (𝟙 _) (by simp) (by simp))) (by simp)

instance (f : X ⟶ Y) : (pullback f).Faithful where

/--
lemma `isPullback_aux` / 引理 `isPullback_aux`

English:
lemma isPullback_aux
  given: (f : X ⟶ Y) (y : Subobject Y)
  proof: by
  obtain ⟨A, i, ⟨_, rfl⟩⟩ := mk_surjective y
  rw [pullback_obj]
  exists (underlyingIso (pullback.snd (mk i).arrow f)).hom ≫ pullback.fst (mk i).arrow f
  exact IsPullback.of_iso (IsPullback.of_hasPullback (mk i).arrow f)
        (underlyingIso (pullback.snd (mk i).arrow f)).symm (Iso.refl _) (I

中文:
引理 isPullback_aux
  条件: (f : X ⟶ Y) (y : Subobject Y)
  证明: by
  obtain ⟨A, i, ⟨_, rfl⟩⟩ := mk_surjective y
  rw [pullback_obj]
  exists (underlyingIso (pullback.snd (mk i).arrow f)).hom ≫ pullback.fst (mk i).arrow f
  exact IsPullback.of_iso (IsPullback.of_hasPullback (mk i).arrow f)
        (underlyingIso (pullback.snd (mk i).arrow f)).symm (Iso.refl _) (I

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, IsPullback.of_iso, Iso.refl, mk_surjective, of_hasPullback, of_iso, pullback, pullback.fst, pullback.snd, pullback_obj, underlyingIso
-/
lemma isPullback_aux (f : X ⟶ Y) (y : Subobject Y) :
    exists φ, IsPullback φ ((pullback f).obj y).arrow y.arrow f := by
  obtain ⟨A, i, ⟨_, rfl⟩⟩ := mk_surjective y
  rw [pullback_obj]
  exists (underlyingIso (pullback.snd (mk i).arrow f)).hom ≫ pullback.fst (mk i).arrow f
  exact IsPullback.of_iso (IsPullback.of_hasPullback (mk i).arrow f)
        (underlyingIso (pullback.snd (mk i).arrow f)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp)

/--
Definition of `pullbackπ` / `pullbackπ` 的定义

English:
definition pullbackπ
  signature: (f : X ⟶ Y) (y : Subobject Y)
  body: (isPullback_aux f y).choose

中文:
定义 pullbackπ
  签名: (f : X ⟶ Y) (y : Subobject Y)
  定义体: (isPullback_aux f y).choose

Depends on / 依赖: isPullback_aux
-/
noncomputable def pullbackπ (f : X ⟶ Y) (y : Subobject Y) :
    ((Subobject.pullback f).obj y : C) ⟶ (y : C) :=
  (isPullback_aux f y).choose

/--
theorem `isPullback` / 定理 `isPullback`

English:
theorem isPullback
  given: (f : X ⟶ Y) (y : Subobject Y)
  proof: (isPullback_aux f y).choose_spec

中文:
定理 isPullback
  条件: (f : X ⟶ Y) (y : Subobject Y)
  证明: (isPullback_aux f y).choose_spec

Depends on / 依赖: choose_spec, isPullback_aux
-/
theorem isPullback (f : X ⟶ Y) (y : Subobject Y) :
    IsPullback (pullbackπ f y) ((pullback f).obj y).arrow y.arrow f :=
  (isPullback_aux f y).choose_spec

end Pullback

section Map

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : X ⟶ Y) [Mono f]
  body: lower (MonoOver.map f)

中文:
定义 map
  签名: (f : X ⟶ Y) [Mono f]
  定义体: lower (MonoOver.map f)

Depends on / 依赖: MonoOver, MonoOver.map
-/
def map (f : X ⟶ Y) [Mono f] : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.map f)

/--
lemma `map_mk` / 引理 `map_mk`

English:
lemma map_mk
  given: {A X Y : C} (i : A ⟶ X) [Mono i] (f : X ⟶ Y) [Mono f]
  proof: rfl

中文:
引理 map_mk
  条件: {A X Y : C} (i : A ⟶ X) [Mono i] (f : X ⟶ Y) [Mono f]
  证明: rfl
-/
lemma map_mk {A X Y : C} (i : A ⟶ X) [Mono i] (f : X ⟶ Y) [Mono f] :
    (map f).obj (mk i) = mk (i ≫ f) :=
  rfl

/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (x : Subobject X)
  statement: (map (𝟙 X)).obj x = x
  proof: by
  induction x using Quotient.inductionOn' with | _ f
  exact Quotient.sound ⟨(MonoOver.mapId _).app f⟩

中文:
定理 map_id
  条件: (x : Subobject X)
  结论: (map (𝟙 X)).obj x = x
  证明: by
  induction x using Quotient.inductionOn' with | _ f
  exact Quotient.sound ⟨(MonoOver.mapId _).app f⟩

Depends on / 依赖: MonoOver, MonoOver.mapId, Quotient, Quotient.inductionOn, Quotient.sound, inductionOn
-/
theorem map_id (x : Subobject X) : (map (𝟙 X)).obj x = x := by
  induction x using Quotient.inductionOn' with | _ f
  exact Quotient.sound ⟨(MonoOver.mapId _).app f⟩

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] (x : Subobject X)
  proof: by
  induction x using Quotient.inductionOn' with | _ t
  exact Quotient.sound ⟨(MonoOver.mapComp _ _).app t⟩

中文:
定理 map_comp
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] (x : Subobject X)
  证明: by
  induction x using Quotient.inductionOn' with | _ t
  exact Quotient.sound ⟨(MonoOver.mapComp _ _).app t⟩

Depends on / 依赖: MonoOver, MonoOver.mapComp, Quotient, Quotient.inductionOn, Quotient.sound, inductionOn, mapComp
-/
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] (x : Subobject X) :
    (map (f ≫ g)).obj x = (map g).obj ((map f).obj x) := by
  induction x using Quotient.inductionOn' with | _ t
  exact Quotient.sound ⟨(MonoOver.mapComp _ _).app t⟩

/--
lemma `map_obj_injective` / 引理 `map_obj_injective`

English:
lemma map_obj_injective
  given: {X Y : C} (f : X ⟶ Y) [Mono f]
  proof: fun X₁ X₂ h => by
  induction X₁ using Subobject.ind
  induction X₂ using Subobject.ind
  simp only [map_mk] at h
  exact mk_eq_mk_of_comm _ _ (isoOfMkEqMk _ _ h) (by simp [← cancel_mono f])

中文:
引理 map_obj_injective
  条件: {X Y : C} (f : X ⟶ Y) [Mono f]
  证明: fun X₁ X₂ h => by
  induction X₁ using Subobject.ind
  induction X₂ using Subobject.ind
  simp only [map_mk] at h
  exact mk_eq_mk_of_comm _ _ (isoOfMkEqMk _ _ h) (by simp [← cancel_mono f])

Depends on / 依赖: Subobject, Subobject.ind, cancel_mono, isoOfMkEqMk, map_mk, mk_eq_mk_of_comm
-/
lemma map_obj_injective {X Y : C} (f : X ⟶ Y) [Mono f] :
    Function.Injective (Subobject.map f).obj := fun X₁ X₂ h => by
  induction X₁ using Subobject.ind
  induction X₂ using Subobject.ind
  simp only [map_mk] at h
  exact mk_eq_mk_of_comm _ _ (isoOfMkEqMk _ _ h) (by simp [← cancel_mono f])

/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: {A B : C} (e : A ≅ B)
  body: lowerEquivalence (MonoOver.mapIso e)

中文:
定义 mapIso
  签名: {A B : C} (e : A ≅ B)
  定义体: lowerEquivalence (MonoOver.mapIso e)

Depends on / 依赖: MonoOver, MonoOver.mapIso, lowerEquivalence, mapIso
-/
def mapIso {A B : C} (e : A ≅ B) : Subobject A ≌ Subobject B :=
  lowerEquivalence (MonoOver.mapIso e)

set_option backward.isDefEq.respectTransparency.types false in
/-- In fact, there's a type level bijection between the subobjects of isomorphic objects,
which preserves the order. -/
@[simps]
/--
Definition of `mapIsoToOrderIso` / `mapIsoToOrderIso` 的定义

English:
definition mapIsoToOrderIso
  signature: (e : X ≅ Y)
  body: (map e.hom).obj
  invFun := (map e.inv).obj
  left_inv g := by simp_rw [← map_comp, e.hom_inv_id, map_id]
  right_inv g := by simp_rw [← map_comp, e.inv_hom_id, map_id]
  map_rel_iff' {A B} := by
    dsimp
    constructor
    · intro h
      apply_fun (map e.inv).obj at h
      · simpa only [← map_c

中文:
定义 mapIsoToOrderIso
  签名: (e : X ≅ Y)
  定义体: (map e.hom).obj
  invFun := (map e.inv).obj
  left_inv g := by simp_rw [← map_comp, e.hom_inv_id, map_id]
  right_inv g := by simp_rw [← map_comp, e.inv_hom_id, map_id]
  map_rel_iff' {A B} := by
    dsimp
    constructor
    · intro h
      apply_fun (map e.inv).obj at h
      · simpa only [← map_c

Depends on / 依赖: e.hom
-/
def mapIsoToOrderIso (e : X ≅ Y) : Subobject X ≃o Subobject Y where
  toFun := (map e.hom).obj
  invFun := (map e.inv).obj
  left_inv g := by simp_rw [← map_comp, e.hom_inv_id, map_id]
  right_inv g := by simp_rw [← map_comp, e.inv_hom_id, map_id]
  map_rel_iff' {A B} := by
    dsimp
    constructor
    · intro h
      apply_fun (map e.inv).obj at h
      · simpa only [← map_comp, e.hom_inv_id, map_id] using h
      · apply Functor.monotone
    · intro h
      apply_fun (map e.hom).obj at h
      · exact h
      · apply Functor.monotone

/--
Definition of `mapPullbackAdj` / `mapPullbackAdj` 的定义

English:
definition mapPullbackAdj
  signature: [HasPullbacks C] (f : X ⟶ Y) [Mono f]
  body: lowerAdjunction (MonoOver.mapPullbackAdj f)

@[simp]

中文:
定义 mapPullbackAdj
  签名: [HasPullbacks C] (f : X ⟶ Y) [Mono f]
  定义体: lowerAdjunction (MonoOver.mapPullbackAdj f)

@[simp]

Depends on / 依赖: MonoOver, MonoOver.mapPullbackAdj, lowerAdjunction, mapPullbackAdj
-/
def mapPullbackAdj [HasPullbacks C] (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  lowerAdjunction (MonoOver.mapPullbackAdj f)

@[simp]
/--
theorem `pullback_map_self` / 定理 `pullback_map_self`

English:
theorem pullback_map_self
  given: [HasPullbacks C] (f : X ⟶ Y) [Mono f] (g : Subobject X)
  proof: by
  revert g
  exact Quotient.ind (fun g' => Quotient.sound ⟨(MonoOver.pullbackMapSelf f).app _⟩)

中文:
定理 pullback_map_self
  条件: [HasPullbacks C] (f : X ⟶ Y) [Mono f] (g : Subobject X)
  证明: by
  revert g
  exact Quotient.ind (fun g' => Quotient.sound ⟨(MonoOver.pullbackMapSelf f).app _⟩)

Depends on / 依赖: MonoOver, MonoOver.pullbackMapSelf, Quotient, Quotient.ind, Quotient.sound, pullbackMapSelf, revert
-/
theorem pullback_map_self [HasPullbacks C] (f : X ⟶ Y) [Mono f] (g : Subobject X) :
    (pullback f).obj ((map f).obj g) = g := by
  revert g
  exact Quotient.ind (fun g' => Quotient.sound ⟨(MonoOver.pullbackMapSelf f).app _⟩)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_pullback` / 定理 `map_pullback`

English:
theorem map_pullback
  statement: [HasPullbacks C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}
  proof: by
  revert p
  apply Quotient.ind'
  intro a
  apply Quotient.sound
  apply ThinSkeleton.equiv_of_both_ways
  · refine MonoOver.homMk (pullback.lift (pullback.fst _ _) _ ?_) (pullback.lift_snd _ _ _)
    simp [← comm, pullback.condition_assoc]
  · refine MonoOver.homMk (pullback.lift (pullback.fst 

中文:
定理 map_pullback
  结论: [HasPullbacks C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}
  证明: by
  revert p
  apply Quotient.ind'
  intro a
  apply Quotient.sound
  apply ThinSkeleton.equiv_of_both_ways
  · refine MonoOver.homMk (pullback.lift (pullback.fst _ _) _ ?_) (pullback.lift_snd _ _ _)
    simp [← comm, pullback.condition_assoc]
  · refine MonoOver.homMk (pullback.lift (pullback.fst 

Depends on / 依赖: IsLimit, MonoOver, MonoOver.homMk, PullbackCone, PullbackCone.IsLimit.lift, PullbackCone.IsLimit.lift_fst, Quotient, Quotient.ind, Quotient.sound, ThinSkeleton, ThinSkeleton.equiv_of_both_ways, a.arrow, condition, condition_assoc, equiv_of_both_ways, lift_fst, lift_snd, lift_snd_assoc, pullback, pullback.condition
-/
theorem map_pullback [HasPullbacks C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}
    [Mono h] [Mono g] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk f g comm))
    (p : Subobject Y) : (map g).obj ((pullback f).obj p) = (pullback k).obj ((map h).obj p) := by
  revert p
  apply Quotient.ind'
  intro a
  apply Quotient.sound
  apply ThinSkeleton.equiv_of_both_ways
  · refine MonoOver.homMk (pullback.lift (pullback.fst _ _) _ ?_) (pullback.lift_snd _ _ _)
    simp [← comm, pullback.condition_assoc]
  · refine MonoOver.homMk (pullback.lift (pullback.fst _ _)
      (PullbackCone.IsLimit.lift t (pullback.fst _ _ ≫ a.arrow) (pullback.snd _ _) _)
      (PullbackCone.IsLimit.lift_fst _ _ _ ?_).symm) ?_
    · rw [← pullback.condition, assoc]
      rfl
    · dsimp
      rw [pullback.lift_snd_assoc]
      apply PullbackCone.IsLimit.lift_snd

end Map

section Exists

variable [HasImages C]

/--
Definition of `«exists»` / `«exists»` 的定义

English:
definition «exists»
  signature: (f : X ⟶ Y)
  body: lower (MonoOver.exists f)

中文:
定义 «exists»
  签名: (f : X ⟶ Y)
  定义体: lower (MonoOver.exists f)
-/
def «exists» (f : X ⟶ Y) : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.exists f)

/--
theorem `exists_iso_map` / 定理 `exists_iso_map`

English:
theorem exists_iso_map
  given: (f : X ⟶ Y) [Mono f]
  statement: «exists» f = map f
  proof: lower_iso _ _ (MonoOver.existsIsoMap f)

中文:
定理 exists_iso_map
  条件: (f : X ⟶ Y) [Mono f]
  结论: «存在» f = map f
  证明: lower_iso _ _ (MonoOver.existsIsoMap f)

Depends on / 依赖: MonoOver, MonoOver.existsIsoMap, existsIsoMap, lower_iso
-/
theorem exists_iso_map (f : X ⟶ Y) [Mono f] : «exists» f = map f :=
  lower_iso _ _ (MonoOver.existsIsoMap f)

/--
Definition of `existsPullbackAdj` / `existsPullbackAdj` 的定义

English:
definition existsPullbackAdj
  signature: (f : X ⟶ Y) [HasPullbacks C]
  body: lowerAdjunction (MonoOver.existsPullbackAdj f)

中文:
定义 existsPullbackAdj
  签名: (f : X ⟶ Y) [HasPullbacks C]
  定义体: lowerAdjunction (MonoOver.existsPullbackAdj f)

Depends on / 依赖: MonoOver, MonoOver.existsPullbackAdj, existsPullbackAdj, lowerAdjunction
-/
def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : «exists» f ⊣ pullback f :=
  lowerAdjunction (MonoOver.existsPullbackAdj f)

/--
Definition of `existsCompRepresentativeIso` / `existsCompRepresentativeIso` 的定义

English:
definition existsCompRepresentativeIso
  signature: (f : X ⟶ Y)
  body: lowerCompRepresentativeIso _

中文:
定义 existsCompRepresentativeIso
  签名: (f : X ⟶ Y)
  定义体: lowerCompRepresentativeIso _

Depends on / 依赖: lowerCompRepresentativeIso
-/
def existsCompRepresentativeIso (f : X ⟶ Y) :
    «exists» f ⋙ representative ≅ representative ⋙ MonoOver.exists f :=
  lowerCompRepresentativeIso _

/--
Definition of `existsIsoImage` / `existsIsoImage` 的定义

English:
definition existsIsoImage
  signature: (f : X ⟶ Y) (x : Subobject X)
  body: (MonoOver.forget Y ⋙ Over.forget Y).mapIso (existsCompRepresentativeIso f).app x

#adaptation_note

中文:
定义 existsIsoImage
  签名: (f : X ⟶ Y) (x : Subobject X)
  定义体: (MonoOver.forget Y ⋙ Over.forget Y).mapIso (existsCompRepresentativeIso f).app x

#adaptation_note

Depends on / 依赖: MonoOver, MonoOver.forget, Over.forget, existsCompRepresentativeIso, forget, mapIso
-/
def existsIsoImage (f : X ⟶ Y) (x : Subobject X) :
    ((«exists» f).obj x : C) ≅ Limits.image (x.arrow ≫ f) :=
(MonoOver.forget Y ⋙ Over.forget Y).mapIso (existsCompRepresentativeIso f).app x

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given a subobject `x`, the `ImageFactorisation` of `x.arrow ≫ f` through `(exists f).obj x`. -/
@[simps! F_I F_m]
/--
Definition of `imageFactorisation` / `imageFactorisation` 的定义

English:
definition imageFactorisation
  signature: (f : X ⟶ Y) (x : Subobject X)
  body: let :=
    ImageFactorisation.ofIsoI
      (Image.imageFactorisation (x.arrow ≫ f))
      (existsIsoImage f x).symm
  ImageFactorisation.copy this ((«exists» f).obj x).arrow this.F.e (by
    simpa [this, -Over.w] using! (Over.w ((existsCompRepresentativeIso f).app x).hom.hom).symm)

中文:
定义 imageFactorisation
  签名: (f : X ⟶ Y) (x : Subobject X)
  定义体: let :=
    ImageFactorisation.ofIsoI
      (Image.imageFactorisation (x.arrow ≫ f))
      (existsIsoImage f x).symm
  ImageFactorisation.copy this ((«exists» f).obj x).arrow this.F.e (by
    simpa [this, -Over.w] using! (Over.w ((existsCompRepresentativeIso f).app x).hom.hom).symm)

Depends on / 依赖: Image.imageFactorisation, ImageFactorisation, ImageFactorisation.copy, ImageFactorisation.ofIsoI, Over.w, existsCompRepresentativeIso, existsIsoImage, hom.hom, imageFactorisation, ofIsoI, this.F.e, x.arrow
-/
def imageFactorisation (f : X ⟶ Y) (x : Subobject X) :
    ImageFactorisation (x.arrow ≫ f) :=
  let :=
    ImageFactorisation.ofIsoI
      (Image.imageFactorisation (x.arrow ≫ f))
      (existsIsoImage f x).symm
  ImageFactorisation.copy this ((«exists» f).obj x).arrow this.F.e (by
    simpa [this, -Over.w] using! (Over.w ((existsCompRepresentativeIso f).app x).hom.hom).symm)

end Exists

end Subobject

end CategoryTheory
