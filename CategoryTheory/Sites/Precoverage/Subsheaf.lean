/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# Sheafification of subpresheafs for precoverages

Let `K` be a precoverage. In this file we define the `K`-sheafification of a subpresheaf.
More generally, for a family of subsets `𝒮` of sections of a sheaf `F`, we construct
the smallest subsheaf of `F` containing `𝒮`.

## Main declarations

- `CategoryTheory.Precoverage.subsheafify`: `K`-sheafification of family of sets `𝒮` in a presheaf
  `F`. This is only a sheaf if `F` itself is a sheaf.
- `CategoryTheory.Precoverage.small_subsheafify_of_small`: If all the sets in the family `𝒮`
  are small, then the `K`-sheafification is again small.

## TODOs

- Relate `Precoverage.subsheafify K` with `Subfunctor.sheafify` for the Grothendieck topology
  `Precoverage.toGrothendieck K`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {K : Precoverage C}

namespace Precoverage

variable {F : Cᵒᵖ ⥤ Type w}

/--
Inductive type `SubsheafClosure` / 归纳类型 `SubsheafClosure`

English:
inductive SubsheafClosure
  parameters: (K : Precoverage C) {F : Cᵒᵖ ⥤ Type w}
  constructors (3):
    - base: {Z : C} {a : F.obj (.op Z)} : a in 𝒮 Z -> K.SubsheafClosure 𝒮 Z a
    - restrict: {Z W : C} (h : Z ⟶ W) {a : F.obj (.op W)} : K.SubsheafClosure 𝒮 W a -> K.SubsheafClosure 𝒮 Z (F.map h.op a)
    - amalgamate: {Z : C} {R : Presieve Z} (hR : R in K Z) {y : Presieve.FamilyOfElements F R} (hy : y.Compatible) (hmem : forall ⦃W : C⦄ (r : W ⟶ Z) (hr : R r), K.SubsheafClosure 𝒮 W (y r hr)) {t : F.obj (.op Z)} (ht : y.IsAmalgamation t) : K.SubsheafClosure 𝒮 Z t

中文:
归纳类型 子层闭包
  参数: (K : Precoverage C) {F : Cᵒᵖ ⥤ 类型 w}
  构造子 (3 个):
    - base: {Z : C} {a : F.obj (.op Z)} : a in 𝒮 Z -> K.子层闭包 𝒮 Z a
    - restrict: {Z W : C} (h : Z ⟶ W) {a : F.obj (.op W)} : K.子层闭包 𝒮 W a -> K.子层闭包 𝒮 Z (F.map h.op a)
    - amalgamate: {Z : C} {R : Presieve Z} (hR : R in K Z) {y : Presieve.FamilyOfElements F R} (hy : y.余mpatible) (hmem : 对任意 ⦃W : C⦄ (r : W ⟶ Z) (hr : R r), K.子层闭包 𝒮 W (y r hr)) {t : F.obj (.op Z)} (ht : y.IsAmalgamation t) : K.子层闭包 𝒮 Z t
-/
inductive SubsheafClosure (K : Precoverage C) {F : Cᵒᵖ ⥤ Type w}
    (𝒮 : forall Z : C, Set (F.obj (.op Z))) :
    forall Z : C, F.obj (.op Z) -> Prop where
  /-- Element of the initial family. -/
  | base {Z : C} {a : F.obj (.op Z)} : a in 𝒮 Z -> K.SubsheafClosure 𝒮 Z a
  /-- Restriction of an element in the closure along a morphism. -/
  | restrict {Z W : C} (h : Z ⟶ W) {a : F.obj (.op W)} :
      K.SubsheafClosure 𝒮 W a -> K.SubsheafClosure 𝒮 Z (F.map h.op a)
  /-- Gluing of sections in the closure. -/
  | amalgamate {Z : C} {R : Presieve Z} (hR : R in K Z)
      {y : Presieve.FamilyOfElements F R} (hy : y.Compatible)
      (hmem : forall ⦃W : C⦄ (r : W ⟶ Z) (hr : R r), K.SubsheafClosure 𝒮 W (y r hr))
      {t : F.obj (.op Z)} (ht : y.IsAmalgamation t) : K.SubsheafClosure 𝒮 Z t

variable (K) in
/-- The `K`-sheafification of a family of sets `𝒮` in `F`: If `F` is
a sheaf for `K`, this is the smallest subsheaf of `F` containing `𝒮`. -/
@[simps]
/--
Definition of `subsheafify` / `subsheafify` 的定义

English:
definition subsheafify
  signature: (𝒮 : forall Z : C, Set (F.obj (.op Z)))
  body: { x | K.SubsheafClosure 𝒮 U.unop x }
  map _ _ ht := .restrict _ ht

中文:
定义 subsheafify
  签名: (𝒮 : 对任意 Z : C, 集合 (F.obj (.op Z)))
  定义体: { x | K.SubsheafClosure 𝒮 U.unop x }
  map _ _ ht := .restrict _ ht

Depends on / 依赖: K.SubsheafClosure, SubsheafClosure, U.unop
-/
def subsheafify (𝒮 : forall Z : C, Set (F.obj (.op Z))) : Subfunctor F where
  obj U := { x | K.SubsheafClosure 𝒮 U.unop x }
  map _ _ ht := .restrict _ ht

variable (𝒮 : forall Z : C, Set (F.obj (.op Z)))

/--
lemma `isSheafFor_subsheafify` / 引理 `isSheafFor_subsheafify`

English:
lemma isSheafFor_subsheafify
  statement: (𝒮 : forall Z : C, Set (F.obj (.op Z))) {X : C} {R : Presieve X}
  proof: by
  let G := K.subsheafify 𝒮
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨.of_mono G.ι h'.isSeparatedFor, fun x hx => ?_⟩
  obtain ⟨t, ht, uniq⟩ := h' (x.map G.ι) (hx.map G.ι)
  exact ⟨⟨t, .amalgamate h (hx.map G.ι) (fun _ _ hr => (x _ hr).property) ht⟩, .of_m

中文:
引理 isSheafFor_subsheafify
  结论: (𝒮 : 对任意 Z : C, 集合 (F.obj (.op Z))) {X : C} {R : Presieve X}
  证明: by
  let G := K.subsheafify 𝒮
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨.of_mono G.ι h'.isSeparatedFor, fun x hx => ?_⟩
  obtain ⟨t, ht, uniq⟩ := h' (x.map G.ι) (hx.map G.ι)
  exact ⟨⟨t, .amalgamate h (hx.map G.ι) (fun _ _ hr => (x _ hr).property) ht⟩, .of_m

Depends on / 依赖: K.subsheafify, Presieve, Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor, amalgamate, hx.map, isSeparatedFor, isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor, of_mono, property, subsheafify, x.map
-/
lemma isSheafFor_subsheafify (𝒮 : forall Z : C, Set (F.obj (.op Z))) {X : C} {R : Presieve X}
    (h : R in K X) (h' : R.IsSheafFor F) :
    R.IsSheafFor (K.subsheafify 𝒮).toFunctor := by
  let G := K.subsheafify 𝒮
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨.of_mono G.ι h'.isSeparatedFor, fun x hx => ?_⟩
  obtain ⟨t, ht, uniq⟩ := h' (x.map G.ι) (hx.map G.ι)
  exact ⟨⟨t, .amalgamate h (hx.map G.ι) (fun _ _ hr => (x _ hr).property) ht⟩, .of_mono _ ht⟩

namespace SmallConstruction

variable (K) in
/--
Inductive type `Witness` / 归纳类型 `Witness`

English:
inductive Witness
  parameters: (ι : C -> Type w)
  constructors (3):
    - base: (X : C) : ι X -> Witness ι X
    - restrict: {X Y : C} (f : X ⟶ Y) : Witness ι Y -> Witness ι X
    - amalgamate: {X : C} {R : Presieve X} (hR : R in K X) (h : forall ⦃W⦄ (r : W ⟶ X), R r -> Witness ι W) : Witness ι X

中文:
归纳类型 Witness
  参数: (ι : C -> 类型 w)
  构造子 (3 个):
    - base: (X : C) : ι X -> Witness ι X
    - restrict: {X Y : C} (f : X ⟶ Y) : Witness ι Y -> Witness ι X
    - amalgamate: {X : C} {R : Presieve X} (hR : R in K X) (h : 对任意 ⦃W⦄ (r : W ⟶ X), R r -> Witness ι W) : Witness ι X
-/
private inductive Witness (ι : C -> Type w) : C -> Type max w u v where
  | base (X : C) : ι X -> Witness ι X
  | restrict {X Y : C} (f : X ⟶ Y) : Witness ι Y -> Witness ι X
  /-- Family of elements over a covering in `K`. Note that it is not necessarily compatible. -/
  | amalgamate {X : C} {R : Presieve X} (hR : R in K X)
      (h : forall ⦃W⦄ (r : W ⟶ X), R r -> Witness ι W) : Witness ι X

/-- Realization of a term of `Witness K ι X` as a section of `F` over `X`. By
construction, the sections will lie in the subsheaf `K.subsheafify 𝒮`.
This takes values in `Option`, because not every term constructed from
the `Witness.amalgamate` constructor corresponds to a compatible family. -/
private noncomputable
/--
Definition of `Witness.eval` / `Witness.eval` 的定义

English:
definition Witness.eval
  signature: (hF : forall ⦃X : C⦄ (R : Presieve X), R in K X -> Presieve.IsSheafFor F R)
  body: fun W (r : W ⟶ _) (hr : R r) => eval hF _ t (h r hr)
    /- If all elements of the family are evaluatable and the resulting family is compatible, take
    the glued section. Otherwise, return `none`. -/
    if hall : forall (W : C) (r : W ⟶ _) (hr : R r), (vals W r hr).isSome then
      let y : R.Fa

中文:
定义 Witness.eval
  签名: (hF : 对任意 ⦃X : C⦄ (R : Presieve X), R in K X -> Presieve.IsSheafFor F R)
  定义体: fun W (r : W ⟶ _) (hr : R r) => eval hF _ t (h r hr)
    /- If all elements of the family are evaluatable and the resulting family is compatible, take
    the glued section. Otherwise, return `none`. -/
    if hall : forall (W : C) (r : W ⟶ _) (hr : R r), (vals W r hr).isSome then
      let y : R.Fa
-/
def Witness.eval (hF : forall ⦃X : C⦄ (R : Presieve X), R in K X -> Presieve.IsSheafFor F R)
    (ι : C -> Type max u v) (t : forall X, ι X -> F.obj (.op X)) :
    {X : C} -> Witness K ι X -> Option (F.obj (.op X))
  | _, .base X i => t _ i
  | _, .restrict f i => do F.map f.op (← eval hF _ t i)
  | _, .amalgamate (R := R) hR h =>
    open scoped Classical in
    let vals := fun W (r : W ⟶ _) (hr : R r) => eval hF _ t (h r hr)
    /- If all elements of the family are evaluatable and the resulting family is compatible, take
    the glued section. Otherwise, return `none`. -/
    if hall : forall (W : C) (r : W ⟶ _) (hr : R r), (vals W r hr).isSome then
      let y : R.FamilyOfElements F := fun _ _ hr => (vals _ _ _).get (hall _ _ hr)
      if hy : y.Compatible then some (hF _ hR _ hy).choose else none
    else none

end SmallConstruction

open SmallConstruction in
/--
lemma `small_subsheafify_of_small` / 引理 `small_subsheafify_of_small`

English:
lemma small_subsheafify_of_small
  proof: by
  rintro ⟨X⟩
  let ι (X : C) := Shrink.{max u v} (𝒮 X)
  let t (X : C) (i : ι X) : F.obj (Opposite.op X) := ((equivShrink _).symm i).val
  have (x : F.obj (.op X)) (hx : K.SubsheafClosure 𝒮 X x) :
      exists (i : Witness K ι X), Witness.eval hF _ t i = x := by
    induction hx with
    | base h

中文:
引理 small_subsheafify_of_small
  证明: by
  rintro ⟨X⟩
  let ι (X : C) := Shrink.{max u v} (𝒮 X)
  let t (X : C) (i : ι X) : F.obj (Opposite.op X) := ((equivShrink _).symm i).val
  have (x : F.obj (.op X)) (hx : K.SubsheafClosure 𝒮 X x) :
      exists (i : Witness K ι X), Witness.eval hF _ t i = x := by
    induction hx with
    | base h

Depends on / 依赖: F.obj, K.SubsheafClosure, Opposite, Opposite.op, Shrink, SubsheafClosure, Witness, Witness.eval, amalgama, amalgamate, equivShrink, restrict
-/
lemma small_subsheafify_of_small
    (hF : forall ⦃X : C⦄ (R : Presieve X), R in K X -> Presieve.IsSheafFor F R)
    (𝒮 : forall Z : C, Set (F.obj (.op Z))) (h : forall Z, _root_.Small.{max u v} (𝒮 Z)) :
    FunctorToTypes.Small.{max u v} (K.subsheafify 𝒮).toFunctor := by
  rintro ⟨X⟩
  let ι (X : C) := Shrink.{max u v} (𝒮 X)
  let t (X : C) (i : ι X) : F.obj (Opposite.op X) := ((equivShrink _).symm i).val
  have (x : F.obj (.op X)) (hx : K.SubsheafClosure 𝒮 X x) :
      exists (i : Witness K ι X), Witness.eval hF _ t i = x := by
    induction hx with
    | base ha => exact ⟨.base _ (equivShrink _ ⟨_, ha⟩), by grind [Witness.eval]⟩
    | restrict f ha ih =>
      obtain ⟨i, hi⟩ := ih
      use .restrict f i
      grind [Witness.eval]
    | amalgamate hR hy hmem ht ih =>
      choose x hx using ih
      exact ⟨.amalgamate hR x, by simp [Witness.eval, hx]; grind⟩
  choose i hi using this
  have : Function.Injective (fun x : { x // K.SubsheafClosure 𝒮 X x } => i x x.prop) := by
    intro x y hxy
    ext
    apply Option.some_injective
    simp [← hi _ x.prop, ← hi _ y.prop, hxy]
  exact small_of_injective this

end Precoverage

end CategoryTheory
