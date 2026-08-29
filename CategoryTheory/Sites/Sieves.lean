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
/--
Definition of `Presieve` / `Presieve` 的定义

English:
definition Presieve
  signature: (X : C)
  body: forall ⦃Y⦄, (Y ⟶ X) -> Prop
deriving CompleteLattice, Inhabited

@[simp]

中文:
定义 Presieve
  签名: (X : C)
  定义体: forall ⦃Y⦄, (Y ⟶ X) -> Prop
deriving CompleteLattice, Inhabited

@[simp]
-/
def Presieve (X : C) :=
  forall ⦃Y⦄, (Y ⟶ X) -> Prop
deriving CompleteLattice, Inhabited

@[simp]
/--
lemma `top_apply` / 引理 `top_apply`

English:
lemma top_apply
  given: (f : Y ⟶ X)
  statement: (⊤ : Presieve X) f
  proof: trivial

@[simp]

中文:
引理 top_apply
  条件: (f : Y ⟶ X)
  结论: (⊤ : Presieve X) f
  证明: trivial

@[simp]
-/
lemma top_apply (f : Y ⟶ X) : (⊤ : Presieve X) f :=
  trivial

@[simp]
/--
lemma `bot_apply` / 引理 `bot_apply`

English:
lemma bot_apply
  given: (f : Y ⟶ X)
  statement: (⊥ : Presieve X) f ↔ False
  proof: .rfl

中文:
引理 bot_apply
  条件: (f : Y ⟶ X)
  结论: (⊥ : Presieve X) f ↔ 假
  证明: .rfl
-/
lemma bot_apply (f : Y ⟶ X) : (⊥ : Presieve X) f ↔ False :=
  .rfl

namespace Presieve

/--
Definition of `category` / `category` 的定义

English:
abbreviation category
  signature: {X : C} (P : Presieve X)
  body: ObjectProperty.FullSubcategory fun f : Over X => P f.hom

中文:
缩写 category
  签名: {X : C} (P : Presieve X)
  定义体: ObjectProperty.FullSubcategory fun f : Over X => P f.hom

Depends on / 依赖: FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory, f.hom
-/
abbrev category {X : C} (P : Presieve X) :=
  ObjectProperty.FullSubcategory fun f : Over X => P f.hom

/--
Definition of `categoryMk` / `categoryMk` 的定义

English:
abbreviation categoryMk
  signature: {X : C} (P : Presieve X) {Y : C} (f : Y ⟶ X) (hf : P f)
  body: ⟨Over.mk f, hf⟩

中文:
缩写 categoryMk
  签名: {X : C} (P : Presieve X) {Y : C} (f : Y ⟶ X) (hf : P f)
  定义体: ⟨Over.mk f, hf⟩

Depends on / 依赖: Over.mk
-/
abbrev categoryMk {X : C} (P : Presieve X) {Y : C} (f : Y ⟶ X) (hf : P f) : P.category :=
  ⟨Over.mk f, hf⟩

/--
Definition of `diagram` / `diagram` 的定义

English:
abbreviation diagram
  signature: (S : Presieve X)
  body: ObjectProperty.ι _ ⋙ Over.forget X

中文:
缩写 diagram
  签名: (S : Presieve X)
  定义体: ObjectProperty.ι _ ⋙ Over.forget X

Depends on / 依赖: ObjectProperty, Over.forget, forget
-/
abbrev diagram (S : Presieve X) : S.category ⥤ C :=
  ObjectProperty.ι _ ⋙ Over.forget X

/--
Definition of `cocone` / `cocone` 的定义

English:
abbreviation cocone
  signature: (S : Presieve X)
  body: (Over.forgetCocone X).whisker (ObjectProperty.ι _)

中文:
缩写 cocone
  签名: (S : Presieve X)
  定义体: (Over.forgetCocone X).whisker (ObjectProperty.ι _)

Depends on / 依赖: ObjectProperty, Over.forgetCocone, forgetCocone, whisker
-/
abbrev cocone (S : Presieve X) : Cocone S.diagram :=
  (Over.forgetCocone X).whisker (ObjectProperty.ι _)

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y)
  body: fun Z h =>
  exists (Y : C) (g : Z ⟶ Y) (f : Y ⟶ X) (H : S f), R H g ∧ g ≫ f = h

中文:
定义 bind
  签名: (S : Presieve X) (R : 对任意 ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y)
  定义体: fun Z h =>
  exists (Y : C) (g : Z ⟶ Y) (f : Y ⟶ X) (H : S f), R H g ∧ g ≫ f = h
-/
def bind (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y) : Presieve X := fun Z h =>
  exists (Y : C) (g : Z ⟶ Y) (f : Y ⟶ X) (H : S f), R H g ∧ g ≫ f = h

/--
Definition of `BindStruct` / `BindStruct` 的定义

English:
structure BindStruct
  parameters: (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y)
  axioms and operations (6):
    - Y : C
    - g : Z ⟶ Y
    - f : Y ⟶ X
    - hf : S f
    - hg : R hf g
    - fac : g ≫ f = h

中文:
结构 BindStruct
  参数: (S : Presieve X) (R : 对任意 ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y)
  公理与运算 (6 个):
    - Y : C
    - g : Z ⟶ Y
    - f : Y ⟶ X
    - hf : S f
    - hg : R hf g
    - fac : g ≫ f = h

Depends on / 依赖: BindStruct, BindStruct.fac
-/
structure BindStruct (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y)
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

/--
Definition of `bind.bindStruct` / `bind.bindStruct` 的定义

English:
definition bind.bindStruct
  signature: {S : Presieve X} {R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y}
  body: Nonempty.some (by
    obtain ⟨Y, g, f, hf, hg, fac⟩ := H
    exact ⟨{ hf := hf, hg := hg, fac := fac, .. }⟩)

中文:
定义 bind.bindStruct
  签名: {S : Presieve X} {R : 对任意 ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y}
  定义体: Nonempty.some (by
    obtain ⟨Y, g, f, hf, hg, fac⟩ := H
    exact ⟨{ hf := hf, hg := hg, fac := fac, .. }⟩)

Depends on / 依赖: Nonempty, Nonempty.some
-/
noncomputable def bind.bindStruct {S : Presieve X} {R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y}
    {Z : C} {h : Z ⟶ X} (H : bind S R h) : BindStruct S R h :=
  Nonempty.some (by
    obtain ⟨Y, g, f, hf, hg, fac⟩ := H
    exact ⟨{ hf := hf, hg := hg, fac := fac, .. }⟩)

/--
lemma `BindStruct.bind` / 引理 `BindStruct.bind`

English:
lemma BindStruct.bind
  statement: {S : Presieve X} {R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y}
  proof: ⟨b.Y, b.g, b.f, b.hf, b.hg, b.fac⟩

@[simp]

中文:
引理 BindStruct.bind
  结论: {S : Presieve X} {R : 对任意 ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y}
  证明: ⟨b.Y, b.g, b.f, b.hf, b.hg, b.fac⟩

@[simp]

Depends on / 依赖: b.fac, b.hf, b.hg
-/
lemma BindStruct.bind {S : Presieve X} {R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y}
    {Z : C} {h : Z ⟶ X} (b : BindStruct S R h) : bind S R h :=
  ⟨b.Y, b.g, b.f, b.hf, b.hg, b.fac⟩

@[simp]
/--
theorem `bind_comp` / 定理 `bind_comp`

English:
theorem bind_comp
  statement: {S : Presieve X} {R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y} {g : Z ⟶ Y}
  proof: ⟨_, _, _, h₁, h₂, rfl⟩

中文:
定理 bind_comp
  结论: {S : Presieve X} {R : 对任意 ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y} {g : Z ⟶ Y}
  证明: ⟨_, _, _, h₁, h₂, rfl⟩
-/
theorem bind_comp {S : Presieve X} {R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Presieve Y} {g : Z ⟶ Y}
    (h₁ : S f) (h₂ : R h₁ g) : bind S R (g ≫ f) :=
  ⟨_, _, _, h₁, h₂, rfl⟩

-- Note we can't make this into `HasSingleton` because of the out-param.
/--
Inductive type `singleton` / 归纳类型 `singleton`

English:
inductive singleton
  parameters: : Presieve X
  constructors (1):
    - mk: singleton f

中文:
归纳类型 singleton
  参数: : Presieve X
  构造子 (1 个):
    - mk: singleton f
-/
inductive singleton : Presieve X
  | mk : singleton f

@[simp]
/--
theorem `singleton_eq_iff_domain` / 定理 `singleton_eq_iff_domain`

English:
theorem singleton_eq_iff_domain
  given: (f g : Y ⟶ X)
  statement: singleton f g ↔ f = g
  proof: by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · rintro rfl
    apply singleton.mk

中文:
定理 singleton_eq_iff_domain
  条件: (f g : Y ⟶ X)
  结论: singleton f g ↔ f = g
  证明: by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · rintro rfl
    apply singleton.mk

Depends on / 依赖: singleton, singleton.mk
-/
theorem singleton_eq_iff_domain (f g : Y ⟶ X) : singleton f g ↔ f = g := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · rintro rfl
    apply singleton.mk

/--
theorem `singleton_self` / 定理 `singleton_self`

English:
theorem singleton_self
  statement: singleton f f
  proof: singleton.mk

中文:
定理 singleton_self
  结论: singleton f f
  证明: singleton.mk

Depends on / 依赖: singleton, singleton.mk
-/
theorem singleton_self : singleton f f :=
  singleton.mk

/--
Definition of `HasPullbacks` / `HasPullbacks` 的定义

English:
class HasPullbacks
  parameters: (R : Presieve X) {Y : C} (f : Y ⟶ X)
  axioms and operations (1):
    - hasPullback((f) {Z : C} {h : Z ⟶ X}) : R h -> Limits.HasPullback h f

中文:
类 有Pullbacks
  参数: (R : Presieve X) {Y : C} (f : Y ⟶ X)
  公理与运算 (1 个):
    - hasPullback((f) {Z : C} {h : Z ⟶ X}) : R h -> Limits.HasPullback h f
-/
protected class HasPullbacks (R : Presieve X) {Y : C} (f : Y ⟶ X) : Prop where
  hasPullback (f) {Z : C} {h : Z ⟶ X} : R h -> Limits.HasPullback h f

protected alias hasPullback := HasPullbacks.hasPullback

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPullbacks
  signature: C] (R
  body: inferInstance

中文:
实例 [有Pullbacks
  签名: C] (R
  定义体: inferInstance
-/
instance [HasPullbacks C] (R : Presieve X) {Y : C} (f : Y ⟶ X) : R.HasPullbacks f where
  hasPullback _ := inferInstance

instance (g : Z ⟶ X) [HasPullback g f] : (singleton g).HasPullbacks f where
  hasPullback {Z} h := by
    intro ⟨⟩
    infer_instance

/--
Inductive type `pullbackArrows` / 归纳类型 `pullbackArrows`

English:
inductive pullbackArrows
  parameters: (R : Presieve X) [R.HasPullbacks f]
  constructors (1):
    - mk: (Z : C) (h : Z ⟶ X) (hRh : R h) : haveI := R.hasPullback f hRh pullbackArrows _ (pullback.snd h f)

中文:
归纳类型 pullbackArrows
  参数: (R : Presieve X) [R.有Pullbacks f]
  构造子 (1 个):
    - mk: (Z : C) (h : Z ⟶ X) (hRh : R h) : haveI := R.hasPullback f hRh pullbackArrows _ (pullback.snd h f)

Depends on / 依赖: R.hasPullback, hasPullback
-/
inductive pullbackArrows (R : Presieve X) [R.HasPullbacks f] : Presieve Y
  | mk (Z : C) (h : Z ⟶ X) (hRh : R h) :
    haveI := R.hasPullback f hRh
    pullbackArrows _ (pullback.snd h f)

/--
theorem `pullback_singleton` / 定理 `pullback_singleton`

English:
theorem pullback_singleton
  given: (g : Z ⟶ X) [HasPullback g f]
  proof: by
  funext W
  ext h
  constructor
  · rintro ⟨W, _, _, _⟩
    exact singleton.mk
  · rintro ⟨_⟩
    exact pullbackArrows.mk Z g singleton.mk

中文:
定理 pullback_singleton
  条件: (g : Z ⟶ X) [HasPullback g f]
  证明: by
  funext W
  ext h
  constructor
  · rintro ⟨W, _, _, _⟩
    exact singleton.mk
  · rintro ⟨_⟩
    exact pullbackArrows.mk Z g singleton.mk

Depends on / 依赖: pullbackArrows, pullbackArrows.mk, singleton, singleton.mk
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

/--
Inductive type `ofArrows` / 归纳类型 `ofArrows`

English:
inductive ofArrows
  parameters: {ι : Type*} (Y : ι -> C) (f : forall i, Y i ⟶ X)
  constructors (1):
    - mk: (i : ι) : ofArrows _ _ (f i)

中文:
归纳类型 ofArrows
  参数: {ι : 类型} (Y : ι -> C) (f : 对任意 i, Y i ⟶ X)
  构造子 (1 个):
    - mk: (i : ι) : ofArrows _ _ (f i)
-/
inductive ofArrows {ι : Type*} (Y : ι -> C) (f : forall i, Y i ⟶ X) : Presieve X
  | mk (i : ι) : ofArrows _ _ (f i)

/--
lemma `ofArrows.mk'` / 引理 `ofArrows.mk'`

English:
lemma ofArrows.mk'
  statement: {ι : Type*} {Y : ι -> C} {f : forall i, Y i ⟶ X} {Z : C} {g : Z ⟶ X}
  proof: by
  subst h
  simp only [eqToHom_refl, id_comp] at hg
  subst hg
  constructor

中文:
引理 ofArrows.mk'
  结论: {ι : 类型} {Y : ι -> C} {f : 对任意 i, Y i ⟶ X} {Z : C} {g : Z ⟶ X}
  证明: by
  subst h
  simp only [eqToHom_refl, id_comp] at hg
  subst hg
  constructor

Depends on / 依赖: eqToHom_refl, id_comp
-/
lemma ofArrows.mk' {ι : Type*} {Y : ι -> C} {f : forall i, Y i ⟶ X} {Z : C} {g : Z ⟶ X}
    (i : ι) (h : Z = Y i) (hg : g = eqToHom h ≫ f i) :
    ofArrows Y f g := by
  subst h
  simp only [eqToHom_refl, id_comp] at hg
  subst hg
  constructor

instance {ι : Type*} (Z : ι -> C) (g : forall i : ι, Z i ⟶ X)
    [forall i, HasPullback (g i) f] : (ofArrows Z g).HasPullbacks f where
  hasPullback {_} _ := fun ⟨i⟩ => inferInstance

/--
theorem `ofArrows_pullback` / 定理 `ofArrows_pullback`

English:
theorem ofArrows_pullback
  statement: {ι : Type*} (Z : ι -> C) (g : forall i : ι, Z i ⟶ X)
  proof: by
  funext T
  ext h
  constructor
  · rintro ⟨hk⟩
    exact pullbackArrows.mk _ _ (ofArrows.mk hk)
  · rintro ⟨W, k, ⟨_⟩⟩
    apply ofArrows.mk

中文:
定理 ofArrows_pullback
  结论: {ι : 类型} (Z : ι -> C) (g : 对任意 i : ι, Z i ⟶ X)
  证明: by
  funext T
  ext h
  constructor
  · rintro ⟨hk⟩
    exact pullbackArrows.mk _ _ (ofArrows.mk hk)
  · rintro ⟨W, k, ⟨_⟩⟩
    apply ofArrows.mk

Depends on / 依赖: ofArrows, ofArrows.mk, pullbackArrows, pullbackArrows.mk
-/
theorem ofArrows_pullback {ι : Type*} (Z : ι -> C) (g : forall i : ι, Z i ⟶ X)
    [forall i, HasPullback (g i) f] :
    (ofArrows (fun i => pullback (g i) f) fun _ => pullback.snd _ _) =
      pullbackArrows f (ofArrows Z g) := by
  funext T
  ext h
  constructor
  · rintro ⟨hk⟩
    exact pullbackArrows.mk _ _ (ofArrows.mk hk)
  · rintro ⟨W, k, ⟨_⟩⟩
    apply ofArrows.mk

/--
theorem `ofArrows_bind` / 定理 `ofArrows_bind`

English:
theorem ofArrows_bind
  statement: {ι : Type*} (Z : ι -> C) (g : forall i : ι, Z i ⟶ X)
  proof: by
  funext Y
  ext f
  constructor
  · rintro ⟨_, _, _, ⟨i⟩, ⟨i'⟩, rfl⟩
    exact ofArrows.mk (Sigma.mk _ _)
  · rintro ⟨i⟩
    exact bind_comp _ (ofArrows.mk _) (ofArrows.mk _)

中文:
定理 ofArrows_bind
  结论: {ι : 类型} (Z : ι -> C) (g : 对任意 i : ι, Z i ⟶ X)
  证明: by
  funext Y
  ext f
  constructor
  · rintro ⟨_, _, _, ⟨i⟩, ⟨i'⟩, rfl⟩
    exact ofArrows.mk (Sigma.mk _ _)
  · rintro ⟨i⟩
    exact bind_comp _ (ofArrows.mk _) (ofArrows.mk _)

Depends on / 依赖: Sigma.mk, bind_comp, ofArrows, ofArrows.mk
-/
theorem ofArrows_bind {ι : Type*} (Z : ι -> C) (g : forall i : ι, Z i ⟶ X)
    (j : forall ⦃Y⦄ (f : Y ⟶ X), ofArrows Z g f -> Type*) (W : forall ⦃Y⦄ (f : Y ⟶ X) (H), j f H -> C)
    (k : forall ⦃Y⦄ (f : Y ⟶ X) (H i), W f H i ⟶ Y) :
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

/--
theorem `ofArrows_surj` / 定理 `ofArrows_surj`

English:
theorem ofArrows_surj
  statement: {ι : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X) {Z : C} (g : Z ⟶ X)
  proof: by
  obtain ⟨i⟩ := hg
  exact ⟨i, rfl, by simp only [eqToHom_refl, id_comp]⟩

中文:
定理 ofArrows_surj
  结论: {ι : 类型} {Y : ι -> C} (f : 对任意 i, Y i ⟶ X) {Z : C} (g : Z ⟶ X)
  证明: by
  obtain ⟨i⟩ := hg
  exact ⟨i, rfl, by simp only [eqToHom_refl, id_comp]⟩

Depends on / 依赖: eqToHom_refl, id_comp
-/
theorem ofArrows_surj {ι : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X) {Z : C} (g : Z ⟶ X)
    (hg : ofArrows Y f g) : exists (i : ι) (h : Y i = Z),
    g = eqToHom h.symm ≫ f i := by
  obtain ⟨i⟩ := hg
  exact ⟨i, rfl, by simp only [eqToHom_refl, id_comp]⟩

/--
lemma `exists_eq_ofArrows` / 引理 `exists_eq_ofArrows`

English:
lemma exists_eq_ofArrows
  given: (R : Presieve X)
  proof: by
  let ι := { x : Σ Z, (Z ⟶ X) // R x.2 }
  use ι, fun x => x.1.1, fun x => x.1.2
  exact le_antisymm (fun Z g hg => .mk (⟨⟨_, _⟩, hg⟩ : ι)) fun Z g ⟨x⟩ => x.2

中文:
引理 存在_eq_ofArrows
  条件: (R : Presieve X)
  证明: by
  let ι := { x : Σ Z, (Z ⟶ X) // R x.2 }
  use ι, fun x => x.1.1, fun x => x.1.2
  exact le_antisymm (fun Z g hg => .mk (⟨⟨_, _⟩, hg⟩ : ι)) fun Z g ⟨x⟩ => x.2

Depends on / 依赖: le_antisymm
-/
lemma exists_eq_ofArrows (R : Presieve X) :
    exists (ι : Type (max u₁ v₁)) (Y : ι -> C) (f : forall i, Y i ⟶ X), R = .ofArrows Y f := by
  let ι := { x : Σ Z, (Z ⟶ X) // R x.2 }
  use ι, fun x => x.1.1, fun x => x.1.2
  exact le_antisymm (fun Z g hg => .mk (⟨⟨_, _⟩, hg⟩ : ι)) fun Z g ⟨x⟩ => x.2

/--
lemma `ofArrows_category` / 引理 `ofArrows_category`

English:
lemma ofArrows_category
  given: {S : C} (R : Presieve S)
  proof: by
  refine le_antisymm ?_ ?_
  · rintro _ _ ⟨X, h⟩
    exact h
  · rintro X g hg
    exact .mk (ι := R.category) ⟨Over.mk g, hg⟩

中文:
引理 ofArrows_category
  条件: {S : C} (R : Presieve S)
  证明: by
  refine le_antisymm ?_ ?_
  · rintro _ _ ⟨X, h⟩
    exact h
  · rintro X g hg
    exact .mk (ι := R.category) ⟨Over.mk g, hg⟩

Depends on / 依赖: Over.mk, R.category, category, le_antisymm
-/
lemma ofArrows_category {S : C} (R : Presieve S) :
    Presieve.ofArrows _ (fun (f : R.category) => f.obj.hom) = R := by
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
/--
Definition of `ofArrows.idx` / `ofArrows.idx` 的定义

English:
definition ofArrows.idx
  signature: {ι : Type*} {S : C} {X : ι -> C} {f : forall i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
  body: (ofArrows_surj _ _ hf).choose

中文:
定义 ofArrows.idx
  签名: {ι : 类型} {S : C} {X : ι -> C} {f : 对任意 i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
  定义体: (ofArrows_surj _ _ hf).choose

Depends on / 依赖: ofArrows_surj
-/
def ofArrows.idx {ι : Type*} {S : C} {X : ι -> C} {f : forall i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
    (hf : Presieve.ofArrows X f g) : ι :=
  (ofArrows_surj _ _ hf).choose

/--
lemma `ofArrows.obj_idx` / 引理 `ofArrows.obj_idx`

English:
lemma ofArrows.obj_idx
  statement: {ι : Type*} {S : C} {X : ι -> C} {f : forall i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
  proof: (ofArrows_surj _ _ hf).choose_spec.1

中文:
引理 ofArrows.obj_idx
  结论: {ι : 类型} {S : C} {X : ι -> C} {f : 对任意 i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
  证明: (ofArrows_surj _ _ hf).choose_spec.1

Depends on / 依赖: choose_spec, ofArrows_surj
-/
lemma ofArrows.obj_idx {ι : Type*} {S : C} {X : ι -> C} {f : forall i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
    (hf : ofArrows X f g) : X hf.idx = Y :=
  (ofArrows_surj _ _ hf).choose_spec.1

/--
lemma `ofArrows.eq_eqToHom_comp_hom_idx` / 引理 `ofArrows.eq_eqToHom_comp_hom_idx`

English:
lemma ofArrows.eq_eqToHom_comp_hom_idx
  statement: {ι : Type*} {S : C} {X : ι -> C} {f : forall i, X i ⟶ S} {Y : C}
  proof: (Presieve.ofArrows_surj _ _ hf).choose_spec.2

中文:
引理 ofArrows.eq_eqToHom_comp_hom_idx
  结论: {ι : 类型} {S : C} {X : ι -> C} {f : 对任意 i, X i ⟶ S} {Y : C}
  证明: (Presieve.ofArrows_surj _ _ hf).choose_spec.2

Depends on / 依赖: Presieve, Presieve.ofArrows_surj, choose_spec, ofArrows_surj
-/
lemma ofArrows.eq_eqToHom_comp_hom_idx {ι : Type*} {S : C} {X : ι -> C} {f : forall i, X i ⟶ S} {Y : C}
    {g : Y ⟶ S} (hf : ofArrows X f g) : g = eqToHom hf.obj_idx.symm ≫ f hf.idx :=
  (Presieve.ofArrows_surj _ _ hf).choose_spec.2

/--
lemma `ofArrows.hom_idx` / 引理 `ofArrows.hom_idx`

English:
lemma ofArrows.hom_idx
  statement: {ι : Type*} {S : C} {X : ι -> C} {f : forall i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
  proof: by
  simp [eq_eqToHom_comp_hom_idx hf]

中文:
引理 ofArrows.hom_idx
  结论: {ι : 类型} {S : C} {X : ι -> C} {f : 对任意 i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
  证明: by
  simp [eq_eqToHom_comp_hom_idx hf]

Depends on / 依赖: eq_eqToHom_comp_hom_idx
-/
lemma ofArrows.hom_idx {ι : Type*} {S : C} {X : ι -> C} {f : forall i, X i ⟶ S} {Y : C} {g : Y ⟶ S}
    (hf : ofArrows X f g) : f hf.idx = eqToHom hf.obj_idx ≫ g := by
  simp [eq_eqToHom_comp_hom_idx hf]

/--
lemma `ofArrows_comp_le` / 引理 `ofArrows_comp_le`

English:
lemma ofArrows_comp_le
  given: {X : C} {ι σ : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X) (a : σ -> ι)
  proof: by
  rintro - - ⟨i⟩
  use a i

中文:
引理 ofArrows_comp_le
  条件: {X : C} {ι σ : 类型} {Y : ι -> C} (f : 对任意 i, Y i ⟶ X) (a : σ -> ι)
  证明: by
  rintro - - ⟨i⟩
  use a i
-/
lemma ofArrows_comp_le {X : C} {ι σ : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X) (a : σ -> ι) :
    ofArrows (Y ∘ a) (fun i => f (a i)) <= ofArrows Y f := by
  rintro - - ⟨i⟩
  use a i

/--
lemma `ofArrows_comp_eq_of_surjective` / 引理 `ofArrows_comp_eq_of_surjective`

English:
lemma ofArrows_comp_eq_of_surjective
  statement: {X : C} {ι σ : Type*} {Y : ι -> C}
  proof: by
  refine le_antisymm (ofArrows_comp_le f a) ?_
  rintro - - ⟨i⟩
  obtain ⟨j, rfl⟩ := ha i
  use j

中文:
引理 ofArrows_comp_eq_of_surjective
  结论: {X : C} {ι σ : 类型} {Y : ι -> C}
  证明: by
  refine le_antisymm (ofArrows_comp_le f a) ?_
  rintro - - ⟨i⟩
  obtain ⟨j, rfl⟩ := ha i
  use j

Depends on / 依赖: le_antisymm, ofArrows_comp_le
-/
lemma ofArrows_comp_eq_of_surjective {X : C} {ι σ : Type*} {Y : ι -> C}
    (f : forall i, Y i ⟶ X) {a : σ -> ι} (ha : a.Surjective) :
    ofArrows (Y ∘ a) (fun i => f (a i)) = ofArrows Y f := by
  refine le_antisymm (ofArrows_comp_le f a) ?_
  rintro - - ⟨i⟩
  obtain ⟨j, rfl⟩ := ha i
  use j

/--
lemma `ofArrows_le_iff` / 引理 `ofArrows_le_iff`

English:
lemma ofArrows_le_iff
  given: {X : C} {ι : Type*} {Y : ι -> C} {f : forall i, Y i ⟶ X} {R : Presieve X}
  proof: ⟨fun hle i => hle _ _ ⟨i⟩, fun h _ g ⟨i⟩ => h i⟩

中文:
引理 ofArrows_le_iff
  条件: {X : C} {ι : 类型} {Y : ι -> C} {f : 对任意 i, Y i ⟶ X} {R : Presieve X}
  证明: ⟨fun hle i => hle _ _ ⟨i⟩, fun h _ g ⟨i⟩ => h i⟩
-/
lemma ofArrows_le_iff {X : C} {ι : Type*} {Y : ι -> C} {f : forall i, Y i ⟶ X} {R : Presieve X} :
    Presieve.ofArrows Y f <= R ↔ forall i, R (f i) :=
  ⟨fun hle i => hle _ _ ⟨i⟩, fun h _ g ⟨i⟩ => h i⟩

/--
lemma `ofArrows_of_unique` / 引理 `ofArrows_of_unique`

English:
lemma ofArrows_of_unique
  given: {X : C} {ι : Type*} [Unique ι] {Y : ι -> C} (f : forall i, Y i ⟶ X)
  proof: by
  refine le_antisymm ?_ fun Y _ ⟨⟩ => ⟨default⟩
  rw [ofArrows_le_iff]
  intro i
  obtain rfl : i = default := Subsingleton.elim _ _
  simp

中文:
引理 ofArrows_of_unique
  条件: {X : C} {ι : 类型} [唯一 ι] {Y : ι -> C} (f : 对任意 i, Y i ⟶ X)
  证明: by
  refine le_antisymm ?_ fun Y _ ⟨⟩ => ⟨default⟩
  rw [ofArrows_le_iff]
  intro i
  obtain rfl : i = default := Subsingleton.elim _ _
  simp

Depends on / 依赖: Subsingleton, Subsingleton.elim, le_antisymm, ofArrows_le_iff
-/
lemma ofArrows_of_unique {X : C} {ι : Type*} [Unique ι] {Y : ι -> C} (f : forall i, Y i ⟶ X) :
    ofArrows Y f = singleton (f default) := by
  refine le_antisymm ?_ fun Y _ ⟨⟩ => ⟨default⟩
  rw [ofArrows_le_iff]
  intro i
  obtain rfl : i = default := Subsingleton.elim _ _
  simp

/--
theorem `ofArrows_pUnit` / 定理 `ofArrows_pUnit`

English:
theorem ofArrows_pUnit
  statement: (ofArrows _ fun _ : PUnit.{w + 1} => f) = singleton f
  proof: by
  rw [ofArrows_of_unique]

@[grind =]

中文:
定理 ofArrows_pUnit
  结论: (ofArrows _ fun _ : 命题单元.{w + 1} => f) = singleton f
  证明: by
  rw [ofArrows_of_unique]

@[grind =]

Depends on / 依赖: ofArrows_of_unique
-/
theorem ofArrows_pUnit : (ofArrows _ fun _ : PUnit.{w + 1} => f) = singleton f := by
  rw [ofArrows_of_unique]

@[grind =]
/--
lemma `ofArrows_of_isEmpty` / 引理 `ofArrows_of_isEmpty`

English:
lemma ofArrows_of_isEmpty
  given: {X : C} {ι : Type*} [IsEmpty ι] {Y : ι -> C} (f : forall i, Y i ⟶ X)
  proof: by
  rw [eq_bot_iff]; rw [ofArrows_le_iff]
  simp

中文:
引理 ofArrows_of_isEmpty
  条件: {X : C} {ι : 类型} [是空 ι] {Y : ι -> C} (f : 对任意 i, Y i ⟶ X)
  证明: by
  rw [eq_bot_iff]; rw [ofArrows_le_iff]
  simp

Depends on / 依赖: eq_bot_iff, ofArrows_le_iff
-/
lemma ofArrows_of_isEmpty {X : C} {ι : Type*} [IsEmpty ι] {Y : ι -> C} (f : forall i, Y i ⟶ X) :
    ofArrows Y f = ⊥ := by
  rw [eq_bot_iff]; rw [ofArrows_le_iff]
  simp

/--
Inductive type `bindOfArrows` / 归纳类型 `bindOfArrows`

English:
inductive bindOfArrows
  parameters: {ι : Type*} {X : C} (Y : ι -> C)

中文:
归纳类型 bindOfArrows
  参数: {ι : 类型} {X : C} (Y : ι -> C)
-/
inductive bindOfArrows {ι : Type*} {X : C} (Y : ι -> C)
    (f : forall i, Y i ⟶ X) (R : forall i, Presieve (Y i)) : Presieve X
  | mk (i : ι) {Z : C} (g : Z ⟶ Y i) (hg : R i g) : bindOfArrows Y f R (g ≫ f i)

/--
lemma `bindOfArrows_ofArrows` / 引理 `bindOfArrows_ofArrows`

English:
lemma bindOfArrows_ofArrows
  statement: {ι : Type*} {S : C} {X : ι -> C} (f : (i : ι) -> X i ⟶ S)
  proof: by
  refine le_antisymm ?_ (fun _ _ ⟨p⟩ => ⟨p.1, _, ⟨p.2⟩⟩)
  rintro W u ⟨i, v, ⟨j⟩⟩
  exact ⟨Sigma.mk i j⟩

中文:
引理 bindOfArrows_ofArrows
  结论: {ι : 类型} {S : C} {X : ι -> C} (f : (i : ι) -> X i ⟶ S)
  证明: by
  refine le_antisymm ?_ (fun _ _ ⟨p⟩ => ⟨p.1, _, ⟨p.2⟩⟩)
  rintro W u ⟨i, v, ⟨j⟩⟩
  exact ⟨Sigma.mk i j⟩

Depends on / 依赖: Sigma.mk, le_antisymm
-/
lemma bindOfArrows_ofArrows {ι : Type*} {S : C} {X : ι -> C} (f : (i : ι) -> X i ⟶ S)
    {σ : ι -> Type*} {Y : (i : ι) -> σ i -> C} (g : (i : ι) -> (j : σ i) -> Y i j ⟶ X i) :
    Presieve.bindOfArrows X f (fun i => .ofArrows (Y i) (g i)) =
      Presieve.ofArrows (fun p : Σ i, σ i => Y p.1 p.2) (fun p => g p.1 p.2 ≫ f p.1) := by
  refine le_antisymm ?_ (fun _ _ ⟨p⟩ => ⟨p.1, _, ⟨p.2⟩⟩)
  rintro W u ⟨i, v, ⟨j⟩⟩
  exact ⟨Sigma.mk i j⟩

/--
Definition of `pushforward` / `pushforward` 的定义

English:
definition pushforward
  signature: {X Y : C} (f : X ⟶ Y) (R : Presieve X)
  body: fun Z fg => exists (g : Z ⟶ X), g ≫ f = fg ∧ R g

@[grind .]

中文:
定义 pushforward
  签名: {X Y : C} (f : X ⟶ Y) (R : Presieve X)
  定义体: fun Z fg => exists (g : Z ⟶ X), g ≫ f = fg ∧ R g

@[grind .]
-/
def pushforward {X Y : C} (f : X ⟶ Y) (R : Presieve X) : Presieve Y :=
  fun Z fg => exists (g : Z ⟶ X), g ≫ f = fg ∧ R g

@[grind .]
/--
lemma `pushforward_apply_comp` / 引理 `pushforward_apply_comp`

English:
lemma pushforward_apply_comp
  given: {X Y Z : C} {f : X ⟶ Y} {R : Presieve X} {g : Z ⟶ X} (hg : R g)
  proof: ⟨g, rfl, hg⟩

中文:
引理 pushforward_apply_comp
  条件: {X Y Z : C} {f : X ⟶ Y} {R : Presieve X} {g : Z ⟶ X} (hg : R g)
  证明: ⟨g, rfl, hg⟩
-/
lemma pushforward_apply_comp {X Y Z : C} {f : X ⟶ Y} {R : Presieve X} {g : Z ⟶ X} (hg : R g) :
    R.pushforward f (g ≫ f) :=
  ⟨g, rfl, hg⟩

/--
lemma `pushforward_ofArrows` / 引理 `pushforward_ofArrows`

English:
lemma pushforward_ofArrows
  statement: {ι : Type*} {U : ι -> C} {X Y : C} (g : forall i, U i ⟶ X)
  proof: by
  refine le_antisymm ?_ ?_
  · rintro _ _ ⟨u, rfl, ⟨i⟩⟩
    exact ⟨i⟩
  · rw [ofArrows_le_iff]
    intro i
    use g i, rfl
    exact ⟨i⟩

中文:
引理 pushforward_ofArrows
  结论: {ι : 类型} {U : ι -> C} {X Y : C} (g : 对任意 i, U i ⟶ X)
  证明: by
  refine le_antisymm ?_ ?_
  · rintro _ _ ⟨u, rfl, ⟨i⟩⟩
    exact ⟨i⟩
  · rw [ofArrows_le_iff]
    intro i
    use g i, rfl
    exact ⟨i⟩

Depends on / 依赖: le_antisymm, ofArrows_le_iff
-/
lemma pushforward_ofArrows {ι : Type*} {U : ι -> C} {X Y : C} (g : forall i, U i ⟶ X)
    (f : X ⟶ Y) : (ofArrows _ g).pushforward f = ofArrows _ (g · ≫ f) := by
  refine le_antisymm ?_ ?_
  · rintro _ _ ⟨u, rfl, ⟨i⟩⟩
    exact ⟨i⟩
  · rw [ofArrows_le_iff]
    intro i
    use g i, rfl
    exact ⟨i⟩

/--
lemma `pushforward_singleton` / 引理 `pushforward_singleton`

English:
lemma pushforward_singleton
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  rw [← ofArrows_pUnit.{0}]; rw [pushforward_ofArrows]; rw [ofArrows_pUnit.{0}]

中文:
引理 pushforward_singleton
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  rw [← ofArrows_pUnit.{0}]; rw [pushforward_ofArrows]; rw [ofArrows_pUnit.{0}]

Depends on / 依赖: ofArrows_pUnit, pushforward_ofArrows
-/
lemma pushforward_singleton {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (singleton f).pushforward g = .singleton (f ≫ g) := by
  rw [← ofArrows_pUnit.{0}]; rw [pushforward_ofArrows]; rw [ofArrows_pUnit.{0}]

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: {X Y : C} (f : X ⟶ Y) (R : Presieve Y)
  body: fun _ g => R (g ≫ f)

中文:
定义 pullback
  签名: {X Y : C} (f : X ⟶ Y) (R : Presieve Y)
  定义体: fun _ g => R (g ≫ f)
-/
def pullback {X Y : C} (f : X ⟶ Y) (R : Presieve Y) : Presieve X :=
  fun _ g => R (g ≫ f)

variable {f} in
@[simp, grind =]
/--
lemma `pullback_iff` / 引理 `pullback_iff`

English:
lemma pullback_iff
  given: {R : Presieve X} {Z : C} {g : Z ⟶ Y}
  proof: .rfl

中文:
引理 pullback_iff
  条件: {R : Presieve X} {Z : C} {g : Z ⟶ Y}
  证明: .rfl
-/
lemma pullback_iff {R : Presieve X} {Z : C} {g : Z ⟶ Y} :
    R.pullback f g ↔ R (g ≫ f) :=
  .rfl

/--
lemma `pushforward_le_iff_le_pullback` / 引理 `pushforward_le_iff_le_pullback`

English:
lemma pushforward_le_iff_le_pullback
  given: (R : Presieve Y) (T : Presieve X)
  proof: by
  refine ⟨fun hle Z g hg => hle _ _ (pushforward_apply_comp hg), ?_⟩
  rintro hle Z - ⟨g, rfl, hg⟩
  exact hle _ _ hg

中文:
引理 pushforward_le_iff_le_pullback
  条件: (R : Presieve Y) (T : Presieve X)
  证明: by
  refine ⟨fun hle Z g hg => hle _ _ (pushforward_apply_comp hg), ?_⟩
  rintro hle Z - ⟨g, rfl, hg⟩
  exact hle _ _ hg

Depends on / 依赖: pushforward_apply_comp
-/
lemma pushforward_le_iff_le_pullback (R : Presieve Y) (T : Presieve X) :
    R.pushforward f <= T ↔ R <= T.pullback f := by
  refine ⟨fun hle Z g hg => hle _ _ (pushforward_apply_comp hg), ?_⟩
  rintro hle Z - ⟨g, rfl, hg⟩
  exact hle _ _ hg

/--
lemma `galoisConnection_pushforward_pullback` / 引理 `galoisConnection_pushforward_pullback`

English:
lemma galoisConnection_pushforward_pullback
  proof: pushforward_le_iff_le_pullback f

中文:
引理 galoisConnection_pushforward_pullback
  证明: pushforward_le_iff_le_pullback f

Depends on / 依赖: pushforward_le_iff_le_pullback
-/
lemma galoisConnection_pushforward_pullback :
    GaloisConnection (pushforward f) (pullback f) :=
  pushforward_le_iff_le_pullback f

/--
lemma `monotone_pushforward` / 引理 `monotone_pushforward`

English:
lemma monotone_pushforward
  statement: Monotone (pushforward f)
  proof: (galoisConnection_pushforward_pullback f).monotone_l

中文:
引理 monotone_pushforward
  结论: 递增 (pushforward f)
  证明: (galoisConnection_pushforward_pullback f).monotone_l

Depends on / 依赖: galoisConnection_pushforward_pullback, monotone_l
-/
lemma monotone_pushforward : Monotone (pushforward f) :=
  (galoisConnection_pushforward_pullback f).monotone_l

/--
lemma `monotone_pullback` / 引理 `monotone_pullback`

English:
lemma monotone_pullback
  statement: Monotone (pullback f)
  proof: (galoisConnection_pushforward_pullback f).monotone_u

中文:
引理 monotone_pullback
  结论: 递增 (pullback f)
  证明: (galoisConnection_pushforward_pullback f).monotone_u

Depends on / 依赖: galoisConnection_pushforward_pullback, monotone_u
-/
lemma monotone_pullback : Monotone (pullback f) :=
  (galoisConnection_pushforward_pullback f).monotone_u

/--
lemma `pushforward_pullback_le` / 引理 `pushforward_pullback_le`

English:
lemma pushforward_pullback_le
  given: (R : Presieve X)
  statement: (R.pullback f).pushforward f <= R
  proof: (galoisConnection_pushforward_pullback f).l_u_le _

中文:
引理 pushforward_pullback_le
  条件: (R : Presieve X)
  结论: (R.pullback f).pushforward f <= R
  证明: (galoisConnection_pushforward_pullback f).l_u_le _

Depends on / 依赖: galoisConnection_pushforward_pullback, l_u_le
-/
lemma pushforward_pullback_le (R : Presieve X) : (R.pullback f).pushforward f <= R :=
  (galoisConnection_pushforward_pullback f).l_u_le _

/--
lemma `le_pullback_pushforward` / 引理 `le_pullback_pushforward`

English:
lemma le_pullback_pushforward
  given: (R : Presieve Y)
  statement: R <= (R.pushforward f).pullback f
  proof: (galoisConnection_pushforward_pullback f).le_u_l _

@[simp]

中文:
引理 le_pullback_pushforward
  条件: (R : Presieve Y)
  结论: R <= (R.pushforward f).pullback f
  证明: (galoisConnection_pushforward_pullback f).le_u_l _

@[simp]

Depends on / 依赖: galoisConnection_pushforward_pullback, le_u_l
-/
lemma le_pullback_pushforward (R : Presieve Y) : R <= (R.pushforward f).pullback f :=
  (galoisConnection_pushforward_pullback f).le_u_l _

@[simp]
/--
lemma `pullback_id` / 引理 `pullback_id`

English:
lemma pullback_id
  given: (R : Presieve X)
  statement: R.pullback (𝟙 X) = R
  proof: by
  funext
  simp

中文:
引理 pullback_id
  条件: (R : Presieve X)
  结论: R.pullback (𝟙 X) = R
  证明: by
  funext
  simp
-/
lemma pullback_id (R : Presieve X) : R.pullback (𝟙 X) = R := by
  funext
  simp

/--
lemma `pullback_comp` / 引理 `pullback_comp`

English:
lemma pullback_comp
  given: (R : Presieve Z) (g : X ⟶ Z)
  proof: by
  funext
  simp

@[simp]

中文:
引理 pullback_comp
  条件: (R : Presieve Z) (g : X ⟶ Z)
  证明: by
  funext
  simp

@[simp]
-/
lemma pullback_comp (R : Presieve Z) (g : X ⟶ Z) :
    R.pullback (f ≫ g) = (R.pullback g).pullback f := by
  funext
  simp

@[simp]
/--
lemma `pushforward_id` / 引理 `pushforward_id`

English:
lemma pushforward_id
  given: (R : Presieve X)
  statement: R.pushforward (𝟙 X) = R
  proof: by
  funext
  simp [pushforward]

中文:
引理 pushforward_id
  条件: (R : Presieve X)
  结论: R.pushforward (𝟙 X) = R
  证明: by
  funext
  simp [pushforward]

Depends on / 依赖: pushforward
-/
lemma pushforward_id (R : Presieve X) : R.pushforward (𝟙 X) = R := by
  funext
  simp [pushforward]

/--
lemma `pushforward_comp` / 引理 `pushforward_comp`

English:
lemma pushforward_comp
  given: (R : Presieve Y) (g : X ⟶ Z)
  proof: by
  funext
  simp [pushforward]

中文:
引理 pushforward_comp
  条件: (R : Presieve Y) (g : X ⟶ Z)
  证明: by
  funext
  simp [pushforward]

Depends on / 依赖: pushforward
-/
lemma pushforward_comp (R : Presieve Y) (g : X ⟶ Z) :
    R.pushforward (f ≫ g) = (R.pushforward f).pushforward g := by
  funext
  simp [pushforward]

/--
Definition of `functorPullback` / `functorPullback` 的定义

English:
definition functorPullback
  signature: (R : Presieve (F.obj X))
  body: fun _ f => R (F.map f)

@[simp]

中文:
定义 functorPullback
  签名: (R : Presieve (F.obj X))
  定义体: fun _ f => R (F.map f)

@[simp]

Depends on / 依赖: F.map
-/
def functorPullback (R : Presieve (F.obj X)) : Presieve X := fun _ f => R (F.map f)

@[simp]
/--
theorem `functorPullback_mem` / 定理 `functorPullback_mem`

English:
theorem functorPullback_mem
  given: (R : Presieve (F.obj X)) {Y} (f : Y ⟶ X)
  proof: Iff.rfl

@[simp]

中文:
定理 functorPullback_mem
  条件: (R : Presieve (F.obj X)) {Y} (f : Y ⟶ X)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem functorPullback_mem (R : Presieve (F.obj X)) {Y} (f : Y ⟶ X) :
    R.functorPullback F f ↔ R (F.map f) :=
  Iff.rfl

@[simp]
/--
theorem `functorPullback_id` / 定理 `functorPullback_id`

English:
theorem functorPullback_id
  given: (R : Presieve X)
  statement: R.functorPullback (𝟭 _) = R
  proof: rfl

中文:
定理 functorPullback_id
  条件: (R : Presieve X)
  结论: R.functorPullback (𝟭 _) = R
  证明: rfl
-/
theorem functorPullback_id (R : Presieve X) : R.functorPullback (𝟭 _) = R :=
  rfl

/--
Definition of `HasPairwisePullbacks` / `HasPairwisePullbacks` 的定义

English:
class HasPairwisePullbacks
  parameters: (R : Presieve X)
  axioms and operations (1):
    - has_pullbacks : forall {Y Z} {f : Y ⟶ X} (_ : R f) {g : Z ⟶ X} (_ : R g), HasPullback f g

中文:
类 有PairwisePullbacks
  参数: (R : Presieve X)
  公理与运算 (1 个):
    - has_pullbacks : 对任意 {Y Z} {f : Y ⟶ X} (_ : R f) {g : Z ⟶ X} (_ : R g), HasPullback f g
-/
class HasPairwisePullbacks (R : Presieve X) : Prop where
  /-- For all arrows `f` and `g` in `R`, the pullback of `f` and `g` exists. -/
  has_pullbacks : forall {Y Z} {f : Y ⟶ X} (_ : R f) {g : Z ⟶ X} (_ : R g), HasPullback f g

instance (R : Presieve X) [HasPullbacks C] : R.HasPairwisePullbacks := ⟨fun _ _ => inferInstance⟩

instance {α : Type v₂} {X : α -> C} {B : C} (π : (a : α) -> X a ⟶ B)
    [(Presieve.ofArrows X π).HasPairwisePullbacks] (a b : α) : HasPullback (π a) (π b) :=
  Presieve.HasPairwisePullbacks.has_pullbacks (Presieve.ofArrows.mk _) (Presieve.ofArrows.mk _)

section FunctorPushforward

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/--
Definition of `functorPushforward` / `functorPushforward` 的定义

English:
definition functorPushforward
  signature: (S : Presieve X)
  body: fun Y f =>
  exists (Z : C) (g : Z ⟶ X) (h : Y ⟶ F.obj Z), S g ∧ f = h ≫ F.map g

中文:
定义 functorPushforward
  签名: (S : Presieve X)
  定义体: fun Y f =>
  exists (Z : C) (g : Z ⟶ X) (h : Y ⟶ F.obj Z), S g ∧ f = h ≫ F.map g
-/
def functorPushforward (S : Presieve X) : Presieve (F.obj X) := fun Y f =>
  exists (Z : C) (g : Z ⟶ X) (h : Y ⟶ F.obj Z), S g ∧ f = h ≫ F.map g

variable {F} in
/--
lemma `functorPushforward_monotone` / 引理 `functorPushforward_monotone`

English:
lemma functorPushforward_monotone
  given: {X : C}
  proof: fun _ _ hle _ _ ⟨Z, g, u, hg, hf⟩ => ⟨Z, g, u, hle _ _ hg, hf⟩

中文:
引理 functorPushforward_monotone
  条件: {X : C}
  证明: fun _ _ hle _ _ ⟨Z, g, u, hg, hf⟩ => ⟨Z, g, u, hle _ _ hg, hf⟩
-/
lemma functorPushforward_monotone {X : C} :
    Monotone (Presieve.functorPushforward (X := X) F) :=
  fun _ _ hle _ _ ⟨Z, g, u, hg, hf⟩ => ⟨Z, g, u, hle _ _ hg, hf⟩

/--
Definition of `FunctorPushforwardStructure` / `FunctorPushforwardStructure` 的定义

English:
structure FunctorPushforwardStructure
  parameters: (S : Presieve X) {Y} (f : Y ⟶ F.obj X)
  axioms and operations (5):
    - preobj : C
    - premap : preobj ⟶ X
    - lift : Y ⟶ F.obj preobj
    - cover : S premap
    - fac : f = lift ≫ F.map premap

中文:
结构 FunctorPushforwardStructure
  参数: (S : Presieve X) {Y} (f : Y ⟶ F.obj X)
  公理与运算 (5 个):
    - preobj : C
    - premap : preobj ⟶ X
    - lift : Y ⟶ F.obj preobj
    - cover : S premap
    - fac : f = lift ≫ F.map premap
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

/--
Definition of `getFunctorPushforwardStructure` / `getFunctorPushforwardStructure` 的定义

English:
definition getFunctorPushforwardStructure
  signature: {F : C ⥤ D} {S : Presieve X} {Y : D}
  body: by
  choose Z f' g h₁ h using h
  exact ⟨Z, f', g, h₁, h⟩

中文:
定义 getFunctorPushforwardStructure
  签名: {F : C ⥤ D} {S : Presieve X} {Y : D}
  定义体: by
  choose Z f' g h₁ h using h
  exact ⟨Z, f', g, h₁, h⟩
-/
noncomputable def getFunctorPushforwardStructure {F : C ⥤ D} {S : Presieve X} {Y : D}
    {f : Y ⟶ F.obj X} (h : S.functorPushforward F f) : FunctorPushforwardStructure F S f := by
  choose Z f' g h₁ h using h
  exact ⟨Z, f', g, h₁, h⟩

set_option backward.defeqAttrib.useBackward true in
/--
theorem `functorPushforward_comp` / 定理 `functorPushforward_comp`

English:
theorem functorPushforward_comp
  given: (R : Presieve X)
  proof: by
  funext x
  ext f
  constructor
  · rintro ⟨X, f₁, g₁, h₁, rfl⟩
    exact ⟨F.obj X, F.map f₁, g₁, ⟨X, f₁, 𝟙 _, h₁, by simp⟩, rfl⟩
  · rintro ⟨X, f₁, g₁, ⟨X', f₂, g₂, h₁, rfl⟩, rfl⟩
    exact ⟨X', f₂, g₁ ≫ G.map g₂, h₁, by simp⟩

中文:
定理 functorPushforward_comp
  条件: (R : Presieve X)
  证明: by
  funext x
  ext f
  constructor
  · rintro ⟨X, f₁, g₁, h₁, rfl⟩
    exact ⟨F.obj X, F.map f₁, g₁, ⟨X, f₁, 𝟙 _, h₁, by simp⟩, rfl⟩
  · rintro ⟨X, f₁, g₁, ⟨X', f₂, g₂, h₁, rfl⟩, rfl⟩
    exact ⟨X', f₂, g₁ ≫ G.map g₂, h₁, by simp⟩

Depends on / 依赖: F.map, F.obj, G.map
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

/--
theorem `image_mem_functorPushforward` / 定理 `image_mem_functorPushforward`

English:
theorem image_mem_functorPushforward
  given: (R : Presieve X) {f : Y ⟶ X} (h : R f)
  proof: ⟨Y, f, 𝟙 _, h, by simp⟩

中文:
定理 image_mem_functorPushforward
  条件: (R : Presieve X) {f : Y ⟶ X} (h : R f)
  证明: ⟨Y, f, 𝟙 _, h, by simp⟩
-/
theorem image_mem_functorPushforward (R : Presieve X) {f : Y ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨Y, f, 𝟙 _, h, by simp⟩

/--
Inductive type `map` / 归纳类型 `map`

English:
inductive map
  parameters: (s : Presieve X)
  constructors (1):
    - of: {Y : C} {u : Y ⟶ X} (h : s u) : map s (F.map u)

中文:
归纳类型 map
  参数: (s : Presieve X)
  构造子 (1 个):
    - of: {Y : C} {u : Y ⟶ X} (h : s u) : map s (F.map u)
-/
inductive map (s : Presieve X) : Presieve (F.obj X) where
  | of {Y : C} {u : Y ⟶ X} (h : s u) : map s (F.map u)

section

variable {F}

@[grind ←]
/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: {X Y : C} {f : Y ⟶ X} {R : Presieve X} (hf : R f)
  statement: R.map F (F.map f)
  proof: ⟨hf⟩

中文:
引理 map_map
  条件: {X Y : C} {f : Y ⟶ X} {R : Presieve X} (hf : R f)
  结论: R.map F (F.map f)
  证明: ⟨hf⟩
-/
lemma map_map {X Y : C} {f : Y ⟶ X} {R : Presieve X} (hf : R f) : R.map F (F.map f) :=
  ⟨hf⟩

/--
lemma `map_iff` / 引理 `map_iff`

English:
lemma map_iff
  given: {X : C} {R : Presieve X} {Y : D} {f : Y ⟶ F.obj X}
  proof: by
  refine ⟨fun (.of (u := u) hu) => ⟨_, rfl, u, hu, by simp⟩, fun ⟨Z, h, g, hg, heq⟩ => ?_⟩
  subst h
  rw [eqToHom_refl]; rw [Category.id_comp] at heq
  simp [← heq, map_map hg]

@[simp]

中文:
引理 map_iff
  条件: {X : C} {R : Presieve X} {Y : D} {f : Y ⟶ F.obj X}
  证明: by
  refine ⟨fun (.of (u := u) hu) => ⟨_, rfl, u, hu, by simp⟩, fun ⟨Z, h, g, hg, heq⟩ => ?_⟩
  subst h
  rw [eqToHom_refl]; rw [Category.id_comp] at heq
  simp [← heq, map_map hg]

@[simp]

Depends on / 依赖: Category, Category.id_comp, eqToHom_refl, id_comp, map_map
-/
lemma map_iff {X : C} {R : Presieve X} {Y : D} {f : Y ⟶ F.obj X} :
    R.map F f ↔ exists (Z : C) (h : F.obj Z = Y) (g : Z ⟶ X), R g ∧ F.map g = eqToHom h ≫ f := by
  refine ⟨fun (.of (u := u) hu) => ⟨_, rfl, u, hu, by simp⟩, fun ⟨Z, h, g, hg, heq⟩ => ?_⟩
  subst h
  rw [eqToHom_refl]; rw [Category.id_comp] at heq
  simp [← heq, map_map hg]

@[simp]
/--
lemma `map_ofArrows` / 引理 `map_ofArrows`

English:
lemma map_ofArrows
  given: {X : C} {ι : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X)
  proof: by
  refine le_antisymm (fun Z g hg => ?_) fun _ _ ⟨i⟩ => map_map ⟨i⟩
  obtain ⟨hu⟩ := hg
  obtain ⟨i, rfl, rfl⟩ := Presieve.ofArrows_surj _ _ hu
  simpa using ofArrows.mk i

@[simp]

中文:
引理 map_ofArrows
  条件: {X : C} {ι : 类型} {Y : ι -> C} (f : 对任意 i, Y i ⟶ X)
  证明: by
  refine le_antisymm (fun Z g hg => ?_) fun _ _ ⟨i⟩ => map_map ⟨i⟩
  obtain ⟨hu⟩ := hg
  obtain ⟨i, rfl, rfl⟩ := Presieve.ofArrows_surj _ _ hu
  simpa using ofArrows.mk i

@[simp]

Depends on / 依赖: Presieve, Presieve.ofArrows_surj, le_antisymm, map_map, ofArrows, ofArrows.mk, ofArrows_surj
-/
lemma map_ofArrows {X : C} {ι : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X) :
    (ofArrows Y f).map F = ofArrows _ (fun i => F.map (f i)) := by
  refine le_antisymm (fun Z g hg => ?_) fun _ _ ⟨i⟩ => map_map ⟨i⟩
  obtain ⟨hu⟩ := hg
  obtain ⟨i, rfl, rfl⟩ := Presieve.ofArrows_surj _ _ hu
  simpa using ofArrows.mk i

@[simp]
/--
lemma `map_singleton` / 引理 `map_singleton`

English:
lemma map_singleton
  given: {X Y : C} (f : X ⟶ Y)
  statement: (singleton f).map F = singleton (F.map f)
  proof: by
  rw [← ofArrows_pUnit.{0}]; rw [map_ofArrows]; rw [ofArrows_pUnit]

中文:
引理 map_singleton
  条件: {X Y : C} (f : X ⟶ Y)
  结论: (singleton f).map F = singleton (F.map f)
  证明: by
  rw [← ofArrows_pUnit.{0}]; rw [map_ofArrows]; rw [ofArrows_pUnit]

Depends on / 依赖: map_ofArrows, ofArrows_pUnit
-/
lemma map_singleton {X Y : C} (f : X ⟶ Y) : (singleton f).map F = singleton (F.map f) := by
  rw [← ofArrows_pUnit.{0}]; rw [map_ofArrows]; rw [ofArrows_pUnit]

/--
lemma `map_le_iff_le_functorPullback` / 引理 `map_le_iff_le_functorPullback`

English:
lemma map_le_iff_le_functorPullback
  given: {R : Presieve X} {S : Presieve (F.obj X)}
  proof: ⟨fun h _ _ hf => h _ _ (.of hf), fun h _ f ⟨hu⟩ => h _ _ hu⟩

中文:
引理 map_le_iff_le_functorPullback
  条件: {R : Presieve X} {S : Presieve (F.obj X)}
  证明: ⟨fun h _ _ hf => h _ _ (.of hf), fun h _ f ⟨hu⟩ => h _ _ hu⟩
-/
lemma map_le_iff_le_functorPullback {R : Presieve X} {S : Presieve (F.obj X)} :
    R.map F <= S ↔ R <= S.functorPullback F :=
  ⟨fun h _ _ hf => h _ _ (.of hf), fun h _ f ⟨hu⟩ => h _ _ hu⟩

variable (F) in
/--
lemma `galoisConnection_map_functorPullback` / 引理 `galoisConnection_map_functorPullback`

English:
lemma galoisConnection_map_functorPullback
  given: (X : C)
  proof: fun _ _ => Presieve.map_le_iff_le_functorPullback

中文:
引理 galoisConnection_map_functorPullback
  条件: (X : C)
  证明: fun _ _ => Presieve.map_le_iff_le_functorPullback

Depends on / 依赖: Presieve, Presieve.functorPullback, functorPullback
-/
lemma galoisConnection_map_functorPullback (X : C) :
    GaloisConnection (Presieve.map F (X := X)) (Presieve.functorPullback F) :=
  fun _ _ => Presieve.map_le_iff_le_functorPullback

/--
lemma `map_functorPullback` / 引理 `map_functorPullback`

English:
lemma map_functorPullback
  given: {X : C} (R : Presieve (F.obj X))
  statement: (R.functorPullback F).map F <= R
  proof: (galoisConnection_map_functorPullback _ _).l_u_le _

中文:
引理 map_functorPullback
  条件: {X : C} (R : Presieve (F.obj X))
  结论: (R.functorPullback F).map F <= R
  证明: (galoisConnection_map_functorPullback _ _).l_u_le _

Depends on / 依赖: galoisConnection_map_functorPullback, l_u_le
-/
lemma map_functorPullback {X : C} (R : Presieve (F.obj X)) : (R.functorPullback F).map F <= R :=
  (galoisConnection_map_functorPullback _ _).l_u_le _

/--
lemma `le_functorPullback_map` / 引理 `le_functorPullback_map`

English:
lemma le_functorPullback_map
  given: {X : C} (R : Presieve X)
  statement: R <= (R.map F).functorPullback F
  proof: (galoisConnection_map_functorPullback _ _).le_u_l _

@[simp]

中文:
引理 le_functorPullback_map
  条件: {X : C} (R : Presieve X)
  结论: R <= (R.map F).functorPullback F
  证明: (galoisConnection_map_functorPullback _ _).le_u_l _

@[simp]

Depends on / 依赖: galoisConnection_map_functorPullback, le_u_l
-/
lemma le_functorPullback_map {X : C} (R : Presieve X) : R <= (R.map F).functorPullback F :=
  (galoisConnection_map_functorPullback _ _).le_u_l _

@[simp]
/--
lemma `map_functorPullback_map` / 引理 `map_functorPullback_map`

English:
lemma map_functorPullback_map
  given: {X : C} (R : Presieve X)
  proof: (galoisConnection_map_functorPullback _ _).l_u_l_eq_l _

@[simp]

中文:
引理 map_functorPullback_map
  条件: {X : C} (R : Presieve X)
  证明: (galoisConnection_map_functorPullback _ _).l_u_l_eq_l _

@[simp]

Depends on / 依赖: galoisConnection_map_functorPullback, l_u_l_eq_l
-/
lemma map_functorPullback_map {X : C} (R : Presieve X) :
    Presieve.map F (Presieve.functorPullback F (R.map F)) = R.map F :=
  (galoisConnection_map_functorPullback _ _).l_u_l_eq_l _

@[simp]
/--
lemma `functorPullback_map_functorPullback` / 引理 `functorPullback_map_functorPullback`

English:
lemma functorPullback_map_functorPullback
  given: {X : C} (R : Presieve (F.obj X))
  proof: (galoisConnection_map_functorPullback _ _).u_l_u_eq_u _

@[simp]

中文:
引理 functorPullback_map_functorPullback
  条件: {X : C} (R : Presieve (F.obj X))
  证明: (galoisConnection_map_functorPullback _ _).u_l_u_eq_u _

@[simp]

Depends on / 依赖: galoisConnection_map_functorPullback, u_l_u_eq_u
-/
lemma functorPullback_map_functorPullback {X : C} (R : Presieve (F.obj X)) :
    Presieve.functorPullback F (Presieve.map F (R.functorPullback F)) = R.functorPullback F :=
  (galoisConnection_map_functorPullback _ _).u_l_u_eq_u _

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: {X : C} (R : Presieve X)
  statement: R.map (𝟭 C) = R
  proof: le_antisymm (fun _ _ ⟨hg⟩ => hg) fun _ _ hg => ⟨hg⟩

@[gcongr]

中文:
引理 map_id
  条件: {X : C} (R : Presieve X)
  结论: R.map (𝟭 C) = R
  证明: le_antisymm (fun _ _ ⟨hg⟩ => hg) fun _ _ hg => ⟨hg⟩

@[gcongr]

Depends on / 依赖: le_antisymm
-/
lemma map_id {X : C} (R : Presieve X) : R.map (𝟭 C) = R :=
  le_antisymm (fun _ _ ⟨hg⟩ => hg) fun _ _ hg => ⟨hg⟩

@[gcongr]
/--
lemma `map_monotone` / 引理 `map_monotone`

English:
lemma map_monotone
  statement: Monotone (map (X := X) F)
  proof: (galoisConnection_map_functorPullback _ _).monotone_l

@[gcongr]

中文:
引理 map_monotone
  结论: 递增 (map (X := X) F)
  证明: (galoisConnection_map_functorPullback _ _).monotone_l

@[gcongr]
-/
lemma map_monotone : Monotone (map (X := X) F) :=
  (galoisConnection_map_functorPullback _ _).monotone_l

@[gcongr]
/--
lemma `functorPullback_monotone` / 引理 `functorPullback_monotone`

English:
lemma functorPullback_monotone
  given: {X : C}
  statement: Monotone (Presieve.functorPullback (X := X) F)
  proof: (galoisConnection_map_functorPullback F X).monotone_u

@[simp]

中文:
引理 functorPullback_monotone
  条件: {X : C}
  结论: 递增 (Presieve.functorPullback (X := X) F)
  证明: (galoisConnection_map_functorPullback F X).monotone_u

@[simp]
-/
lemma functorPullback_monotone {X : C} : Monotone (Presieve.functorPullback (X := X) F) :=
  (galoisConnection_map_functorPullback F X).monotone_u

@[simp]
/--
lemma `map_bot` / 引理 `map_bot`

English:
lemma map_bot
  statement: map F (⊥ : Presieve X) = ⊥
  proof: (galoisConnection_map_functorPullback _ _).l_bot

中文:
引理 map_bot
  结论: map F (⊥ : Presieve X) = ⊥
  证明: (galoisConnection_map_functorPullback _ _).l_bot

Depends on / 依赖: galoisConnection_map_functorPullback, l_bot
-/
lemma map_bot : map F (⊥ : Presieve X) = ⊥ :=
  (galoisConnection_map_functorPullback _ _).l_bot

end

end FunctorPushforward

section uncurry

variable (s : Presieve X)

/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: : Set (Σ Y, Y ⟶ X)
  body: { u | s u.snd }

中文:
定义 uncurry
  签名: : 集合 (Σ Y, Y ⟶ X)
  定义体: { u | s u.snd }

Depends on / 依赖: u.snd
-/
def uncurry : Set (Σ Y, Y ⟶ X) :=
  { u | s u.snd }

/--
theorem `uncurry_singleton` / 定理 `uncurry_singleton`

English:
theorem uncurry_singleton
  given: {Y : C} (u : Y ⟶ X)
  statement: (singleton u).uncurry = { ⟨Y, u⟩ }
  proof: by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨⟩; rfl
  · intro h
    rw [Set.mem_singleton_iff]; rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h; subst h; constructor

中文:
定理 uncurry_singleton
  条件: {Y : C} (u : Y ⟶ X)
  结论: (singleton u).uncurry = { ⟨Y, u⟩ }
  证明: by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨⟩; rfl
  · intro h
    rw [Set.mem_singleton_iff]; rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h; subst h; constructor
-/
@[simp] theorem uncurry_singleton {Y : C} (u : Y ⟶ X) : (singleton u).uncurry = { ⟨Y, u⟩ } := by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨⟩; rfl
  · intro h
    rw [Set.mem_singleton_iff]; rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h; subst h; constructor

/--
theorem `uncurry_pullbackArrows` / 定理 `uncurry_pullbackArrows`

English:
theorem uncurry_pullbackArrows
  given: [HasPullbacks C] {B : C} (b : B ⟶ X)
  proof: by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨Y, u, hu⟩; exact ⟨⟨Y, u⟩, hu, rfl⟩
  · rintro ⟨⟨Y, u⟩, hu, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    exact ⟨Y, u, hu⟩

中文:
定理 uncurry_pullbackArrows
  条件: [有Pullbacks C] {B : C} (b : B ⟶ X)
  证明: by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨Y, u, hu⟩; exact ⟨⟨Y, u⟩, hu, rfl⟩
  · rintro ⟨⟨Y, u⟩, hu, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    exact ⟨Y, u, hu⟩
-/
@[simp] theorem uncurry_pullbackArrows [HasPullbacks C] {B : C} (b : B ⟶ X) :
    (pullbackArrows b s).uncurry =
      (fun f => ⟨Limits.pullback f.2 b, pullback.snd _ _⟩) '' s.uncurry := by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨Y, u, hu⟩; exact ⟨⟨Y, u⟩, hu, rfl⟩
  · rintro ⟨⟨Y, u⟩, hu, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    exact ⟨Y, u, hu⟩

/--
theorem `uncurry_bind` / 定理 `uncurry_bind`

English:
theorem uncurry_bind
  given: (t : ⦃Y : C⦄ -> (f : Y ⟶ X) -> s f -> Presieve Y)
  proof: by
  ext ⟨Z, v⟩; simp only [Set.mem_iUnion, Set.mem_image]; constructor
  · rintro ⟨Y, g, f, hf, ht, hv⟩
    exact ⟨⟨_, f⟩, hf, ⟨_, g⟩, ht, Sigma.ext rfl (heq_of_eq hv)⟩
  · rintro ⟨⟨_, f⟩, hf, ⟨Y, g⟩, hg, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    

中文:
定理 uncurry_bind
  条件: (t : ⦃Y : C⦄ -> (f : Y ⟶ X) -> s f -> Presieve Y)
  证明: by
  ext ⟨Z, v⟩; simp only [Set.mem_iUnion, Set.mem_image]; constructor
  · rintro ⟨Y, g, f, hf, ht, hv⟩
    exact ⟨⟨_, f⟩, hf, ⟨_, g⟩, ht, Sigma.ext rfl (heq_of_eq hv)⟩
  · rintro ⟨⟨_, f⟩, hf, ⟨Y, g⟩, hg, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    
-/
@[simp] theorem uncurry_bind (t : ⦃Y : C⦄ -> (f : Y ⟶ X) -> s f -> Presieve Y) :
    (s.bind t).uncurry = ⋃ i in s.uncurry,
      Sigma.map id (fun Z g => (g ≫ i.2 : Z ⟶ X)) '' (t i.2 ‹_›).uncurry := by
  ext ⟨Z, v⟩; simp only [Set.mem_iUnion, Set.mem_image]; constructor
  · rintro ⟨Y, g, f, hf, ht, hv⟩
    exact ⟨⟨_, f⟩, hf, ⟨_, g⟩, ht, Sigma.ext rfl (heq_of_eq hv)⟩
  · rintro ⟨⟨_, f⟩, hf, ⟨Y, g⟩, hg, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    exact ⟨_, _, _, _, hg, rfl⟩

/--
theorem `uncurry_ofArrows` / 定理 `uncurry_ofArrows`

English:
theorem uncurry_ofArrows
  given: {ι : Type*} (Y : ι -> C) (f : (i : ι) -> Y i ⟶ X)
  proof: by
  ext ⟨Z, v⟩; simp only [Set.mem_range, Sigma.mk.injEq]; constructor
  · rintro ⟨i⟩; exact ⟨_, rfl, HEq.refl _⟩
  · rintro ⟨i, rfl, h⟩; rw [← eq_of_heq h]; exact ⟨i⟩

中文:
定理 uncurry_ofArrows
  条件: {ι : 类型} (Y : ι -> C) (f : (i : ι) -> Y i ⟶ X)
  证明: by
  ext ⟨Z, v⟩; simp only [Set.mem_range, Sigma.mk.injEq]; constructor
  · rintro ⟨i⟩; exact ⟨_, rfl, HEq.refl _⟩
  · rintro ⟨i, rfl, h⟩; rw [← eq_of_heq h]; exact ⟨i⟩
-/
@[simp] theorem uncurry_ofArrows {ι : Type*} (Y : ι -> C) (f : (i : ι) -> Y i ⟶ X) :
    (ofArrows Y f).uncurry = Set.range fun i : ι => ⟨_, f i⟩ := by
  ext ⟨Z, v⟩; simp only [Set.mem_range, Sigma.mk.injEq]; constructor
  · rintro ⟨i⟩; exact ⟨_, rfl, HEq.refl _⟩
  · rintro ⟨i, rfl, h⟩; rw [← eq_of_heq h]; exact ⟨i⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ofArrows_eq_ofArrows_uncurry` / 引理 `ofArrows_eq_ofArrows_uncurry`

English:
lemma ofArrows_eq_ofArrows_uncurry
  given: {ι : Type*} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S)
  proof: by
  refine le_antisymm (fun Z g hg => ?_) fun Z g ⟨i⟩ => .mk _
  exact .mk' ⟨⟨_, _⟩, hg⟩ (by simp [ofArrows.obj_idx]) (by simp [ofArrows.hom_idx])

中文:
引理 ofArrows_eq_ofArrows_uncurry
  条件: {ι : 类型} {S : C} {X : ι -> C} (f : 对任意 i, X i ⟶ S)
  证明: by
  refine le_antisymm (fun Z g hg => ?_) fun Z g ⟨i⟩ => .mk _
  exact .mk' ⟨⟨_, _⟩, hg⟩ (by simp [ofArrows.obj_idx]) (by simp [ofArrows.hom_idx])

Depends on / 依赖: hom_idx, le_antisymm, obj_idx, ofArrows, ofArrows.hom_idx, ofArrows.obj_idx
-/
lemma ofArrows_eq_ofArrows_uncurry {ι : Type*} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) :
    ofArrows X f = ofArrows _ (fun i : (Presieve.ofArrows X f).uncurry => f i.2.idx) := by
  refine le_antisymm (fun Z g hg => ?_) fun Z g ⟨i⟩ => .mk _
  exact .mk' ⟨⟨_, _⟩, hg⟩ (by simp [ofArrows.obj_idx]) (by simp [ofArrows.hom_idx])

end uncurry

end Presieve

/--
Definition of `Sieve` / `Sieve` 的定义

English:
structure Sieve
  parameters: {C : Type u₁} [Category.{v₁} C] (X : C)
  axioms and operations (2):
    - arrows : Presieve X
    - downward_closed : forall {Y Z f} (_ : arrows f) (g : Z ⟶ Y), arrows (g ≫ f)

中文:
结构 筛
  参数: {C : 类型u₁} [范畴.{v₁} C] (X : C)
  公理与运算 (2 个):
    - arrows : Presieve X
    - downward_closed : 对任意 {Y Z f} (_ : arrows f) (g : Z ⟶ Y), arrows (g ≫ f)
-/
structure Sieve {C : Type u₁} [Category.{v₁} C] (X : C) where
  /-- the underlying presieve -/
  arrows : Presieve X
  /-- stability by precomposition -/
  downward_closed : forall {Y Z f} (_ : arrows f) (g : Z ⟶ Y), arrows (g ≫ f)

namespace Sieve

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (Sieve X) fun _ => Presieve X
  body: ⟨Sieve.arrows⟩

initialize_simps_projections Sieve (arrows -> apply)

中文:
实例 :
  签名: CoeFun (筛 X) fun _ => Presieve X
  定义体: ⟨Sieve.arrows⟩

initialize_simps_projections Sieve (arrows -> apply)

Depends on / 依赖: Sieve.arrows, arrows
-/
instance : CoeFun (Sieve X) fun _ => Presieve X :=
  ⟨Sieve.arrows⟩

initialize_simps_projections Sieve (arrows -> apply)

variable {S R : Sieve X}

attribute [simp] downward_closed

/--
theorem `arrows_ext` / 定理 `arrows_ext`

English:
theorem arrows_ext
  statement: forall {R S : Sieve X}, R.arrows = S.arrows -> R = S
  proof: by
  rintro ⟨_, _⟩ ⟨_, _⟩ rfl
  rfl

@[ext]

中文:
定理 arrows_ext
  结论: 对任意 {R S : 筛 X}, R.arrows = S.arrows -> R = S
  证明: by
  rintro ⟨_, _⟩ ⟨_, _⟩ rfl
  rfl

@[ext]
-/
theorem arrows_ext : forall {R S : Sieve X}, R.arrows = S.arrows -> R = S := by
  rintro ⟨_, _⟩ ⟨_, _⟩ rfl
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {R S : Sieve X} (h : forall ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f)
  statement: R = S
  proof: arrows_ext funext fun _ => funext fun f => propext h f

中文:
定理 ext
  条件: {R S : 筛 X} (h : 对任意 ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f)
  结论: R = S
  证明: arrows_ext funext fun _ => funext fun f => propext h f
-/
protected theorem ext {R S : Sieve X} (h : forall ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) : R = S :=
arrows_ext funext fun _ => funext fun f => propext h f

open Lattice

/--
Definition of `sup` / `sup` 的定义

English:
definition sup
  signature: (𝒮 : Set (Sieve X))
  body: exists S in 𝒮, Sieve.arrows S f
  downward_closed {_ _ f} hf _ := by
    obtain ⟨S, hS, hf⟩ := hf
    exact ⟨S, hS, S.downward_closed hf _⟩

中文:
定义 上确界
  签名: (𝒮 : 集合 (筛 X))
  定义体: exists S in 𝒮, Sieve.arrows S f
  downward_closed {_ _ f} hf _ := by
    obtain ⟨S, hS, hf⟩ := hf
    exact ⟨S, hS, S.downward_closed hf _⟩
-/
protected def sup (𝒮 : Set (Sieve X)) : Sieve X where
  arrows _ f := exists S in 𝒮, Sieve.arrows S f
  downward_closed {_ _ f} hf _ := by
    obtain ⟨S, hS, hf⟩ := hf
    exact ⟨S, hS, S.downward_closed hf _⟩

/--
Definition of `inf` / `inf` 的定义

English:
definition inf
  signature: (𝒮 : Set (Sieve X))
  body: forall S in 𝒮, Sieve.arrows S f
  downward_closed {_ _ _} hf g S H := S.downward_closed (hf S H) g

中文:
定义 下确界
  签名: (𝒮 : 集合 (筛 X))
  定义体: forall S in 𝒮, Sieve.arrows S f
  downward_closed {_ _ _} hf g S H := S.downward_closed (hf S H) g
-/
protected def inf (𝒮 : Set (Sieve X)) : Sieve X where
  arrows _ f := forall S in 𝒮, Sieve.arrows S f
  downward_closed {_ _ _} hf g S H := S.downward_closed (hf S H) g

/--
Definition of `union` / `union` 的定义

English:
definition union
  signature: (S R : Sieve X)
  body: S f ∨ R f
  downward_closed := by rintro _ _ _ (h | h) g <;> simp [h]

中文:
定义 union
  签名: (S R : 筛 X)
  定义体: S f ∨ R f
  downward_closed := by rintro _ _ _ (h | h) g <;> simp [h]
-/
protected def union (S R : Sieve X) : Sieve X where
  arrows _ f := S f ∨ R f
  downward_closed := by rintro _ _ _ (h | h) g <;> simp [h]

/--
Definition of `inter` / `inter` 的定义

English:
definition inter
  signature: (S R : Sieve X)
  body: S f ∧ R f
  downward_closed := by
    rintro _ _ _ ⟨h₁, h₂⟩ g
    simp [h₁, h₂]

中文:
定义 inter
  签名: (S R : 筛 X)
  定义体: S f ∧ R f
  downward_closed := by
    rintro _ _ _ ⟨h₁, h₂⟩ g
    simp [h₁, h₂]
-/
protected def inter (S R : Sieve X) : Sieve X where
  arrows _ f := S f ∧ R f
  downward_closed := by
    rintro _ _ _ ⟨h₁, h₂⟩ g
    simp [h₁, h₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Sieve X)
  body: forall ⦃Y⦄ (f : Y ⟶ X), S f -> R f
  le_refl _ _ _ := id
  le_trans _ _ _ S₁₂ S₂₃ _ _ h := S₂₃ _ (S₁₂ _ h)
  le_antisymm _ _ p q := Sieve.ext fun _ _ => ⟨p _, q _⟩
  top :=
    { arrows := ⊤
      downward_closed := fun _ _ => ⟨⟩ }
  bot :=
    { arrows := ⊥
      downward_closed := False.elim }
  s

中文:
实例 :
  签名: 完备格 (筛 X)
  定义体: forall ⦃Y⦄ (f : Y ⟶ X), S f -> R f
  le_refl _ _ _ := id
  le_trans _ _ _ S₁₂ S₂₃ _ _ h := S₂₃ _ (S₁₂ _ h)
  le_antisymm _ _ p q := Sieve.ext fun _ _ => ⟨p _, q _⟩
  top :=
    { arrows := ⊤
      downward_closed := fun _ _ => ⟨⟩ }
  bot :=
    { arrows := ⊥
      downward_closed := False.elim }
  s
-/
instance : CompleteLattice (Sieve X) where
  le S R := forall ⦃Y⦄ (f : Y ⟶ X), S f -> R f
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
  isLUB_sSup _ := ⟨fun S hS _ _ hf => ⟨S, hS, hf⟩, fun _ ha _ _ ⟨b, hb, hf⟩ => ha hb _ hf⟩
  isGLB_sInf _ := ⟨fun S hS _ _ h => h _ hS, fun _ hS _ _ hf _ hR => hS hR _ hf⟩
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

/--
Instance `sieveInhabited` / 实例 `sieveInhabited`

English:
instance sieveInhabited
  signature: : Inhabited (Sieve X)
  body: ⟨⊤⟩

@[simp]

中文:
实例 sieveInhabited
  签名: : 可居 (筛 X)
  定义体: ⟨⊤⟩

@[simp]
-/
instance sieveInhabited : Inhabited (Sieve X) :=
  ⟨⊤⟩

@[simp]
/--
theorem `sInf_apply` / 定理 `sInf_apply`

English:
theorem sInf_apply
  given: {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X)
  proof: Iff.rfl

@[simp]

中文:
定理 sInf_apply
  条件: {Ss : 集合 (筛 X)} {Y} (f : Y ⟶ X)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem sInf_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sInf Ss f ↔ forall (S : Sieve X) (_ : S in Ss), S f :=
  Iff.rfl

@[simp]
/--
theorem `sSup_apply` / 定理 `sSup_apply`

English:
theorem sSup_apply
  given: {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X)
  proof: by
  simp [sSup, Sieve.sup]

@[simp]

中文:
定理 sSup_apply
  条件: {Ss : 集合 (筛 X)} {Y} (f : Y ⟶ X)
  证明: by
  simp [sSup, Sieve.sup]

@[simp]

Depends on / 依赖: Sieve.sup
-/
theorem sSup_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) :
    sSup Ss f ↔ exists (S : Sieve X) (_ : S in Ss), S f := by
  simp [sSup, Sieve.sup]

@[simp]
/--
theorem `inter_apply` / 定理 `inter_apply`

English:
theorem inter_apply
  given: {R S : Sieve X} {Y} (f : Y ⟶ X)
  statement: (R ⊓ S) f ↔ R f ∧ S f
  proof: Iff.rfl

@[simp]

中文:
定理 inter_apply
  条件: {R S : 筛 X} {Y} (f : Y ⟶ X)
  结论: (R ⊓ S) f ↔ R f ∧ S f
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem inter_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊓ S) f ↔ R f ∧ S f :=
  Iff.rfl

@[simp]
/--
theorem `union_apply` / 定理 `union_apply`

English:
theorem union_apply
  given: {R S : Sieve X} {Y} (f : Y ⟶ X)
  statement: (R ⊔ S) f ↔ R f ∨ S f
  proof: Iff.rfl

中文:
定理 union_apply
  条件: {R S : 筛 X} {Y} (f : Y ⟶ X)
  结论: (R ⊔ S) f ↔ R f ∨ S f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem union_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊔ S) f ↔ R f ∨ S f :=
  Iff.rfl

/--
theorem `top_apply` / 定理 `top_apply`

English:
theorem top_apply
  given: (f : Y ⟶ X)
  statement: (⊤ : Sieve X) f
  proof: trivial

@[simp]

中文:
定理 top_apply
  条件: (f : Y ⟶ X)
  结论: (⊤ : 筛 X) f
  证明: trivial

@[simp]
-/
theorem top_apply (f : Y ⟶ X) : (⊤ : Sieve X) f :=
  trivial

@[simp]
/--
theorem `bot_apply` / 定理 `bot_apply`

English:
theorem bot_apply
  given: (f : Y ⟶ X)
  statement: (⊥ : Sieve X) f ↔ False
  proof: .rfl

@[simp]

中文:
定理 bot_apply
  条件: (f : Y ⟶ X)
  结论: (⊥ : 筛 X) f ↔ 假
  证明: .rfl

@[simp]
-/
theorem bot_apply (f : Y ⟶ X) : (⊥ : Sieve X) f ↔ False :=
  .rfl

@[simp]
/--
lemma `arrows_top` / 引理 `arrows_top`

English:
lemma arrows_top
  statement: (⊤ : Sieve X).arrows = ⊤
  proof: rfl

中文:
引理 arrows_top
  结论: (⊤ : 筛 X).arrows = ⊤
  证明: rfl
-/
lemma arrows_top : (⊤ : Sieve X).arrows = ⊤ := rfl

/--
lemma `arrows_eq_top_iff` / 引理 `arrows_eq_top_iff`

English:
lemma arrows_eq_top_iff
  given: {S : Sieve X}
  statement: S.arrows = ⊤ ↔ S = ⊤
  proof: ⟨fun h => arrows_ext (h ▸ arrows_top), fun h => h ▸ arrows_top⟩

@[simp]

中文:
引理 arrows_eq_top_iff
  条件: {S : 筛 X}
  结论: S.arrows = ⊤ ↔ S = ⊤
  证明: ⟨fun h => arrows_ext (h ▸ arrows_top), fun h => h ▸ arrows_top⟩

@[simp]

Depends on / 依赖: arrows_ext, arrows_top
-/
lemma arrows_eq_top_iff {S : Sieve X} : S.arrows = ⊤ ↔ S = ⊤ :=
  ⟨fun h => arrows_ext (h ▸ arrows_top), fun h => h ▸ arrows_top⟩

@[simp]
/--
lemma `arrows_bot` / 引理 `arrows_bot`

English:
lemma arrows_bot
  statement: (⊥ : Sieve X).arrows = ⊥
  proof: rfl

中文:
引理 arrows_bot
  结论: (⊥ : 筛 X).arrows = ⊥
  证明: rfl
-/
lemma arrows_bot : (⊥ : Sieve X).arrows = ⊥ := rfl

/--
lemma `arrows_eq_bot_iff` / 引理 `arrows_eq_bot_iff`

English:
lemma arrows_eq_bot_iff
  given: {S : Sieve X}
  statement: S.arrows = ⊥ ↔ S = ⊥
  proof: ⟨fun h => arrows_ext (h ▸ arrows_bot), fun h => h ▸ arrows_bot⟩

中文:
引理 arrows_eq_bot_iff
  条件: {S : 筛 X}
  结论: S.arrows = ⊥ ↔ S = ⊥
  证明: ⟨fun h => arrows_ext (h ▸ arrows_bot), fun h => h ▸ arrows_bot⟩

Depends on / 依赖: arrows_bot, arrows_ext
-/
lemma arrows_eq_bot_iff {S : Sieve X} : S.arrows = ⊥ ↔ S = ⊥ :=
  ⟨fun h => arrows_ext (h ▸ arrows_bot), fun h => h ▸ arrows_bot⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial (Sieve X)
  body: ⟨⊤, ⊥, fun h => by simp [← bot_apply (𝟙 X), ← h]⟩

中文:
实例 :
  签名: 非平凡 (筛 X)
  定义体: ⟨⊤, ⊥, fun h => by simp [← bot_apply (𝟙 X), ← h]⟩

Depends on / 依赖: bot_apply
-/
instance : Nontrivial (Sieve X) where
  exists_pair_ne := ⟨⊤, ⊥, fun h => by simp [← bot_apply (𝟙 X), ← h]⟩

/-- Generate the smallest sieve containing the given presieve. -/
@[simps]
/--
Definition of `generate` / `generate` 的定义

English:
definition generate
  signature: (R : Presieve X)
  body: exists (Y : _) (h : Z ⟶ Y) (g : Y ⟶ X), R g ∧ h ≫ g = f
  downward_closed := by
    rintro Y Z _ ⟨W, g, f, hf, rfl⟩ h
    exact ⟨_, h ≫ g, _, hf, by simp⟩

中文:
定义 generate
  签名: (R : Presieve X)
  定义体: exists (Y : _) (h : Z ⟶ Y) (g : Y ⟶ X), R g ∧ h ≫ g = f
  downward_closed := by
    rintro Y Z _ ⟨W, g, f, hf, rfl⟩ h
    exact ⟨_, h ≫ g, _, hf, by simp⟩
-/
def generate (R : Presieve X) : Sieve X where
  arrows Z f := exists (Y : _) (h : Z ⟶ Y) (g : Y ⟶ X), R g ∧ h ≫ g = f
  downward_closed := by
    rintro Y Z _ ⟨W, g, f, hf, rfl⟩ h
    exact ⟨_, h ≫ g, _, hf, by simp⟩

/--
theorem `arrows_generate_map_eq_functorPushforward` / 定理 `arrows_generate_map_eq_functorPushforward`

English:
theorem arrows_generate_map_eq_functorPushforward
  given: {s : Presieve X}
  proof: by
  refine funext fun Z => funext fun u => propext ⟨?_, ?_⟩
  · rintro ⟨_, _, _, ⟨hu⟩, rfl⟩; exact ⟨_, _, _, hu, rfl⟩
  · rintro ⟨_, _, _, hu, rfl⟩; exact ⟨_, _, _, ⟨hu⟩, rfl⟩

中文:
定理 arrows_generate_map_eq_functorPushforward
  条件: {s : Presieve X}
  证明: by
  refine funext fun Z => funext fun u => propext ⟨?_, ?_⟩
  · rintro ⟨_, _, _, ⟨hu⟩, rfl⟩; exact ⟨_, _, _, hu, rfl⟩
  · rintro ⟨_, _, _, hu, rfl⟩; exact ⟨_, _, _, ⟨hu⟩, rfl⟩

Depends on / 依赖: propext
-/
theorem arrows_generate_map_eq_functorPushforward {s : Presieve X} :
    (generate (s.map F)).arrows = s.functorPushforward F := by
  refine funext fun Z => funext fun u => propext ⟨?_, ?_⟩
  · rintro ⟨_, _, _, ⟨hu⟩, rfl⟩; exact ⟨_, _, _, hu, rfl⟩
  · rintro ⟨_, _, _, hu, rfl⟩; exact ⟨_, _, _, ⟨hu⟩, rfl⟩

/-- Given a presieve on `X`, and a sieve on each domain of an arrow in the presieve, we can bind to
produce a sieve on `X`.
-/
@[simps]
/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y)
  body: S.bind fun _ _ h => R h
  downward_closed := by
    rintro Y Z f ⟨W, f, h, hh, hf, rfl⟩ g
    exact ⟨_, g ≫ f, _, hh, by simp [hf]⟩

中文:
定义 bind
  签名: (S : Presieve X) (R : 对任意 ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> 筛 Y)
  定义体: S.bind fun _ _ h => R h
  downward_closed := by
    rintro Y Z f ⟨W, f, h, hh, hf, rfl⟩ g
    exact ⟨_, g ≫ f, _, hh, by simp [hf]⟩

Depends on / 依赖: S.bind
-/
def bind (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) : Sieve X where
  arrows := S.bind fun _ _ h => R h
  downward_closed := by
    rintro Y Z f ⟨W, f, h, hh, hf, rfl⟩ g
    exact ⟨_, g ≫ f, _, hh, by simp [hf]⟩

/--
Definition of `BindStruct` / `BindStruct` 的定义

English:
abbreviation BindStruct
  signature: (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y)
  body: Presieve.BindStruct S (fun _ _ hf => R hf) h

中文:
缩写 BindStruct
  签名: (S : Presieve X) (R : 对任意 ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> 筛 Y)
  定义体: Presieve.BindStruct S (fun _ _ hf => R hf) h

Depends on / 依赖: BindStruct, Presieve, Presieve.BindStruct
-/
abbrev BindStruct (S : Presieve X) (R : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y)
    {Z : C} (h : Z ⟶ X) :=
  Presieve.BindStruct S (fun _ _ hf => R hf) h

open Order Lattice

/--
theorem `generate_le_iff` / 定理 `generate_le_iff`

English:
theorem generate_le_iff
  given: (R : Presieve X) (S : Sieve X)
  statement: generate R <= S ↔ R <= S
  proof: ⟨fun H _ _ hg => H _ ⟨_, 𝟙 _, _, hg, id_comp _⟩, fun ss Y f => by
    rintro ⟨Z, f, g, hg, rfl⟩
    exact S.downward_closed (ss Z _ hg) f⟩

中文:
定理 generate_le_iff
  条件: (R : Presieve X) (S : 筛 X)
  结论: generate R <= S ↔ R <= S
  证明: ⟨fun H _ _ hg => H _ ⟨_, 𝟙 _, _, hg, id_comp _⟩, fun ss Y f => by
    rintro ⟨Z, f, g, hg, rfl⟩
    exact S.downward_closed (ss Z _ hg) f⟩

Depends on / 依赖: S.downward_closed, downward_closed, id_comp
-/
theorem generate_le_iff (R : Presieve X) (S : Sieve X) : generate R <= S ↔ R <= S :=
  ⟨fun H _ _ hg => H _ ⟨_, 𝟙 _, _, hg, id_comp _⟩, fun ss Y f => by
    rintro ⟨Z, f, g, hg, rfl⟩
    exact S.downward_closed (ss Z _ hg) f⟩

/--
Definition of `giGenerate` / `giGenerate` 的定义

English:
definition giGenerate
  signature: : GaloisInsertion (generate : Presieve X -> Sieve X) arrows where
  body: generate_le_iff
  choice 𝒢 _ := generate 𝒢
  choice_eq _ _ := rfl
  le_l_u _ _ _ hf := ⟨_, 𝟙 _, _, hf, id_comp _⟩

中文:
定义 giGenerate
  签名: : Galois嵌入 (generate : Presieve X -> 筛 X) arrows where
  定义体: generate_le_iff
  choice 𝒢 _ := generate 𝒢
  choice_eq _ _ := rfl
  le_l_u _ _ _ hf := ⟨_, 𝟙 _, _, hf, id_comp _⟩

Depends on / 依赖: generate_le_iff
-/
def giGenerate : GaloisInsertion (generate : Presieve X -> Sieve X) arrows where
  gc := generate_le_iff
  choice 𝒢 _ := generate 𝒢
  choice_eq _ _ := rfl
  le_l_u _ _ _ hf := ⟨_, 𝟙 _, _, hf, id_comp _⟩

/--
theorem `le_generate` / 定理 `le_generate`

English:
theorem le_generate
  given: (R : Presieve X)
  statement: R <= generate R
  proof: giGenerate.gc.le_u_l R

@[simp]

中文:
定理 le_generate
  条件: (R : Presieve X)
  结论: R <= generate R
  证明: giGenerate.gc.le_u_l R

@[simp]

Depends on / 依赖: giGenerate, giGenerate.gc.le_u_l, le_u_l
-/
theorem le_generate (R : Presieve X) : R <= generate R :=
  giGenerate.gc.le_u_l R

@[simp]
/--
theorem `generate_sieve` / 定理 `generate_sieve`

English:
theorem generate_sieve
  given: (S : Sieve X)
  statement: generate S = S
  proof: giGenerate.l_u_eq S

@[gcongr]

中文:
定理 generate_sieve
  条件: (S : 筛 X)
  结论: generate S = S
  证明: giGenerate.l_u_eq S

@[gcongr]

Depends on / 依赖: giGenerate, giGenerate.l_u_eq, l_u_eq
-/
theorem generate_sieve (S : Sieve X) : generate S = S :=
  giGenerate.l_u_eq S

@[gcongr]
/--
theorem `generate_mono` / 定理 `generate_mono`

English:
theorem generate_mono
  statement: Monotone (generate : Presieve X -> Sieve X)
  proof: giGenerate.gc.monotone_l

@[gcongr]

中文:
定理 generate_mono
  结论: 递增 (generate : Presieve X -> 筛 X)
  证明: giGenerate.gc.monotone_l

@[gcongr]

Depends on / 依赖: giGenerate, giGenerate.gc.monotone_l, monotone_l
-/
theorem generate_mono : Monotone (generate : Presieve X -> Sieve X) := giGenerate.gc.monotone_l

@[gcongr]
/--
theorem `arrows_mono` / 定理 `arrows_mono`

English:
theorem arrows_mono
  statement: Monotone (arrows : Sieve X -> Presieve X)
  proof: giGenerate.gc.monotone_u

中文:
定理 arrows_mono
  结论: 递增 (arrows : 筛 X -> Presieve X)
  证明: giGenerate.gc.monotone_u

Depends on / 依赖: giGenerate, giGenerate.gc.monotone_u, monotone_u
-/
theorem arrows_mono : Monotone (arrows : Sieve X -> Presieve X) := giGenerate.gc.monotone_u

/--
theorem `id_mem_iff_eq_top` / 定理 `id_mem_iff_eq_top`

English:
theorem id_mem_iff_eq_top
  statement: S (𝟙 X) ↔ S = ⊤
  proof: ⟨fun h => top_unique fun Y f _ => by simpa using downward_closed _ h f, fun h => h.symm ▸ trivial⟩

中文:
定理 id_mem_iff_eq_top
  结论: S (𝟙 X) ↔ S = ⊤
  证明: ⟨fun h => top_unique fun Y f _ => by simpa using downward_closed _ h f, fun h => h.symm ▸ trivial⟩

Depends on / 依赖: downward_closed, h.symm, top_unique
-/
theorem id_mem_iff_eq_top : S (𝟙 X) ↔ S = ⊤ :=
  ⟨fun h => top_unique fun Y f _ => by simpa using downward_closed _ h f, fun h => h.symm ▸ trivial⟩

/--
theorem `generate_of_contains_isSplitEpi` / 定理 `generate_of_contains_isSplitEpi`

English:
theorem generate_of_contains_isSplitEpi
  given: {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f)
  proof: by
  rw [← id_mem_iff_eq_top]
  exact ⟨_, section_ f, f, hf, by simp⟩

@[simp]

中文:
定理 generate_of_contains_isSplitEpi
  条件: {R : Presieve X} (f : Y ⟶ X) [是分裂满态射 f] (hf : R f)
  证明: by
  rw [← id_mem_iff_eq_top]
  exact ⟨_, section_ f, f, hf, by simp⟩

@[simp]

Depends on / 依赖: id_mem_iff_eq_top, section_
-/
theorem generate_of_contains_isSplitEpi {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f) :
    generate R = ⊤ := by
  rw [← id_mem_iff_eq_top]
  exact ⟨_, section_ f, f, hf, by simp⟩

@[simp]
/--
theorem `generate_of_singleton_isSplitEpi` / 定理 `generate_of_singleton_isSplitEpi`

English:
theorem generate_of_singleton_isSplitEpi
  given: (f : Y ⟶ X) [IsSplitEpi f]
  proof: generate_of_contains_isSplitEpi f (Presieve.singleton_self _)

@[simp]

中文:
定理 generate_of_singleton_isSplitEpi
  条件: (f : Y ⟶ X) [是分裂满态射 f]
  证明: generate_of_contains_isSplitEpi f (Presieve.singleton_self _)

@[simp]

Depends on / 依赖: Presieve, Presieve.singleton_self, generate_of_contains_isSplitEpi, singleton_self
-/
theorem generate_of_singleton_isSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    generate (Presieve.singleton f) = ⊤ :=
  generate_of_contains_isSplitEpi f (Presieve.singleton_self _)

@[simp]
/--
theorem `generate_top` / 定理 `generate_top`

English:
theorem generate_top
  statement: generate (⊤ : Presieve X) = ⊤
  proof: generate_of_contains_isSplitEpi (𝟙 _) ⟨⟩

@[simp]

中文:
定理 generate_top
  结论: generate (⊤ : Presieve X) = ⊤
  证明: generate_of_contains_isSplitEpi (𝟙 _) ⟨⟩

@[simp]

Depends on / 依赖: generate_of_contains_isSplitEpi
-/
theorem generate_top : generate (⊤ : Presieve X) = ⊤ :=
  generate_of_contains_isSplitEpi (𝟙 _) ⟨⟩

@[simp]
/--
lemma `generate_bot` / 引理 `generate_bot`

English:
lemma generate_bot
  statement: generate (⊥ : Presieve X) = ⊥
  proof: by
  simp only [eq_bot_iff, generate_le_iff, bot_le]

@[simp]

中文:
引理 generate_bot
  结论: generate (⊥ : Presieve X) = ⊥
  证明: by
  simp only [eq_bot_iff, generate_le_iff, bot_le]

@[simp]

Depends on / 依赖: bot_le, eq_bot_iff, generate_le_iff
-/
lemma generate_bot : generate (⊥ : Presieve X) = ⊥ := by
  simp only [eq_bot_iff, generate_le_iff, bot_le]

@[simp]
/--
lemma `generate_eq_bot_iff` / 引理 `generate_eq_bot_iff`

English:
lemma generate_eq_bot_iff
  given: (R : Presieve X)
  statement: generate R = ⊥ ↔ R = ⊥
  proof: by
  simp [giGenerate.gc.l_eq_bot]

@[simp]

中文:
引理 generate_eq_bot_iff
  条件: (R : Presieve X)
  结论: generate R = ⊥ ↔ R = ⊥
  证明: by
  simp [giGenerate.gc.l_eq_bot]

@[simp]

Depends on / 依赖: giGenerate, giGenerate.gc.l_eq_bot, l_eq_bot
-/
lemma generate_eq_bot_iff (R : Presieve X) : generate R = ⊥ ↔ R = ⊥ := by
  simp [giGenerate.gc.l_eq_bot]

@[simp]
/--
lemma `comp_mem_iff` / 引理 `comp_mem_iff`

English:
lemma comp_mem_iff
  given: (i : X ⟶ Y) (f : Y ⟶ Z) [IsIso i] (S : Sieve Z)
  proof: by
  refine ⟨fun H => ?_, fun H => S.downward_closed H _⟩
  convert! S.downward_closed H (inv i)
  simp

中文:
引理 comp_mem_iff
  条件: (i : X ⟶ Y) (f : Y ⟶ Z) [是同构 i] (S : 筛 Z)
  证明: by
  refine ⟨fun H => ?_, fun H => S.downward_closed H _⟩
  convert! S.downward_closed H (inv i)
  simp

Depends on / 依赖: S.downward_closed, convert, downward_closed
-/
lemma comp_mem_iff (i : X ⟶ Y) (f : Y ⟶ Z) [IsIso i] (S : Sieve Z) :
    S (i ≫ f) ↔ S f := by
  refine ⟨fun H => ?_, fun H => S.downward_closed H _⟩
  convert! S.downward_closed H (inv i)
  simp

section

variable {I : Type*} {X : C} (Y : I -> C) (f : forall i, Y i ⟶ X)

/--
Definition of `ofArrows` / `ofArrows` 的定义

English:
abbreviation ofArrows
  signature: : Sieve X
  body: generate (Presieve.ofArrows Y f)

中文:
缩写 ofArrows
  签名: : 筛 X
  定义体: generate (Presieve.ofArrows Y f)

Depends on / 依赖: Presieve, Presieve.ofArrows, generate, ofArrows
-/
abbrev ofArrows : Sieve X := generate (Presieve.ofArrows Y f)

/--
lemma `ofArrows_mk` / 引理 `ofArrows_mk`

English:
lemma ofArrows_mk
  given: (i : I)
  statement: ofArrows Y f (f i)
  proof: ⟨_, 𝟙 _, _, ⟨i⟩, by simp⟩

中文:
引理 ofArrows_mk
  条件: (i : I)
  结论: ofArrows Y f (f i)
  证明: ⟨_, 𝟙 _, _, ⟨i⟩, by simp⟩
-/
lemma ofArrows_mk (i : I) : ofArrows Y f (f i) :=
  ⟨_, 𝟙 _, _, ⟨i⟩, by simp⟩

/--
lemma `mem_ofArrows_iff` / 引理 `mem_ofArrows_iff`

English:
lemma mem_ofArrows_iff
  given: {W : C} (g : W ⟶ X)
  proof: by
  constructor
  · rintro ⟨T, a, b, ⟨i⟩, rfl⟩
    exact ⟨i, a, rfl⟩
  · rintro ⟨i, a, rfl⟩
    apply downward_closed _ (ofArrows_mk Y f i)

中文:
引理 mem_ofArrows_iff
  条件: {W : C} (g : W ⟶ X)
  证明: by
  constructor
  · rintro ⟨T, a, b, ⟨i⟩, rfl⟩
    exact ⟨i, a, rfl⟩
  · rintro ⟨i, a, rfl⟩
    apply downward_closed _ (ofArrows_mk Y f i)

Depends on / 依赖: downward_closed, ofArrows_mk
-/
lemma mem_ofArrows_iff {W : C} (g : W ⟶ X) :
    ofArrows Y f g ↔ exists (i : I) (a : W ⟶ Y i), g = a ≫ f i := by
  constructor
  · rintro ⟨T, a, b, ⟨i⟩, rfl⟩
    exact ⟨i, a, rfl⟩
  · rintro ⟨i, a, rfl⟩
    apply downward_closed _ (ofArrows_mk Y f i)

variable {Y f} {W : C} {g : W ⟶ X} (hg : ofArrows Y f g)

include hg in
/--
lemma `ofArrows.exists` / 引理 `ofArrows.exists`

English:
lemma ofArrows.exists
  statement: exists (i : I) (h : W ⟶ Y i), g = h ≫ f i
  proof: by
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hg
  exact ⟨i, h, rfl⟩

中文:
引理 ofArrows.存在
  结论: 存在 (i : I) (h : W ⟶ Y i), g = h ≫ f i
  证明: by
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hg
  exact ⟨i, h, rfl⟩
-/
lemma ofArrows.exists : exists (i : I) (h : W ⟶ Y i), g = h ≫ f i := by
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hg
  exact ⟨i, h, rfl⟩

/--
Definition of `ofArrows.i` / `ofArrows.i` 的定义

English:
definition ofArrows.i
  signature: : I
  body: (ofArrows.exists hg).choose

中文:
定义 ofArrows.i
  签名: : I
  定义体: (ofArrows.exists hg).choose

Depends on / 依赖: ofArrows, ofArrows.exists
-/
noncomputable def ofArrows.i : I := (ofArrows.exists hg).choose

/--
Definition of `ofArrows.h` / `ofArrows.h` 的定义

English:
definition ofArrows.h
  signature: : W ⟶ Y (i hg)
  body: (ofArrows.exists hg).choose_spec.choose

@[reassoc (attr := simp)]

中文:
定义 ofArrows.h
  签名: : W ⟶ Y (i hg)
  定义体: (ofArrows.exists hg).choose_spec.choose

@[reassoc (attr := simp)]

Depends on / 依赖: choose_spec, choose_spec.choose, ofArrows, ofArrows.exists
-/
noncomputable def ofArrows.h : W ⟶ Y (i hg) := (ofArrows.exists hg).choose_spec.choose

@[reassoc (attr := simp)]
/--
lemma `ofArrows.fac` / 引理 `ofArrows.fac`

English:
lemma ofArrows.fac
  statement: h hg ≫ f (i hg) = g
  proof: (ofArrows.exists hg).choose_spec.choose_spec.symm

中文:
引理 ofArrows.fac
  结论: h hg ≫ f (i hg) = g
  证明: (ofArrows.exists hg).choose_spec.choose_spec.symm

Depends on / 依赖: choose_spec, choose_spec.choose_spec.symm, ofArrows, ofArrows.exists
-/
lemma ofArrows.fac : h hg ≫ f (i hg) = g :=
  (ofArrows.exists hg).choose_spec.choose_spec.symm

end

/--
lemma `ofArrows_category'` / 引理 `ofArrows_category'`

English:
lemma ofArrows_category'
  given: {S : C} (R : Presieve S)
  proof: by
  refine le_antisymm ?_ ?_
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨f, hf⟩
    exact ⟨_, 𝟙 _, f.hom, hf, by simp⟩
  · rintro _ _ ⟨_, a, b, h, rfl⟩
    exact ⟨_, _, _, .mk (ι := R.category) ⟨Over.mk b, h⟩, rfl⟩

中文:
引理 ofArrows_category'
  条件: {S : C} (R : Presieve S)
  证明: by
  refine le_antisymm ?_ ?_
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨f, hf⟩
    exact ⟨_, 𝟙 _, f.hom, hf, by simp⟩
  · rintro _ _ ⟨_, a, b, h, rfl⟩
    exact ⟨_, _, _, .mk (ι := R.category) ⟨Over.mk b, h⟩, rfl⟩

Depends on / 依赖: Over.mk, R.category, Sieve.generate_le_iff, category, f.hom, generate_le_iff, le_antisymm
-/
lemma ofArrows_category' {S : C} (R : Presieve S) :
    Sieve.ofArrows _ (fun (f : R.category) => f.obj.hom) = generate R := by
  refine le_antisymm ?_ ?_
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨f, hf⟩
    exact ⟨_, 𝟙 _, f.hom, hf, by simp⟩
  · rintro _ _ ⟨_, a, b, h, rfl⟩
    exact ⟨_, _, _, .mk (ι := R.category) ⟨Over.mk b, h⟩, rfl⟩

/--
lemma `ofArrows_category` / 引理 `ofArrows_category`

English:
lemma ofArrows_category
  given: {S : C} (R : Sieve S)
  proof: by
  rw [ofArrows_category']; rw [generate_sieve]

中文:
引理 ofArrows_category
  条件: {S : C} (R : 筛 S)
  证明: by
  rw [ofArrows_category']; rw [generate_sieve]

Depends on / 依赖: generate_sieve, ofArrows_category
-/
lemma ofArrows_category {S : C} (R : Sieve S) :
    Sieve.ofArrows _ (fun (f : R.arrows.category) => f.obj.hom) = R := by
  rw [ofArrows_category']; rw [generate_sieve]

/--
lemma `exists_eq_ofArrows` / 引理 `exists_eq_ofArrows`

English:
lemma exists_eq_ofArrows
  given: (R : Sieve X)
  proof: ⟨_, _, _, (ofArrows_category R).symm⟩

中文:
引理 存在_eq_ofArrows
  条件: (R : 筛 X)
  证明: ⟨_, _, _, (ofArrows_category R).symm⟩

Depends on / 依赖: ofArrows_category
-/
lemma exists_eq_ofArrows (R : Sieve X) :
    exists (I : Type max u₁ v₁) (Y : I -> C) (f : forall i, Y i ⟶ X),
      R = Sieve.ofArrows _ f :=
  ⟨_, _, _, (ofArrows_category R).symm⟩

/--
Definition of `ofTwoArrows` / `ofTwoArrows` 的定义

English:
abbreviation ofTwoArrows
  signature: {U V X : C} (i : U ⟶ X) (j : V ⟶ X)
  body: Sieve.ofArrows (Y := pairFunction U V) (fun k => WalkingPair.casesOn k i j)

中文:
缩写 ofTwoArrows
  签名: {U V X : C} (i : U ⟶ X) (j : V ⟶ X)
  定义体: Sieve.ofArrows (Y := pairFunction U V) (fun k => WalkingPair.casesOn k i j)

Depends on / 依赖: Sieve.ofArrows, WalkingPair, WalkingPair.casesOn, casesOn, ofArrows, pairFunction
-/
abbrev ofTwoArrows {U V X : C} (i : U ⟶ X) (j : V ⟶ X) : Sieve X :=
  Sieve.ofArrows (Y := pairFunction U V) (fun k => WalkingPair.casesOn k i j)

/--
Definition of `ofObjects` / `ofObjects` 的定义

English:
definition ofObjects
  signature: {I : Type*} (Y : I -> C) (X : C)
  body: exists (i : I), Nonempty (Z ⟶ Y i)
  downward_closed := by
    rintro Z₁ Z₂ p ⟨i, ⟨f⟩⟩ g
    exact ⟨i, ⟨g ≫ f⟩⟩

中文:
定义 ofObjects
  签名: {I : 类型} (Y : I -> C) (X : C)
  定义体: exists (i : I), Nonempty (Z ⟶ Y i)
  downward_closed := by
    rintro Z₁ Z₂ p ⟨i, ⟨f⟩⟩ g
    exact ⟨i, ⟨g ≫ f⟩⟩

Depends on / 依赖: Nonempty
-/
def ofObjects {I : Type*} (Y : I -> C) (X : C) : Sieve X where
  arrows Z _ := exists (i : I), Nonempty (Z ⟶ Y i)
  downward_closed := by
    rintro Z₁ Z₂ p ⟨i, ⟨f⟩⟩ g
    exact ⟨i, ⟨g ≫ f⟩⟩

/--
lemma `mem_ofObjects_iff` / 引理 `mem_ofObjects_iff`

English:
lemma mem_ofObjects_iff
  given: {I : Type*} (Y : I -> C) {Z X : C} (g : Z ⟶ X)
  proof: by rfl

中文:
引理 mem_ofObjects_iff
  条件: {I : 类型} (Y : I -> C) {Z X : C} (g : Z ⟶ X)
  证明: by rfl
-/
lemma mem_ofObjects_iff {I : Type*} (Y : I -> C) {Z X : C} (g : Z ⟶ X) :
    ofObjects Y X g ↔ exists (i : I), Nonempty (Z ⟶ Y i) := by rfl

/--
lemma `ofArrows_le_ofObjects` / 引理 `ofArrows_le_ofObjects`

English:
lemma ofArrows_le_ofObjects
  proof: by
  intro W g hg
  rw [mem_ofArrows_iff] at hg
  obtain ⟨i, a, rfl⟩ := hg
  exact ⟨i, ⟨a⟩⟩

中文:
引理 ofArrows_le_ofObjects
  证明: by
  intro W g hg
  rw [mem_ofArrows_iff] at hg
  obtain ⟨i, a, rfl⟩ := hg
  exact ⟨i, ⟨a⟩⟩

Depends on / 依赖: mem_ofArrows_iff
-/
lemma ofArrows_le_ofObjects
    {I : Type*} (Y : I -> C) {X : C} (f : forall i, Y i ⟶ X) :
    Sieve.ofArrows Y f <= Sieve.ofObjects Y X := by
  intro W g hg
  rw [mem_ofArrows_iff] at hg
  obtain ⟨i, a, rfl⟩ := hg
  exact ⟨i, ⟨a⟩⟩

/--
lemma `ofArrows_eq_ofObjects` / 引理 `ofArrows_eq_ofObjects`

English:
lemma ofArrows_eq_ofObjects
  statement: {X : C} (hX : IsTerminal X)
  proof: by
  refine le_antisymm (ofArrows_le_ofObjects Y f) (fun W g => ?_)
  rw [mem_ofArrows_iff]; rw [mem_ofObjects_iff]
  rintro ⟨i, ⟨h⟩⟩
  exact ⟨i, h, hX.hom_ext _ _⟩

中文:
引理 ofArrows_eq_ofObjects
  结论: {X : C} (hX : 是终止 X)
  证明: by
  refine le_antisymm (ofArrows_le_ofObjects Y f) (fun W g => ?_)
  rw [mem_ofArrows_iff]; rw [mem_ofObjects_iff]
  rintro ⟨i, ⟨h⟩⟩
  exact ⟨i, h, hX.hom_ext _ _⟩

Depends on / 依赖: hX.hom_ext, hom_ext, le_antisymm, mem_ofArrows_iff, mem_ofObjects_iff, ofArrows_le_ofObjects
-/
lemma ofArrows_eq_ofObjects {X : C} (hX : IsTerminal X)
    {I : Type*} (Y : I -> C) (f : forall i, Y i ⟶ X) :
    ofArrows Y f = ofObjects Y X := by
  refine le_antisymm (ofArrows_le_ofObjects Y f) (fun W g => ?_)
  rw [mem_ofArrows_iff]; rw [mem_ofObjects_iff]
  rintro ⟨i, ⟨h⟩⟩
  exact ⟨i, h, hX.hom_ext _ _⟩

/--
lemma `ofObjects_mono` / 引理 `ofObjects_mono`

English:
lemma ofObjects_mono
  statement: {I : Type*} {X : I -> C} {I' : Type*} {X' : I' -> C} {Y : C}
  proof: by
  rintro Z f ⟨i, ⟨g⟩⟩
  obtain ⟨i', h⟩ := h ⟨i, rfl⟩
  exact ⟨i', ⟨h ▸ g⟩⟩

中文:
引理 ofObjects_mono
  结论: {I : 类型} {X : I -> C} {I' : 类型} {X' : I' -> C} {Y : C}
  证明: by
  rintro Z f ⟨i, ⟨g⟩⟩
  obtain ⟨i', h⟩ := h ⟨i, rfl⟩
  exact ⟨i', ⟨h ▸ g⟩⟩
-/
lemma ofObjects_mono {I : Type*} {X : I -> C} {I' : Type*} {X' : I' -> C} {Y : C}
    (h : Set.range X subseteq Set.range X') :
    Sieve.ofObjects X Y <= Sieve.ofObjects X' Y := by
  rintro Z f ⟨i, ⟨g⟩⟩
  obtain ⟨i', h⟩ := h ⟨i, rfl⟩
  exact ⟨i', ⟨h ▸ g⟩⟩

/-- Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
as the inverse image of S with `_ ≫ h`. That is, `Sieve.pullback S h := (≫ h) '⁻¹ S`. -/
@[simps]
/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: (h : Y ⟶ X) (S : Sieve X)
  body: S (sl ≫ h)
  downward_closed g := by simp [g]

@[simp]

中文:
定义 pullback
  签名: (h : Y ⟶ X) (S : 筛 X)
  定义体: S (sl ≫ h)
  downward_closed g := by simp [g]

@[simp]
-/
def pullback (h : Y ⟶ X) (S : Sieve X) : Sieve Y where
  arrows _ sl := S (sl ≫ h)
  downward_closed g := by simp [g]

@[simp]
/--
theorem `pullback_id` / 定理 `pullback_id`

English:
theorem pullback_id
  statement: S.pullback (𝟙 _) = S
  proof: by simp [Sieve.ext_iff]

@[simp]

中文:
定理 pullback_id
  结论: S.pullback (𝟙 _) = S
  证明: by simp [Sieve.ext_iff]

@[simp]

Depends on / 依赖: Sieve.ext_iff, ext_iff
-/
theorem pullback_id : S.pullback (𝟙 _) = S := by simp [Sieve.ext_iff]

@[simp]
/--
theorem `pullback_top` / 定理 `pullback_top`

English:
theorem pullback_top
  given: {f : Y ⟶ X}
  statement: (⊤ : Sieve X).pullback f = ⊤
  proof: top_unique fun _ _ => id

中文:
定理 pullback_top
  条件: {f : Y ⟶ X}
  结论: (⊤ : 筛 X).pullback f = ⊤
  证明: top_unique fun _ _ => id

Depends on / 依赖: top_unique
-/
theorem pullback_top {f : Y ⟶ X} : (⊤ : Sieve X).pullback f = ⊤ :=
  top_unique fun _ _ => id

/--
theorem `pullback_comp` / 定理 `pullback_comp`

English:
theorem pullback_comp
  given: {f : Y ⟶ X} {g : Z ⟶ Y} (S : Sieve X)
  proof: by simp [Sieve.ext_iff]

@[simp]

中文:
定理 pullback_comp
  条件: {f : Y ⟶ X} {g : Z ⟶ Y} (S : 筛 X)
  证明: by simp [Sieve.ext_iff]

@[simp]

Depends on / 依赖: Sieve.ext_iff, ext_iff
-/
theorem pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : Sieve X) :
    S.pullback (g ≫ f) = (S.pullback f).pullback g := by simp [Sieve.ext_iff]

@[simp]
/--
theorem `pullback_inter` / 定理 `pullback_inter`

English:
theorem pullback_inter
  given: {f : Y ⟶ X} (S R : Sieve X)
  proof: by simp [Sieve.ext_iff]

中文:
定理 pullback_inter
  条件: {f : Y ⟶ X} (S R : 筛 X)
  证明: by simp [Sieve.ext_iff]

Depends on / 依赖: Sieve.ext_iff, ext_iff
-/
theorem pullback_inter {f : Y ⟶ X} (S R : Sieve X) :
    (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f := by simp [Sieve.ext_iff]

/--
lemma `pullback_ofArrows_of_iso` / 引理 `pullback_ofArrows_of_iso`

English:
lemma pullback_ofArrows_of_iso
  proof: by
  rw [Sieve.ext_iff]
  intro W a
  constructor
  · rintro ⟨T, b, c, ⟨i⟩, fac⟩
    exact ⟨_, b, _, ⟨i⟩, by simp [reassoc_of% fac]⟩
  · rintro ⟨_, a, _, ⟨i⟩, rfl⟩
    exact ⟨_, a, _, ⟨i⟩, by simp⟩

中文:
引理 pullback_ofArrows_of_iso
  证明: by
  rw [Sieve.ext_iff]
  intro W a
  constructor
  · rintro ⟨T, b, c, ⟨i⟩, fac⟩
    exact ⟨_, b, _, ⟨i⟩, by simp [reassoc_of% fac]⟩
  · rintro ⟨_, a, _, ⟨i⟩, rfl⟩
    exact ⟨_, a, _, ⟨i⟩, by simp⟩

Depends on / 依赖: Sieve.ext_iff, ext_iff, reassoc_of
-/
lemma pullback_ofArrows_of_iso
    {I : Type*} {X : C} (Z : I -> C) (f : forall i, Z i ⟶ X) {X' : C} (e : X' ≅ X) :
    pullback e.hom (Sieve.ofArrows _ f) =
      Sieve.ofArrows _ (fun i => f i ≫ e.inv) := by
  rw [Sieve.ext_iff]
  intro W a
  constructor
  · rintro ⟨T, b, c, ⟨i⟩, fac⟩
    exact ⟨_, b, _, ⟨i⟩, by simp [reassoc_of% fac]⟩
  · rintro ⟨_, a, _, ⟨i⟩, rfl⟩
    exact ⟨_, a, _, ⟨i⟩, by simp⟩

/--
theorem `mem_iff_pullback_eq_top` / 定理 `mem_iff_pullback_eq_top`

English:
theorem mem_iff_pullback_eq_top
  given: (f : Y ⟶ X)
  statement: S f ↔ S.pullback f = ⊤
  proof: by
  rw [← id_mem_iff_eq_top]; rw [pullback_apply]; rw [id_comp]

中文:
定理 mem_iff_pullback_eq_top
  条件: (f : Y ⟶ X)
  结论: S f ↔ S.pullback f = ⊤
  证明: by
  rw [← id_mem_iff_eq_top]; rw [pullback_apply]; rw [id_comp]

Depends on / 依赖: id_comp, id_mem_iff_eq_top, pullback_apply
-/
theorem mem_iff_pullback_eq_top (f : Y ⟶ X) : S f ↔ S.pullback f = ⊤ := by
  rw [← id_mem_iff_eq_top]; rw [pullback_apply]; rw [id_comp]

/--
theorem `pullback_eq_top_of_mem` / 定理 `pullback_eq_top_of_mem`

English:
theorem pullback_eq_top_of_mem
  given: (S : Sieve X) {f : Y ⟶ X}
  statement: S f -> S.pullback f = ⊤
  proof: (mem_iff_pullback_eq_top f).1

中文:
定理 pullback_eq_top_of_mem
  条件: (S : 筛 X) {f : Y ⟶ X}
  结论: S f -> S.pullback f = ⊤
  证明: (mem_iff_pullback_eq_top f).1

Depends on / 依赖: mem_iff_pullback_eq_top
-/
theorem pullback_eq_top_of_mem (S : Sieve X) {f : Y ⟶ X} : S f -> S.pullback f = ⊤ :=
  (mem_iff_pullback_eq_top f).1

/--
lemma `pullback_ofObjects_eq_top` / 引理 `pullback_ofObjects_eq_top`

English:
lemma pullback_ofObjects_eq_top
  proof: by
  ext Z h
  simp only [top_apply, iff_true]
  rw [mem_ofObjects_iff]
  exact ⟨i, ⟨h ≫ g⟩⟩

@[simp]

中文:
引理 pullback_ofObjects_eq_top
  证明: by
  ext Z h
  simp only [top_apply, iff_true]
  rw [mem_ofObjects_iff]
  exact ⟨i, ⟨h ≫ g⟩⟩

@[simp]

Depends on / 依赖: iff_true, mem_ofObjects_iff, top_apply
-/
lemma pullback_ofObjects_eq_top
    {I : Type*} (Y : I -> C) {X : C} {i : I} (g : X ⟶ Y i) :
    ofObjects Y X = ⊤ := by
  ext Z h
  simp only [top_apply, iff_true]
  rw [mem_ofObjects_iff]
  exact ⟨i, ⟨h ≫ g⟩⟩

@[simp]
/--
lemma `pullback_ofObjects` / 引理 `pullback_ofObjects`

English:
lemma pullback_ofObjects
  given: {I : Type*} (X : I -> C) {Y Z : C} (f : Z ⟶ Y)
  proof: by
  ext
  simp [Sieve.ofObjects]

@[simp]

中文:
引理 pullback_ofObjects
  条件: {I : 类型} (X : I -> C) {Y Z : C} (f : Z ⟶ Y)
  证明: by
  ext
  simp [Sieve.ofObjects]

@[simp]

Depends on / 依赖: Sieve.ofObjects, ofObjects
-/
lemma pullback_ofObjects {I : Type*} (X : I -> C) {Y Z : C} (f : Z ⟶ Y) :
    (ofObjects X Y).pullback f = ofObjects X Z := by
  ext
  simp [Sieve.ofObjects]

@[simp]
/--
lemma `ofObjects_id` / 引理 `ofObjects_id`

English:
lemma ofObjects_id
  given: (X : C)
  statement: Sieve.ofObjects id X = ⊤
  proof: Sieve.pullback_ofObjects_eq_top _ (𝟙 _)

中文:
引理 ofObjects_id
  条件: (X : C)
  结论: 筛.ofObjects id X = ⊤
  证明: Sieve.pullback_ofObjects_eq_top _ (𝟙 _)

Depends on / 依赖: Sieve.pullback_ofObjects_eq_top, pullback_ofObjects_eq_top
-/
lemma ofObjects_id (X : C) : Sieve.ofObjects id X = ⊤ :=
  Sieve.pullback_ofObjects_eq_top _ (𝟙 _)

/-- Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X` is in the sieve if `gf`
factors through some `g : Z ⟶ Y` which is in `R`.
-/
@[simps]
/--
Definition of `pushforward` / `pushforward` 的定义

English:
definition pushforward
  signature: (f : Y ⟶ X) (R : Sieve Y)
  body: exists g, g ≫ f = gf ∧ R g
  downward_closed := fun ⟨j, k, z⟩ h => ⟨h ≫ j, by simp [k], by simp [z]⟩

中文:
定义 pushforward
  签名: (f : Y ⟶ X) (R : 筛 Y)
  定义体: exists g, g ≫ f = gf ∧ R g
  downward_closed := fun ⟨j, k, z⟩ h => ⟨h ≫ j, by simp [k], by simp [z]⟩
-/
def pushforward (f : Y ⟶ X) (R : Sieve Y) : Sieve X where
  arrows _ gf := exists g, g ≫ f = gf ∧ R g
  downward_closed := fun ⟨j, k, z⟩ h => ⟨h ≫ j, by simp [k], by simp [z]⟩

/--
theorem `pushforward_apply_comp` / 定理 `pushforward_apply_comp`

English:
theorem pushforward_apply_comp
  given: {R : Sieve Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y ⟶ X)
  proof: ⟨g, rfl, hg⟩

中文:
定理 pushforward_apply_comp
  条件: {R : 筛 Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y ⟶ X)
  证明: ⟨g, rfl, hg⟩
-/
theorem pushforward_apply_comp {R : Sieve Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y ⟶ X) :
    R.pushforward f (g ≫ f) :=
  ⟨g, rfl, hg⟩

/--
theorem `pushforward_comp` / 定理 `pushforward_comp`

English:
theorem pushforward_comp
  given: {f : Y ⟶ X} {g : Z ⟶ Y} (R : Sieve Z)
  proof: Sieve.ext fun W h =>
    ⟨fun ⟨f₁, hq, hf₁⟩ => ⟨f₁ ≫ g, by simpa, f₁, rfl, hf₁⟩, fun ⟨y, hy, z, hR, hz⟩ =>
      ⟨z, by rw [← Category.assoc, hR]; tauto⟩⟩

中文:
定理 pushforward_comp
  条件: {f : Y ⟶ X} {g : Z ⟶ Y} (R : 筛 Z)
  证明: Sieve.ext fun W h =>
    ⟨fun ⟨f₁, hq, hf₁⟩ => ⟨f₁ ≫ g, by simpa, f₁, rfl, hf₁⟩, fun ⟨y, hy, z, hR, hz⟩ =>
      ⟨z, by rw [← Category.assoc, hR]; tauto⟩⟩

Depends on / 依赖: Category, Category.assoc, Sieve.ext
-/
theorem pushforward_comp {f : Y ⟶ X} {g : Z ⟶ Y} (R : Sieve Z) :
    R.pushforward (g ≫ f) = (R.pushforward g).pushforward f :=
  Sieve.ext fun W h =>
    ⟨fun ⟨f₁, hq, hf₁⟩ => ⟨f₁ ≫ g, by simpa, f₁, rfl, hf₁⟩, fun ⟨y, hy, z, hR, hz⟩ =>
      ⟨z, by rw [← Category.assoc, hR]; tauto⟩⟩

/--
theorem `galoisConnection` / 定理 `galoisConnection`

English:
theorem galoisConnection
  given: (f : Y ⟶ X)
  statement: GaloisConnection (Sieve.pushforward f) (Sieve.pullback f)
  proof: fun _ _ => ⟨fun hR _ g hg => hR _ ⟨g, rfl, hg⟩, fun hS _ _ ⟨h, hg, hh⟩ => hg ▸ hS h hh⟩

中文:
定理 galoisConnection
  条件: (f : Y ⟶ X)
  结论: GaloisConnection (筛.pushforward f) (筛.pullback f)
  证明: fun _ _ => ⟨fun hR _ g hg => hR _ ⟨g, rfl, hg⟩, fun hS _ _ ⟨h, hg, hh⟩ => hg ▸ hS h hh⟩
-/
theorem galoisConnection (f : Y ⟶ X) : GaloisConnection (Sieve.pushforward f) (Sieve.pullback f) :=
  fun _ _ => ⟨fun hR _ g hg => hR _ ⟨g, rfl, hg⟩, fun hS _ _ ⟨h, hg, hh⟩ => hg ▸ hS h hh⟩

/--
theorem `pullback_monotone` / 定理 `pullback_monotone`

English:
theorem pullback_monotone
  given: (f : Y ⟶ X)
  statement: Monotone (Sieve.pullback f)
  proof: (galoisConnection f).monotone_u

中文:
定理 pullback_monotone
  条件: (f : Y ⟶ X)
  结论: 递增 (筛.pullback f)
  证明: (galoisConnection f).monotone_u

Depends on / 依赖: galoisConnection, monotone_u
-/
theorem pullback_monotone (f : Y ⟶ X) : Monotone (Sieve.pullback f) :=
  (galoisConnection f).monotone_u

/--
theorem `pushforward_monotone` / 定理 `pushforward_monotone`

English:
theorem pushforward_monotone
  given: (f : Y ⟶ X)
  statement: Monotone (Sieve.pushforward f)
  proof: (galoisConnection f).monotone_l

中文:
定理 pushforward_monotone
  条件: (f : Y ⟶ X)
  结论: 递增 (筛.pushforward f)
  证明: (galoisConnection f).monotone_l

Depends on / 依赖: galoisConnection, monotone_l
-/
theorem pushforward_monotone (f : Y ⟶ X) : Monotone (Sieve.pushforward f) :=
  (galoisConnection f).monotone_l

/--
theorem `le_pushforward_pullback` / 定理 `le_pushforward_pullback`

English:
theorem le_pushforward_pullback
  given: (f : Y ⟶ X) (R : Sieve Y)
  statement: R <= (R.pushforward f).pullback f
  proof: (galoisConnection f).le_u_l _

中文:
定理 le_pushforward_pullback
  条件: (f : Y ⟶ X) (R : 筛 Y)
  结论: R <= (R.pushforward f).pullback f
  证明: (galoisConnection f).le_u_l _

Depends on / 依赖: galoisConnection, le_u_l
-/
theorem le_pushforward_pullback (f : Y ⟶ X) (R : Sieve Y) : R <= (R.pushforward f).pullback f :=
  (galoisConnection f).le_u_l _

/--
theorem `pullback_pushforward_le` / 定理 `pullback_pushforward_le`

English:
theorem pullback_pushforward_le
  given: (f : Y ⟶ X) (R : Sieve X)
  statement: (R.pullback f).pushforward f <= R
  proof: (galoisConnection f).l_u_le _

中文:
定理 pullback_pushforward_le
  条件: (f : Y ⟶ X) (R : 筛 X)
  结论: (R.pullback f).pushforward f <= R
  证明: (galoisConnection f).l_u_le _

Depends on / 依赖: galoisConnection, l_u_le
-/
theorem pullback_pushforward_le (f : Y ⟶ X) (R : Sieve X) : (R.pullback f).pushforward f <= R :=
  (galoisConnection f).l_u_le _

/--
theorem `pushforward_union` / 定理 `pushforward_union`

English:
theorem pushforward_union
  given: {f : Y ⟶ X} (S R : Sieve Y)
  proof: (galoisConnection f).l_sup

@[simp]

中文:
定理 pushforward_union
  条件: {f : Y ⟶ X} (S R : 筛 Y)
  证明: (galoisConnection f).l_sup

@[simp]

Depends on / 依赖: galoisConnection, l_sup
-/
theorem pushforward_union {f : Y ⟶ X} (S R : Sieve Y) :
    (S ⊔ R).pushforward f = S.pushforward f ⊔ R.pushforward f :=
  (galoisConnection f).l_sup

@[simp]
/--
lemma `pullback_bot` / 引理 `pullback_bot`

English:
lemma pullback_bot
  given: (f : Y ⟶ X)
  statement: (⊥ : Sieve X).pullback f = ⊥
  proof: rfl

@[simp]

中文:
引理 pullback_bot
  条件: (f : Y ⟶ X)
  结论: (⊥ : 筛 X).pullback f = ⊥
  证明: rfl

@[simp]
-/
lemma pullback_bot (f : Y ⟶ X) : (⊥ : Sieve X).pullback f = ⊥ :=
  rfl

@[simp]
/--
lemma `pushforward_bot` / 引理 `pushforward_bot`

English:
lemma pushforward_bot
  given: (f : Y ⟶ X)
  statement: (⊥ : Sieve Y).pushforward f = ⊥
  proof: (galoisConnection f).l_bot

中文:
引理 pushforward_bot
  条件: (f : Y ⟶ X)
  结论: (⊥ : 筛 Y).pushforward f = ⊥
  证明: (galoisConnection f).l_bot

Depends on / 依赖: galoisConnection, l_bot
-/
lemma pushforward_bot (f : Y ⟶ X) : (⊥ : Sieve Y).pushforward f = ⊥ :=
  (galoisConnection f).l_bot

/--
lemma `pushforward_eq_bot_iff` / 引理 `pushforward_eq_bot_iff`

English:
lemma pushforward_eq_bot_iff
  given: {f : Y ⟶ X} {S : Sieve Y}
  statement: S.pushforward f = ⊥ ↔ S = ⊥
  proof: by
  simp [(galoisConnection f).l_eq_bot]

中文:
引理 pushforward_eq_bot_iff
  条件: {f : Y ⟶ X} {S : 筛 Y}
  结论: S.pushforward f = ⊥ ↔ S = ⊥
  证明: by
  simp [(galoisConnection f).l_eq_bot]

Depends on / 依赖: galoisConnection, l_eq_bot
-/
lemma pushforward_eq_bot_iff {f : Y ⟶ X} {S : Sieve Y} : S.pushforward f = ⊥ ↔ S = ⊥ := by
  simp [(galoisConnection f).l_eq_bot]

/--
theorem `pushforward_le_bind_of_mem` / 定理 `pushforward_le_bind_of_mem`

English:
theorem pushforward_le_bind_of_mem
  statement: (S : Presieve X) (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y)
  proof: by
  rintro Z _ ⟨g, rfl, hg⟩
  exact ⟨_, g, f, h, hg, rfl⟩

中文:
定理 pushforward_le_bind_of_mem
  结论: (S : Presieve X) (R : 对任意 ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> 筛 Y)
  证明: by
  rintro Z _ ⟨g, rfl, hg⟩
  exact ⟨_, g, f, h, hg, rfl⟩
-/
theorem pushforward_le_bind_of_mem (S : Presieve X) (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y)
    (f : Y ⟶ X) (h : S f) : (R h).pushforward f <= bind S R := by
  rintro Z _ ⟨g, rfl, hg⟩
  exact ⟨_, g, f, h, hg, rfl⟩

/--
theorem `le_pullback_bind` / 定理 `le_pullback_bind`

English:
theorem le_pullback_bind
  statement: (S : Presieve X) (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) (f : Y ⟶ X)
  proof: by
  rw [← galoisConnection f]
  apply pushforward_le_bind_of_mem

中文:
定理 le_pullback_bind
  结论: (S : Presieve X) (R : 对任意 ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> 筛 Y) (f : Y ⟶ X)
  证明: by
  rw [← galoisConnection f]
  apply pushforward_le_bind_of_mem

Depends on / 依赖: galoisConnection, pushforward_le_bind_of_mem
-/
theorem le_pullback_bind (S : Presieve X) (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) (f : Y ⟶ X)
    (h : S f) : R h <= (bind S R).pullback f := by
  rw [← galoisConnection f]
  apply pushforward_le_bind_of_mem

/--
Definition of `galoisCoinsertionOfMono` / `galoisCoinsertionOfMono` 的定义

English:
definition galoisCoinsertionOfMono
  signature: (f : Y ⟶ X) [Mono f]
  body: by
  apply (galoisConnection f).toGaloisCoinsertion
  rintro S Z g ⟨g₁, hf, hg₁⟩
  rw [cancel_mono f] at hf
  rwa [← hf]

中文:
定义 galoisCoinsertionOfMono
  签名: (f : Y ⟶ X) [单态射 f]
  定义体: by
  apply (galoisConnection f).toGaloisCoinsertion
  rintro S Z g ⟨g₁, hf, hg₁⟩
  rw [cancel_mono f] at hf
  rwa [← hf]

Depends on / 依赖: cancel_mono, galoisConnection, toGaloisCoinsertion
-/
def galoisCoinsertionOfMono (f : Y ⟶ X) [Mono f] :
    GaloisCoinsertion (Sieve.pushforward f) (Sieve.pullback f) := by
  apply (galoisConnection f).toGaloisCoinsertion
  rintro S Z g ⟨g₁, hf, hg₁⟩
  rw [cancel_mono f] at hf
  rwa [← hf]

/--
Definition of `galoisInsertionOfIsSplitEpi` / `galoisInsertionOfIsSplitEpi` 的定义

English:
definition galoisInsertionOfIsSplitEpi
  signature: (f : Y ⟶ X) [IsSplitEpi f]
  body: by
  apply (galoisConnection f).toGaloisInsertion
  intro S Z g hg
  exact ⟨g ≫ section_ f, by simpa⟩

中文:
定义 galoisInsertionOfIsSplitEpi
  签名: (f : Y ⟶ X) [是分裂满态射 f]
  定义体: by
  apply (galoisConnection f).toGaloisInsertion
  intro S Z g hg
  exact ⟨g ≫ section_ f, by simpa⟩

Depends on / 依赖: galoisConnection, section_, toGaloisInsertion
-/
def galoisInsertionOfIsSplitEpi (f : Y ⟶ X) [IsSplitEpi f] :
    GaloisInsertion (Sieve.pushforward f) (Sieve.pullback f) := by
  apply (galoisConnection f).toGaloisInsertion
  intro S Z g hg
  exact ⟨g ≫ section_ f, by simpa⟩

/--
theorem `pullbackArrows_comm` / 定理 `pullbackArrows_comm`

English:
theorem pullbackArrows_comm
  given: {X Y : C} (f : Y ⟶ X) (R : Presieve X) [R.HasPullbacks f]
  proof: by
  ext W g
  constructor
  · rintro ⟨_, h, k, ⟨W, g, hg⟩, rfl⟩
    have := R.hasPullback f hg
    rw [Sieve.pullback_apply]; rw [assoc]; rw [← pullback.condition]; rw [← assoc]
    exact Sieve.downward_closed _ (by exact Sieve.le_generate R W _ hg) (h ≫ pullback.fst g f)
  · rintro ⟨W, h, k, hk, c

中文:
定理 pullbackArrows_comm
  条件: {X Y : C} (f : Y ⟶ X) (R : Presieve X) [R.有Pullbacks f]
  证明: by
  ext W g
  constructor
  · rintro ⟨_, h, k, ⟨W, g, hg⟩, rfl⟩
    have := R.hasPullback f hg
    rw [Sieve.pullback_apply]; rw [assoc]; rw [← pullback.condition]; rw [← assoc]
    exact Sieve.downward_closed _ (by exact Sieve.le_generate R W _ hg) (h ≫ pullback.fst g f)
  · rintro ⟨W, h, k, hk, c

Depends on / 依赖: Presieve, Presieve.pullbackArrows.mk, R.hasPullback, Sieve.downward_closed, Sieve.le_generate, Sieve.pullback_apply, condition, downward_closed, hasPullback, le_generate, lift_snd, pullback, pullback.condition, pullback.fst, pullback.lift_snd, pullbackArrows, pullback_apply
-/
theorem pullbackArrows_comm {X Y : C} (f : Y ⟶ X) (R : Presieve X) [R.HasPullbacks f] :
    Sieve.generate (R.pullbackArrows f) = (Sieve.generate R).pullback f := by
  ext W g
  constructor
  · rintro ⟨_, h, k, ⟨W, g, hg⟩, rfl⟩
    have := R.hasPullback f hg
    rw [Sieve.pullback_apply]; rw [assoc]; rw [← pullback.condition]; rw [← assoc]
    exact Sieve.downward_closed _ (by exact Sieve.le_generate R W _ hg) (h ≫ pullback.fst g f)
  · rintro ⟨W, h, k, hk, comm⟩
    have := R.hasPullback f hk
    exact ⟨_, _, _, Presieve.pullbackArrows.mk _ _ hk, pullback.lift_snd _ _ comm⟩

/--
lemma `pullback_arrows` / 引理 `pullback_arrows`

English:
lemma pullback_arrows
  given: {X Y : C} (f : X ⟶ Y) (S : Sieve Y)
  proof: rfl

中文:
引理 pullback_arrows
  条件: {X Y : C} (f : X ⟶ Y) (S : 筛 Y)
  证明: rfl
-/
lemma pullback_arrows {X Y : C} (f : X ⟶ Y) (S : Sieve Y) :
    (S.pullback f).arrows = S.arrows.pullback f :=
  rfl

/--
lemma `pushforward_arrows` / 引理 `pushforward_arrows`

English:
lemma pushforward_arrows
  given: {X Y : C} (f : X ⟶ Y) (S : Sieve X)
  proof: rfl

中文:
引理 pushforward_arrows
  条件: {X Y : C} (f : X ⟶ Y) (S : 筛 X)
  证明: rfl
-/
lemma pushforward_arrows {X Y : C} (f : X ⟶ Y) (S : Sieve X) :
    (S.pushforward f).arrows = S.arrows.pushforward f :=
  rfl

/--
lemma `generate_pushforward` / 引理 `generate_pushforward`

English:
lemma generate_pushforward
  given: {X Y : C} (f : X ⟶ Y) (R : Presieve X)
  proof: by
  ext
  grind [generate_apply, Presieve.pushforward, pushforward_apply]

中文:
引理 generate_pushforward
  条件: {X Y : C} (f : X ⟶ Y) (R : Presieve X)
  证明: by
  ext
  grind [generate_apply, Presieve.pushforward, pushforward_apply]

Depends on / 依赖: Presieve, Presieve.pushforward, generate_apply, pushforward, pushforward_apply
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
/--
Definition of `functorPullback` / `functorPullback` 的定义

English:
definition functorPullback
  signature: (R : Sieve (F.obj X))
  body: Presieve.functorPullback F R
  downward_closed := by
    intro _ _ f hf g
    unfold Presieve.functorPullback
    rw [F.map_comp]
    exact R.downward_closed hf (F.map g)

@[simp]

中文:
定义 functorPullback
  签名: (R : 筛 (F.obj X))
  定义体: Presieve.functorPullback F R
  downward_closed := by
    intro _ _ f hf g
    unfold Presieve.functorPullback
    rw [F.map_comp]
    exact R.downward_closed hf (F.map g)

@[simp]

Depends on / 依赖: Presieve, Presieve.functorPullback, functorPullback
-/
def functorPullback (R : Sieve (F.obj X)) : Sieve X where
  arrows := Presieve.functorPullback F R
  downward_closed := by
    intro _ _ f hf g
    unfold Presieve.functorPullback
    rw [F.map_comp]
    exact R.downward_closed hf (F.map g)

@[simp]
/--
theorem `functorPullback_arrows` / 定理 `functorPullback_arrows`

English:
theorem functorPullback_arrows
  given: (R : Sieve (F.obj X))
  proof: rfl

@[simp]

中文:
定理 functorPullback_arrows
  条件: (R : 筛 (F.obj X))
  证明: rfl

@[simp]
-/
theorem functorPullback_arrows (R : Sieve (F.obj X)) :
    (R.functorPullback F).arrows = R.arrows.functorPullback F :=
  rfl

@[simp]
/--
theorem `functorPullback_id` / 定理 `functorPullback_id`

English:
theorem functorPullback_id
  given: (R : Sieve X)
  statement: R.functorPullback (𝟭 _) = R
  proof: by
  ext
  rfl

中文:
定理 functorPullback_id
  条件: (R : 筛 X)
  结论: R.functorPullback (𝟭 _) = R
  证明: by
  ext
  rfl
-/
theorem functorPullback_id (R : Sieve X) : R.functorPullback (𝟭 _) = R := by
  ext
  rfl

/--
theorem `functorPullback_comp` / 定理 `functorPullback_comp`

English:
theorem functorPullback_comp
  given: (R : Sieve ((F ⋙ G).obj X))
  proof: by
  ext
  rfl

中文:
定理 functorPullback_comp
  条件: (R : 筛 ((F ⋙ G).obj X))
  证明: by
  ext
  rfl
-/
theorem functorPullback_comp (R : Sieve ((F ⋙ G).obj X)) :
    R.functorPullback (F ⋙ G) = (R.functorPullback G).functorPullback F := by
  ext
  rfl

/--
lemma `generate_functorPullback_le` / 引理 `generate_functorPullback_le`

English:
lemma generate_functorPullback_le
  given: {X : C} (R : Presieve (F.obj X))
  proof: by
  rw [generate_le_iff]
  intro Z g hg
  exact le_generate _ _ _ hg

中文:
引理 generate_functorPullback_le
  条件: {X : C} (R : Presieve (F.obj X))
  证明: by
  rw [generate_le_iff]
  intro Z g hg
  exact le_generate _ _ _ hg

Depends on / 依赖: generate_le_iff, le_generate
-/
lemma generate_functorPullback_le {X : C} (R : Presieve (F.obj X)) :
     generate (R.functorPullback F) <= functorPullback F (generate R) := by
  rw [generate_le_iff]
  intro Z g hg
  exact le_generate _ _ _ hg

/--
lemma `functorPullback_pullback` / 引理 `functorPullback_pullback`

English:
lemma functorPullback_pullback
  given: {X Y : C} (f : X ⟶ Y) (S : Sieve (F.obj Y))
  proof: by
  ext
  simp

中文:
引理 functorPullback_pullback
  条件: {X Y : C} (f : X ⟶ Y) (S : 筛 (F.obj Y))
  证明: by
  ext
  simp
-/
lemma functorPullback_pullback {X Y : C} (f : X ⟶ Y) (S : Sieve (F.obj Y)) :
    functorPullback F (pullback (F.map f) S) = pullback f (functorPullback F S) := by
  ext
  simp

/--
theorem `functorPushforward_extend_eq` / 定理 `functorPushforward_extend_eq`

English:
theorem functorPushforward_extend_eq
  given: {R : Presieve X}
  proof: by
  funext Y
  ext f
  constructor
  · rintro ⟨X', g, f', ⟨X'', g', f'', h₁, rfl⟩, rfl⟩
    exact ⟨X'', f'', f' ≫ F.map g', h₁, by simp⟩
  · rintro ⟨X', g, f', h₁, h₂⟩
    exact ⟨X', g, f', le_generate R _ _ h₁, h₂⟩

中文:
定理 functorPushforward_extend_eq
  条件: {R : Presieve X}
  证明: by
  funext Y
  ext f
  constructor
  · rintro ⟨X', g, f', ⟨X'', g', f'', h₁, rfl⟩, rfl⟩
    exact ⟨X'', f'', f' ≫ F.map g', h₁, by simp⟩
  · rintro ⟨X', g, f', h₁, h₂⟩
    exact ⟨X', g, f', le_generate R _ _ h₁, h₂⟩

Depends on / 依赖: F.map, le_generate
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
/--
Definition of `functorPushforward` / `functorPushforward` 的定义

English:
definition functorPushforward
  signature: (R : Sieve X)
  body: R.arrows.functorPushforward F
  downward_closed := by
    intro _ _ f h g
    obtain ⟨X, α, β, hα, rfl⟩ := h
    exact ⟨X, α, g ≫ β, hα, by simp⟩

中文:
定义 functorPushforward
  签名: (R : 筛 X)
  定义体: R.arrows.functorPushforward F
  downward_closed := by
    intro _ _ f h g
    obtain ⟨X, α, β, hα, rfl⟩ := h
    exact ⟨X, α, g ≫ β, hα, by simp⟩

Depends on / 依赖: R.arrows.functorPushforward, arrows, functorPushforward
-/
def functorPushforward (R : Sieve X) : Sieve (F.obj X) where
  arrows := R.arrows.functorPushforward F
  downward_closed := by
    intro _ _ f h g
    obtain ⟨X, α, β, hα, rfl⟩ := h
    exact ⟨X, α, g ≫ β, hα, by simp⟩

/--
theorem `generate_map_eq_functorPushforward` / 定理 `generate_map_eq_functorPushforward`

English:
theorem generate_map_eq_functorPushforward
  given: {s : Presieve X}
  proof: by
  ext
  rw [arrows_generate_map_eq_functorPushforward]
  simp [functorPushforward_extend_eq]

中文:
定理 generate_map_eq_functorPushforward
  条件: {s : Presieve X}
  证明: by
  ext
  rw [arrows_generate_map_eq_functorPushforward]
  simp [functorPushforward_extend_eq]

Depends on / 依赖: arrows_generate_map_eq_functorPushforward, functorPushforward_extend_eq
-/
theorem generate_map_eq_functorPushforward {s : Presieve X} :
    generate (s.map F) = (generate s).functorPushforward F := by
  ext
  rw [arrows_generate_map_eq_functorPushforward]
  simp [functorPushforward_extend_eq]

/--
lemma `functorPushforward_ofArrows` / 引理 `functorPushforward_ofArrows`

English:
lemma functorPushforward_ofArrows
  given: {X : C} {ι : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X)
  proof: by
  rw [← generate_map_eq_functorPushforward]; rw [Presieve.map_ofArrows]

@[simp]

中文:
引理 functorPushforward_ofArrows
  条件: {X : C} {ι : 类型} {Y : ι -> C} (f : 对任意 i, Y i ⟶ X)
  证明: by
  rw [← generate_map_eq_functorPushforward]; rw [Presieve.map_ofArrows]

@[simp]

Depends on / 依赖: Presieve, Presieve.map_ofArrows, generate_map_eq_functorPushforward, map_ofArrows
-/
lemma functorPushforward_ofArrows {X : C} {ι : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X) :
    functorPushforward F (ofArrows Y f) = ofArrows _ fun i : ι => F.map (f i) := by
  rw [← generate_map_eq_functorPushforward]; rw [Presieve.map_ofArrows]

@[simp]
/--
theorem `functorPushforward_id` / 定理 `functorPushforward_id`

English:
theorem functorPushforward_id
  given: (R : Sieve X)
  statement: R.functorPushforward (𝟭 _) = R
  proof: by
  ext X f
  constructor
  · intro hf
    obtain ⟨X, g, h, hg, rfl⟩ := hf
    exact R.downward_closed hg h
  · intro hf
    exact ⟨X, f, 𝟙 _, hf, by simp⟩

中文:
定理 functorPushforward_id
  条件: (R : 筛 X)
  结论: R.functorPushforward (𝟭 _) = R
  证明: by
  ext X f
  constructor
  · intro hf
    obtain ⟨X, g, h, hg, rfl⟩ := hf
    exact R.downward_closed hg h
  · intro hf
    exact ⟨X, f, 𝟙 _, hf, by simp⟩

Depends on / 依赖: R.downward_closed, downward_closed
-/
theorem functorPushforward_id (R : Sieve X) : R.functorPushforward (𝟭 _) = R := by
  ext X f
  constructor
  · intro hf
    obtain ⟨X, g, h, hg, rfl⟩ := hf
    exact R.downward_closed hg h
  · intro hf
    exact ⟨X, f, 𝟙 _, hf, by simp⟩

/--
theorem `functorPushforward_comp` / 定理 `functorPushforward_comp`

English:
theorem functorPushforward_comp
  given: (R : Sieve X)
  proof: by
  ext
  simp [R.arrows.functorPushforward_comp F G]

中文:
定理 functorPushforward_comp
  条件: (R : 筛 X)
  证明: by
  ext
  simp [R.arrows.functorPushforward_comp F G]

Depends on / 依赖: R.arrows.functorPushforward_comp, arrows, functorPushforward_comp
-/
theorem functorPushforward_comp (R : Sieve X) :
    R.functorPushforward (F ⋙ G) = (R.functorPushforward F).functorPushforward G := by
  ext
  simp [R.arrows.functorPushforward_comp F G]

/--
theorem `functor_galoisConnection` / 定理 `functor_galoisConnection`

English:
theorem functor_galoisConnection
  given: (X : C)
  proof: by
  intro R S
  constructor
  · intro hle X f hf
    apply hle
    refine ⟨X, f, 𝟙 _, hf, ?_⟩
    rw [id_comp]
  · rintro hle Y f ⟨X, g, h, hg, rfl⟩
    apply Sieve.downward_closed S
    exact hle g hg

中文:
定理 functor_galoisConnection
  条件: (X : C)
  证明: by
  intro R S
  constructor
  · intro hle X f hf
    apply hle
    refine ⟨X, f, 𝟙 _, hf, ?_⟩
    rw [id_comp]
  · rintro hle Y f ⟨X, g, h, hg, rfl⟩
    apply Sieve.downward_closed S
    exact hle g hg

Depends on / 依赖: Sieve.downward_closed, downward_closed, id_comp
-/
theorem functor_galoisConnection (X : C) :
    GaloisConnection (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj X))
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

/--
lemma `functorPushforward_le_iff_le_functorPullback` / 引理 `functorPushforward_le_iff_le_functorPullback`

English:
lemma functorPushforward_le_iff_le_functorPullback
  given: {X : C} (S : Sieve X) (R : Sieve (F.obj X))
  proof: (Sieve.functor_galoisConnection F X).le_iff_le

中文:
引理 functorPushforward_le_iff_le_functorPullback
  条件: {X : C} (S : 筛 X) (R : 筛 (F.obj X))
  证明: (Sieve.functor_galoisConnection F X).le_iff_le

Depends on / 依赖: Sieve.functor_galoisConnection, functor_galoisConnection, le_iff_le
-/
lemma functorPushforward_le_iff_le_functorPullback {X : C} (S : Sieve X) (R : Sieve (F.obj X)) :
    S.functorPushforward F <= R ↔ S <= R.functorPullback F :=
  (Sieve.functor_galoisConnection F X).le_iff_le

/--
theorem `functorPullback_monotone` / 定理 `functorPullback_monotone`

English:
theorem functorPullback_monotone
  given: (X : C)
  proof: (functor_galoisConnection F X).monotone_u

中文:
定理 functorPullback_monotone
  条件: (X : C)
  证明: (functor_galoisConnection F X).monotone_u

Depends on / 依赖: functor_galoisConnection, monotone_u
-/
theorem functorPullback_monotone (X : C) :
    Monotone (Sieve.functorPullback F : Sieve (F.obj X) -> Sieve X) :=
  (functor_galoisConnection F X).monotone_u

/--
theorem `functorPushforward_monotone` / 定理 `functorPushforward_monotone`

English:
theorem functorPushforward_monotone
  given: (X : C)
  proof: (functor_galoisConnection F X).monotone_l

中文:
定理 functorPushforward_monotone
  条件: (X : C)
  证明: (functor_galoisConnection F X).monotone_l

Depends on / 依赖: functor_galoisConnection, monotone_l
-/
theorem functorPushforward_monotone (X : C) :
    Monotone (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj X)) :=
  (functor_galoisConnection F X).monotone_l

/--
theorem `le_functorPushforward_pullback` / 定理 `le_functorPushforward_pullback`

English:
theorem le_functorPushforward_pullback
  given: (R : Sieve X)
  proof: (functor_galoisConnection F X).le_u_l _

中文:
定理 le_functorPushforward_pullback
  条件: (R : 筛 X)
  证明: (functor_galoisConnection F X).le_u_l _

Depends on / 依赖: functor_galoisConnection, le_u_l
-/
theorem le_functorPushforward_pullback (R : Sieve X) :
    R <= (R.functorPushforward F).functorPullback F :=
  (functor_galoisConnection F X).le_u_l _

/--
theorem `functorPullback_pushforward_le` / 定理 `functorPullback_pushforward_le`

English:
theorem functorPullback_pushforward_le
  given: (R : Sieve (F.obj X))
  proof: (functor_galoisConnection F X).l_u_le _

中文:
定理 functorPullback_pushforward_le
  条件: (R : 筛 (F.obj X))
  证明: (functor_galoisConnection F X).l_u_le _

Depends on / 依赖: functor_galoisConnection, l_u_le
-/
theorem functorPullback_pushforward_le (R : Sieve (F.obj X)) :
    (R.functorPullback F).functorPushforward F <= R :=
  (functor_galoisConnection F X).l_u_le _

/--
theorem `functorPushforward_union` / 定理 `functorPushforward_union`

English:
theorem functorPushforward_union
  given: (S R : Sieve X)
  proof: (functor_galoisConnection F X).l_sup

中文:
定理 functorPushforward_union
  条件: (S R : 筛 X)
  证明: (functor_galoisConnection F X).l_sup

Depends on / 依赖: functor_galoisConnection, l_sup
-/
theorem functorPushforward_union (S R : Sieve X) :
    (S ⊔ R).functorPushforward F = S.functorPushforward F ⊔ R.functorPushforward F :=
  (functor_galoisConnection F X).l_sup

/--
theorem `functorPullback_union` / 定理 `functorPullback_union`

English:
theorem functorPullback_union
  given: (S R : Sieve (F.obj X))
  proof: rfl

中文:
定理 functorPullback_union
  条件: (S R : 筛 (F.obj X))
  证明: rfl
-/
theorem functorPullback_union (S R : Sieve (F.obj X)) :
    (S ⊔ R).functorPullback F = S.functorPullback F ⊔ R.functorPullback F :=
  rfl

/--
theorem `functorPullback_inter` / 定理 `functorPullback_inter`

English:
theorem functorPullback_inter
  given: (S R : Sieve (F.obj X))
  proof: rfl

@[simp]

中文:
定理 functorPullback_inter
  条件: (S R : 筛 (F.obj X))
  证明: rfl

@[simp]
-/
theorem functorPullback_inter (S R : Sieve (F.obj X)) :
    (S ⊓ R).functorPullback F = S.functorPullback F ⊓ R.functorPullback F :=
  rfl

@[simp]
/--
theorem `functorPushforward_bot` / 定理 `functorPushforward_bot`

English:
theorem functorPushforward_bot
  given: (F : C ⥤ D) (X : C)
  statement: (⊥ : Sieve X).functorPushforward F = ⊥
  proof: (functor_galoisConnection F X).l_bot

@[simp]

中文:
定理 functorPushforward_bot
  条件: (F : C ⥤ D) (X : C)
  结论: (⊥ : 筛 X).functorPushforward F = ⊥
  证明: (functor_galoisConnection F X).l_bot

@[simp]

Depends on / 依赖: functor_galoisConnection, l_bot
-/
theorem functorPushforward_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve X).functorPushforward F = ⊥ :=
  (functor_galoisConnection F X).l_bot

@[simp]
/--
theorem `functorPushforward_top` / 定理 `functorPushforward_top`

English:
theorem functorPushforward_top
  given: (F : C ⥤ D) (X : C)
  statement: (⊤ : Sieve X).functorPushforward F = ⊤
  proof: by
  refine (generate_sieve _).symm.trans ?_
  apply generate_of_contains_isSplitEpi (𝟙 (F.obj X))
  exact ⟨X, 𝟙 _, 𝟙 _, trivial, by simp⟩

@[simp]

中文:
定理 functorPushforward_top
  条件: (F : C ⥤ D) (X : C)
  结论: (⊤ : 筛 X).functorPushforward F = ⊤
  证明: by
  refine (generate_sieve _).symm.trans ?_
  apply generate_of_contains_isSplitEpi (𝟙 (F.obj X))
  exact ⟨X, 𝟙 _, 𝟙 _, trivial, by simp⟩

@[simp]

Depends on / 依赖: F.obj, generate_of_contains_isSplitEpi, generate_sieve, symm.trans
-/
theorem functorPushforward_top (F : C ⥤ D) (X : C) : (⊤ : Sieve X).functorPushforward F = ⊤ := by
  refine (generate_sieve _).symm.trans ?_
  apply generate_of_contains_isSplitEpi (𝟙 (F.obj X))
  exact ⟨X, 𝟙 _, 𝟙 _, trivial, by simp⟩

@[simp]
/--
theorem `functorPullback_bot` / 定理 `functorPullback_bot`

English:
theorem functorPullback_bot
  given: (F : C ⥤ D) (X : C)
  statement: (⊥ : Sieve (F.obj X)).functorPullback F = ⊥
  proof: rfl

@[simp]

中文:
定理 functorPullback_bot
  条件: (F : C ⥤ D) (X : C)
  结论: (⊥ : 筛 (F.obj X)).functorPullback F = ⊥
  证明: rfl

@[simp]
-/
theorem functorPullback_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve (F.obj X)).functorPullback F = ⊥ :=
  rfl

@[simp]
/--
theorem `functorPullback_top` / 定理 `functorPullback_top`

English:
theorem functorPullback_top
  given: (F : C ⥤ D) (X : C)
  statement: (⊤ : Sieve (F.obj X)).functorPullback F = ⊤
  proof: rfl

中文:
定理 functorPullback_top
  条件: (F : C ⥤ D) (X : C)
  结论: (⊤ : 筛 (F.obj X)).functorPullback F = ⊤
  证明: rfl
-/
theorem functorPullback_top (F : C ⥤ D) (X : C) : (⊤ : Sieve (F.obj X)).functorPullback F = ⊤ :=
  rfl

/--
theorem `image_mem_functorPushforward` / 定理 `image_mem_functorPushforward`

English:
theorem image_mem_functorPushforward
  given: (R : Sieve X) {V} {f : V ⟶ X} (h : R f)
  proof: ⟨V, f, 𝟙 _, h, by simp⟩

中文:
定理 image_mem_functorPushforward
  条件: (R : 筛 X) {V} {f : V ⟶ X} (h : R f)
  证明: ⟨V, f, 𝟙 _, h, by simp⟩
-/
theorem image_mem_functorPushforward (R : Sieve X) {V} {f : V ⟶ X} (h : R f) :
    R.functorPushforward F (F.map f) :=
  ⟨V, f, 𝟙 _, h, by simp⟩

/--
lemma `functorPushforward_pullback_le` / 引理 `functorPushforward_pullback_le`

English:
lemma functorPushforward_pullback_le
  given: {X Y : C} (f : Y ⟶ X) (S : Sieve X)
  proof: by
  rw [Sieve.functorPushforward_le_iff_le_functorPullback]; rw [Sieve.functorPullback_pullback]
  apply Sieve.pullback_monotone
  exact Sieve.le_functorPushforward_pullback _ _

中文:
引理 functorPushforward_pullback_le
  条件: {X Y : C} (f : Y ⟶ X) (S : 筛 X)
  证明: by
  rw [Sieve.functorPushforward_le_iff_le_functorPullback]; rw [Sieve.functorPullback_pullback]
  apply Sieve.pullback_monotone
  exact Sieve.le_functorPushforward_pullback _ _

Depends on / 依赖: Sieve.functorPullback_pullback, Sieve.functorPushforward_le_iff_le_functorPullback, Sieve.le_functorPushforward_pullback, Sieve.pullback_monotone, functorPullback_pullback, functorPushforward_le_iff_le_functorPullback, le_functorPushforward_pullback, pullback_monotone
-/
lemma functorPushforward_pullback_le {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    (S.pullback f).functorPushforward F <= (S.functorPushforward F).pullback (F.map f) := by
  rw [Sieve.functorPushforward_le_iff_le_functorPullback]; rw [Sieve.functorPullback_pullback]
  apply Sieve.pullback_monotone
  exact Sieve.le_functorPushforward_pullback _ _

/--
Definition of `essSurjFullFunctorGaloisInsertion` / `essSurjFullFunctorGaloisInsertion` 的定义

English:
definition essSurjFullFunctorGaloisInsertion
  signature: [F.EssSurj] [F.Full] (X : C)
  body: by
  apply (functor_galoisConnection F X).toGaloisInsertion
  intro S Y f hf
  refine ⟨_, F.preimage ((F.objObjPreimageIso Y).hom ≫ f), (F.objObjPreimageIso Y).inv, ?_⟩
  simpa using hf

中文:
定义 essSurjFullFunctorGaloisInsertion
  签名: [F.本质满射] [F.满] (X : C)
  定义体: by
  apply (functor_galoisConnection F X).toGaloisInsertion
  intro S Y f hf
  refine ⟨_, F.preimage ((F.objObjPreimageIso Y).hom ≫ f), (F.objObjPreimageIso Y).inv, ?_⟩
  simpa using hf

Depends on / 依赖: F.objObjPreimageIso, F.preimage, functor_galoisConnection, objObjPreimageIso, preimage, toGaloisInsertion
-/
def essSurjFullFunctorGaloisInsertion [F.EssSurj] [F.Full] (X : C) :
    GaloisInsertion (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  apply (functor_galoisConnection F X).toGaloisInsertion
  intro S Y f hf
  refine ⟨_, F.preimage ((F.objObjPreimageIso Y).hom ≫ f), (F.objObjPreimageIso Y).inv, ?_⟩
  simpa using hf

/--
Definition of `fullyFaithfulFunctorGaloisCoinsertion` / `fullyFaithfulFunctorGaloisCoinsertion` 的定义

English:
definition fullyFaithfulFunctorGaloisCoinsertion
  signature: [F.Full] [F.Faithful] (X : C)
  body: by
  apply (functor_galoisConnection F X).toGaloisCoinsertion
  rintro S Y f ⟨Z, g, h, h₁, h₂⟩
  rw [← F.map_preimage h]; rw [← F.map_comp] at h₂
  rw [F.map_injective h₂]
  exact S.downward_closed h₁ _

中文:
定义 fullyFaithfulFunctorGaloisCoinsertion
  签名: [F.满] [F.忠实] (X : C)
  定义体: by
  apply (functor_galoisConnection F X).toGaloisCoinsertion
  rintro S Y f ⟨Z, g, h, h₁, h₂⟩
  rw [← F.map_preimage h]; rw [← F.map_comp] at h₂
  rw [F.map_injective h₂]
  exact S.downward_closed h₁ _

Depends on / 依赖: F.map_comp, F.map_injective, F.map_preimage, S.downward_closed, downward_closed, functor_galoisConnection, map_comp, map_injective, map_preimage, toGaloisCoinsertion
-/
def fullyFaithfulFunctorGaloisCoinsertion [F.Full] [F.Faithful] (X : C) :
    GaloisCoinsertion (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj X))
      (Sieve.functorPullback F) := by
  apply (functor_galoisConnection F X).toGaloisCoinsertion
  rintro S Y f ⟨Z, g, h, h₁, h₂⟩
  rw [← F.map_preimage h]; rw [← F.map_comp] at h₂
  rw [F.map_injective h₂]
  exact S.downward_closed h₁ _

/--
lemma `functorPullback_functorPushforward_eq` / 引理 `functorPullback_functorPushforward_eq`

English:
lemma functorPullback_functorPushforward_eq
  given: {X : C} {S : Sieve X} [F.Full] [F.Faithful]
  proof: (Sieve.fullyFaithfulFunctorGaloisCoinsertion _ _).u_l_eq _

中文:
引理 functorPullback_functorPushforward_eq
  条件: {X : C} {S : 筛 X} [F.满] [F.忠实]
  证明: (Sieve.fullyFaithfulFunctorGaloisCoinsertion _ _).u_l_eq _

Depends on / 依赖: Sieve.fullyFaithfulFunctorGaloisCoinsertion, fullyFaithfulFunctorGaloisCoinsertion, u_l_eq
-/
lemma functorPullback_functorPushforward_eq {X : C} {S : Sieve X} [F.Full] [F.Faithful] :
    Sieve.functorPullback F (Sieve.functorPushforward F S) = S :=
  (Sieve.fullyFaithfulFunctorGaloisCoinsertion _ _).u_l_eq _

set_option backward.defeqAttrib.useBackward true in
/--
lemma `functorPushforward_functor` / 引理 `functorPushforward_functor`

English:
lemma functorPushforward_functor
  given: (S : Sieve X) (e : C ≌ D)
  proof: by
  ext Y iYX
  constructor
  · rintro ⟨Z, iZX, iYZ, hiZX, rfl⟩
    simpa using S.downward_closed hiZX (e.inverse.map iYZ ≫ e.unitInv.app Z)
  · intro H
    exact ⟨_, e.inverse.map iYX ≫ e.unitInv.app X, e.counitInv.app Y, by simpa using H, by simp⟩

@[simp]

中文:
引理 functorPushforward_functor
  条件: (S : 筛 X) (e : C ≌ D)
  证明: by
  ext Y iYX
  constructor
  · rintro ⟨Z, iZX, iYZ, hiZX, rfl⟩
    simpa using S.downward_closed hiZX (e.inverse.map iYZ ≫ e.unitInv.app Z)
  · intro H
    exact ⟨_, e.inverse.map iYX ≫ e.unitInv.app X, e.counitInv.app Y, by simpa using H, by simp⟩

@[simp]

Depends on / 依赖: S.downward_closed, counitInv, downward_closed, e.counitInv.app, e.inverse.map, e.unitInv.app, inverse, unitInv
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
/--
lemma `mem_functorPushforward_functor` / 引理 `mem_functorPushforward_functor`

English:
lemma mem_functorPushforward_functor
  given: {Y : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ e.functor.obj X}
  proof: congr($(S.functorPushforward_functor e).arrows f)

中文:
引理 mem_functorPushforward_functor
  条件: {Y : D} {S : 筛 X} {e : C ≌ D} {f : Y ⟶ e.functor.obj X}
  证明: congr($(S.functorPushforward_functor e).arrows f)

Depends on / 依赖: S.functorPushforward_functor, arrows, functorPushforward_functor
-/
lemma mem_functorPushforward_functor {Y : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ e.functor.obj X} :
    S.functorPushforward e.functor f ↔ S (e.inverse.map f ≫ e.unitInv.app X) :=
  congr($(S.functorPushforward_functor e).arrows f)

/--
lemma `functorPushforward_inverse` / 引理 `functorPushforward_inverse`

English:
lemma functorPushforward_inverse
  given: {X : D} (S : Sieve X) (e : C ≌ D)
  proof: Sieve.functorPushforward_functor S e.symm

@[simp]

中文:
引理 functorPushforward_inverse
  条件: {X : D} (S : 筛 X) (e : C ≌ D)
  证明: Sieve.functorPushforward_functor S e.symm

@[simp]

Depends on / 依赖: Sieve.functorPushforward_functor, e.symm, functorPushforward_functor
-/
lemma functorPushforward_inverse {X : D} (S : Sieve X) (e : C ≌ D) :
    S.functorPushforward e.inverse = (S.pullback (e.counit.app X)).functorPullback e.functor :=
  Sieve.functorPushforward_functor S e.symm

@[simp]
/--
lemma `mem_functorPushforward_inverse` / 引理 `mem_functorPushforward_inverse`

English:
lemma mem_functorPushforward_inverse
  given: {X : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ e.inverse.obj X}
  proof: congr($(S.functorPushforward_inverse e).arrows f)

中文:
引理 mem_functorPushforward_inverse
  条件: {X : D} {S : 筛 X} {e : C ≌ D} {f : Y ⟶ e.inverse.obj X}
  证明: congr($(S.functorPushforward_inverse e).arrows f)

Depends on / 依赖: S.functorPushforward_inverse, arrows, functorPushforward_inverse
-/
lemma mem_functorPushforward_inverse {X : D} {S : Sieve X} {e : C ≌ D} {f : Y ⟶ e.inverse.obj X} :
    S.functorPushforward e.inverse f ↔ S (e.functor.map f ≫ e.counit.app X) :=
  congr($(S.functorPushforward_inverse e).arrows f)

variable (e : C ≌ D)

/--
lemma `functorPushforward_equivalence_eq_pullback` / 引理 `functorPushforward_equivalence_eq_pullback`

English:
lemma functorPushforward_equivalence_eq_pullback
  given: {U : C} (S : Sieve U)
  proof: by ext; simp

中文:
引理 functorPushforward_equivalence_eq_pullback
  条件: {U : C} (S : 筛 U)
  证明: by ext; simp
-/
lemma functorPushforward_equivalence_eq_pullback {U : C} (S : Sieve U) :
    Sieve.functorPushforward e.inverse (Sieve.functorPushforward e.functor S) =
      Sieve.pullback (e.unitInv.app U) S := by ext; simp

/--
lemma `pullback_functorPushforward_equivalence_eq` / 引理 `pullback_functorPushforward_equivalence_eq`

English:
lemma pullback_functorPushforward_equivalence_eq
  given: {X : C} (S : Sieve X)
  proof: by ext; simp

中文:
引理 pullback_functorPushforward_equivalence_eq
  条件: {X : C} (S : 筛 X)
  证明: by ext; simp
-/
lemma pullback_functorPushforward_equivalence_eq {X : C} (S : Sieve X) :
    Sieve.pullback (e.unit.app X) (Sieve.functorPushforward e.inverse
      (Sieve.functorPushforward e.functor S)) = S := by ext; simp

/--
lemma `mem_functorPushforward_iff_of_full` / 引理 `mem_functorPushforward_iff_of_full`

English:
lemma mem_functorPushforward_iff_of_full
  given: [F.Full] {X Y : C} (R : Sieve X) (f : F.obj Y ⟶ F.obj X)
  proof: by
  refine ⟨fun ⟨Z, g, h, hg, hcomp⟩ => ?_, fun ⟨g, hcomp, hg⟩ => ?_⟩
  · obtain ⟨h', hh'⟩ := F.map_surjective h
    use h' ≫ g
    simp only [Functor.map_comp, hh', hcomp, true_and]
    apply R.downward_closed hg
  · use Y, g, 𝟙 _, hg
    simp [hcomp]

中文:
引理 mem_functorPushforward_iff_of_full
  条件: [F.满] {X Y : C} (R : 筛 X) (f : F.obj Y ⟶ F.obj X)
  证明: by
  refine ⟨fun ⟨Z, g, h, hg, hcomp⟩ => ?_, fun ⟨g, hcomp, hg⟩ => ?_⟩
  · obtain ⟨h', hh'⟩ := F.map_surjective h
    use h' ≫ g
    simp only [Functor.map_comp, hh', hcomp, true_and]
    apply R.downward_closed hg
  · use Y, g, 𝟙 _, hg
    simp [hcomp]

Depends on / 依赖: F.map_surjective, Functor, Functor.map_comp, R.downward_closed, downward_closed, map_comp, map_surjective, true_and
-/
lemma mem_functorPushforward_iff_of_full [F.Full] {X Y : C} (R : Sieve X) (f : F.obj Y ⟶ F.obj X) :
    (R.arrows.functorPushforward F) f ↔ exists (g : Y ⟶ X), F.map g = f ∧ R g := by
  refine ⟨fun ⟨Z, g, h, hg, hcomp⟩ => ?_, fun ⟨g, hcomp, hg⟩ => ?_⟩
  · obtain ⟨h', hh'⟩ := F.map_surjective h
    use h' ≫ g
    simp only [Functor.map_comp, hh', hcomp, true_and]
    apply R.downward_closed hg
  · use Y, g, 𝟙 _, hg
    simp [hcomp]

/--
lemma `mem_functorPushforward_iff_of_full_of_faithful` / 引理 `mem_functorPushforward_iff_of_full_of_faithful`

English:
lemma mem_functorPushforward_iff_of_full_of_faithful
  statement: [F.Full] [F.Faithful]
  proof: by
  rw [Sieve.mem_functorPushforward_iff_of_full]
  refine ⟨fun ⟨g, hcomp, hg⟩ => ?_, fun hf => ⟨f, rfl, hf⟩⟩
  rwa [← F.map_injective hcomp]

中文:
引理 mem_functorPushforward_iff_of_full_of_faithful
  结论: [F.满] [F.忠实]
  证明: by
  rw [Sieve.mem_functorPushforward_iff_of_full]
  refine ⟨fun ⟨g, hcomp, hg⟩ => ?_, fun hf => ⟨f, rfl, hf⟩⟩
  rwa [← F.map_injective hcomp]

Depends on / 依赖: F.map_injective, Sieve.mem_functorPushforward_iff_of_full, map_injective, mem_functorPushforward_iff_of_full
-/
lemma mem_functorPushforward_iff_of_full_of_faithful [F.Full] [F.Faithful]
    {X Y : C} (R : Sieve X) (f : Y ⟶ X) :
    (R.arrows.functorPushforward F) (F.map f) ↔ R f := by
  rw [Sieve.mem_functorPushforward_iff_of_full]
  refine ⟨fun ⟨g, hcomp, hg⟩ => ?_, fun hf => ⟨f, rfl, hf⟩⟩
  rwa [← F.map_injective hcomp]

/--
lemma `functorPushforward_ofObjects_le` / 引理 `functorPushforward_ofObjects_le`

English:
lemma functorPushforward_ofObjects_le
  proof: by
  rintro Z f ⟨W, g₁, g₂, ⟨i, ⟨g₃⟩⟩, hf⟩
  exact ⟨i, ⟨g₂ ≫ F.map g₃⟩⟩

中文:
引理 functorPushforward_ofObjects_le
  证明: by
  rintro Z f ⟨W, g₁, g₂, ⟨i, ⟨g₃⟩⟩, hf⟩
  exact ⟨i, ⟨g₂ ≫ F.map g₃⟩⟩

Depends on / 依赖: F.map
-/
lemma functorPushforward_ofObjects_le
    {I : Type*} (X : I -> C) (Y : C) :
    (ofObjects X Y).functorPushforward F <= ofObjects (F.obj ∘ X) (F.obj Y) := by
  rintro Z f ⟨W, g₁, g₂, ⟨i, ⟨g₃⟩⟩, hf⟩
  exact ⟨i, ⟨g₂ ≫ F.map g₃⟩⟩

end Functor

/-- A sieve induces a presheaf. -/
@[simps obj map]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: (S : Sieve X)
  body: { g : Y.unop ⟶ X // S g }
  map f := ↾fun g => ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩

中文:
定义 functor
  签名: (S : 筛 X)
  定义体: { g : Y.unop ⟶ X // S g }
  map f := ↾fun g => ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩

Depends on / 依赖: Y.unop
-/
def functor (S : Sieve X) : Cᵒᵖ ⥤ Type v₁ where
  obj Y := { g : Y.unop ⟶ X // S g }
  map f := ↾fun g => ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩

/-- If a sieve S is contained in a sieve T, then we have a morphism of presheaves on their induced
presheaves.
-/
@[simps]
/--
Definition of `natTransOfLe` / `natTransOfLe` 的定义

English:
definition natTransOfLe
  signature: {S T : Sieve X} (h : S <= T)
  body: ↾fun f => ⟨f.1, h _ f.2⟩

中文:
定义 natTransOfLe
  签名: {S T : 筛 X} (h : S <= T)
  定义体: ↾fun f => ⟨f.1, h _ f.2⟩
-/
def natTransOfLe {S T : Sieve X} (h : S <= T) : S.functor ⟶ T.functor where
  app _ := ↾fun f => ⟨f.1, h _ f.2⟩

/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simps]
/--
Definition of `functorInclusion` / `functorInclusion` 的定义

English:
definition functorInclusion
  signature: (S : Sieve X)
  body: ↾fun f => f.1

中文:
定义 functorInclusion
  签名: (S : 筛 X)
  定义体: ↾fun f => f.1
-/
def functorInclusion (S : Sieve X) : S.functor ⟶ yoneda.obj X where
  app _ := ↾fun f => f.1

set_option backward.isDefEq.respectTransparency.types false in
/-- Any component `f : Y ⟶ X` of the sieve `S` induces a natural transformation from `yoneda.obj Y`
to the presheaf induced by `S`. -/
@[simps]
/--
Definition of `toFunctor` / `toFunctor` 的定义

English:
definition toFunctor
  signature: (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f)
  body: ↾fun g => ⟨g ≫ f, S.downward_closed hf g⟩

中文:
定义 toFunctor
  签名: (S : 筛 X) {Y : C} (f : Y ⟶ X) (hf : S f)
  定义体: ↾fun g => ⟨g ≫ f, S.downward_closed hf g⟩

Depends on / 依赖: S.downward_closed, downward_closed
-/
def toFunctor (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f) : yoneda.obj Y ⟶ S.functor where
  app Z := ↾fun g => ⟨g ≫ f, S.downward_closed hf g⟩

/--
theorem `natTransOfLe_comm` / 定理 `natTransOfLe_comm`

English:
theorem natTransOfLe_comm
  given: {S T : Sieve X} (h : S <= T)
  proof: rfl

中文:
定理 natTransOfLe_comm
  条件: {S T : 筛 X} (h : S <= T)
  证明: rfl
-/
theorem natTransOfLe_comm {S T : Sieve X} (h : S <= T) :
    natTransOfLe h ≫ functorInclusion _ = functorInclusion _ :=
  rfl

open ConcreteCategory

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `functorInclusion_is_mono` / 实例 `functorInclusion_is_mono`

English:
instance functorInclusion_is_mono
  signature: : Mono S.functorInclusion
  body: ⟨fun f g h => by
    ext Y y
    simpa [Subtype.ext_iff] using congr_hom (NatTrans.congr_app h Y) y⟩

中文:
实例 functorInclusion_is_mono
  签名: : 单态射 S.functorInclusion
  定义体: ⟨fun f g h => by
    ext Y y
    simpa [Subtype.ext_iff] using congr_hom (NatTrans.congr_app h Y) y⟩

Depends on / 依赖: NatTrans, NatTrans.congr_app, Subtype, Subtype.ext_iff, congr_app, congr_hom, ext_iff
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
/--
Definition of `sieveOfSubfunctor` / `sieveOfSubfunctor` 的定义

English:
definition sieveOfSubfunctor
  signature: {R} (f : R ⟶ yoneda.obj X)
  body: exists t, f.app (Opposite.op Y) t = g
  downward_closed := by
    rintro Y Z _ ⟨t, rfl⟩ g
    refine ⟨R.map g.op t, ?_⟩
    simp

中文:
定义 sieveOfSubfunctor
  签名: {R} (f : R ⟶ yoneda.obj X)
  定义体: exists t, f.app (Opposite.op Y) t = g
  downward_closed := by
    rintro Y Z _ ⟨t, rfl⟩ g
    refine ⟨R.map g.op t, ?_⟩
    simp

Depends on / 依赖: Opposite, Opposite.op, f.app
-/
def sieveOfSubfunctor {R} (f : R ⟶ yoneda.obj X) : Sieve X where
  arrows Y g := exists t, f.app (Opposite.op Y) t = g
  downward_closed := by
    rintro Y Z _ ⟨t, rfl⟩ g
    refine ⟨R.map g.op t, ?_⟩
    simp

/--
theorem `sieveOfSubfunctor_functorInclusion` / 定理 `sieveOfSubfunctor_functorInclusion`

English:
theorem sieveOfSubfunctor_functorInclusion
  statement: sieveOfSubfunctor S.functorInclusion = S
  proof: by
  ext
  simp only [functorInclusion_app, sieveOfSubfunctor_apply]
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact hf
  · intro hf
    exact ⟨⟨_, hf⟩, rfl⟩

中文:
定理 sieveOfSubfunctor_functorInclusion
  结论: sieveOfSubfunctor S.functorInclusion = S
  证明: by
  ext
  simp only [functorInclusion_app, sieveOfSubfunctor_apply]
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact hf
  · intro hf
    exact ⟨⟨_, hf⟩, rfl⟩

Depends on / 依赖: functorInclusion_app, sieveOfSubfunctor_apply
-/
theorem sieveOfSubfunctor_functorInclusion : sieveOfSubfunctor S.functorInclusion = S := by
  ext
  simp only [functorInclusion_app, sieveOfSubfunctor_apply]
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact hf
  · intro hf
    exact ⟨⟨_, hf⟩, rfl⟩

/--
Instance `functorInclusion_top_isIso` / 实例 `functorInclusion_top_isIso`

English:
instance functorInclusion_top_isIso
  signature: : IsIso (⊤ : Sieve X).functorInclusion
  body: ⟨⟨{ app := fun _ => ↾fun a => ⟨a, ⟨⟩⟩ }, rfl, rfl⟩⟩

中文:
实例 functorInclusion_top_isIso
  签名: : 是同构 (⊤ : 筛 X).functorInclusion
  定义体: ⟨⟨{ app := fun _ => ↾fun a => ⟨a, ⟨⟩⟩ }, rfl, rfl⟩⟩
-/
instance functorInclusion_top_isIso : IsIso (⊤ : Sieve X).functorInclusion :=
  ⟨⟨{ app := fun _ => ↾fun a => ⟨a, ⟨⟩⟩ }, rfl, rfl⟩⟩

/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
abbreviation uliftFunctor
  signature: (S : Sieve X)
  body: S.functor ⋙ CategoryTheory.uliftFunctor

中文:
缩写 uliftFunctor
  签名: (S : 筛 X)
  定义体: S.functor ⋙ CategoryTheory.uliftFunctor

Depends on / 依赖: CategoryTheory, CategoryTheory.uliftFunctor, S.functor, functor, uliftFunctor
-/
abbrev uliftFunctor (S : Sieve X) : Cᵒᵖ ⥤ Type (max w v₁) :=
  S.functor ⋙ CategoryTheory.uliftFunctor

/-- A variant of `Sieve.natTransOfLe` with universe lifting. -/
@[simps]
/--
Definition of `uliftNatTransOfLe` / `uliftNatTransOfLe` 的定义

English:
definition uliftNatTransOfLe
  signature: {S T : Sieve X} (h : S <= T)
  body: ↾fun f => ⟨f.down.1, h _ f.down.2⟩

中文:
定义 ulift自然数TransOfLe
  签名: {S T : 筛 X} (h : S <= T)
  定义体: ↾fun f => ⟨f.down.1, h _ f.down.2⟩

Depends on / 依赖: f.down
-/
def uliftNatTransOfLe {S T : Sieve X} (h : S <= T) :
    Sieve.uliftFunctor.{w} S ⟶ Sieve.uliftFunctor.{w} T where
  app _ := ↾fun f => ⟨f.down.1, h _ f.down.2⟩

/-- A variant of `Sieve.functorInclusion` with universe lifting. -/
@[simps! app]
/--
Definition of `uliftFunctorInclusion` / `uliftFunctorInclusion` 的定义

English:
definition uliftFunctorInclusion
  signature: (S : Sieve X)
  body: Functor.whiskerRight S.functorInclusion CategoryTheory.uliftFunctor

中文:
定义 uliftFunctorInclusion
  签名: (S : 筛 X)
  定义体: Functor.whiskerRight S.functorInclusion CategoryTheory.uliftFunctor

Depends on / 依赖: CategoryTheory, CategoryTheory.uliftFunctor, Functor, Functor.whiskerRight, S.functorInclusion, functorInclusion, uliftFunctor, whiskerRight
-/
def uliftFunctorInclusion (S : Sieve X) :
    S.uliftFunctor ⟶ uliftYoneda.{w}.obj X :=
  Functor.whiskerRight S.functorInclusion CategoryTheory.uliftFunctor

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `Sieve.toFunctor` with universe lifting. -/
@[simps]
/--
Definition of `toUliftFunctor` / `toUliftFunctor` 的定义

English:
definition toUliftFunctor
  signature: (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f)
  body: ↾fun g => ⟨g.down ≫ f, S.downward_closed hf g.down⟩

中文:
定义 toUliftFunctor
  签名: (S : 筛 X) {Y : C} (f : Y ⟶ X) (hf : S f)
  定义体: ↾fun g => ⟨g.down ≫ f, S.downward_closed hf g.down⟩

Depends on / 依赖: S.downward_closed, downward_closed, g.down
-/
def toUliftFunctor (S : Sieve X) {Y : C} (f : Y ⟶ X) (hf : S f) :
    uliftYoneda.{w}.obj Y ⟶ Sieve.uliftFunctor.{w} S where
  app Z := ↾fun g => ⟨g.down ≫ f, S.downward_closed hf g.down⟩

/--
theorem `uliftNatTransOfLe_comm` / 定理 `uliftNatTransOfLe_comm`

English:
theorem uliftNatTransOfLe_comm
  given: {S T : Sieve X} (h : S <= T)
  proof: rfl

中文:
定理 ulift自然数TransOfLe_comm
  条件: {S T : 筛 X} (h : S <= T)
  证明: rfl
-/
theorem uliftNatTransOfLe_comm {S T : Sieve X} (h : S <= T) :
    uliftNatTransOfLe.{w} h ≫ uliftFunctorInclusion.{w} _ = uliftFunctorInclusion.{w} _ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `uliftFunctorInclusion_is_mono` / 实例 `uliftFunctorInclusion_is_mono`

English:
instance uliftFunctorInclusion_is_mono
  signature: (S : Sieve X)
  body: ⟨fun _ _ h => by
    ext Y y
    refine ULift.ext _ _ (Subtype.ext_iff.2 ?_)
    simpa using congr_hom (NatTrans.congr_app h Y) y⟩

中文:
实例 uliftFunctorInclusion_is_mono
  签名: (S : 筛 X)
  定义体: ⟨fun _ _ h => by
    ext Y y
    refine ULift.ext _ _ (Subtype.ext_iff.2 ?_)
    simpa using congr_hom (NatTrans.congr_app h Y) y⟩

Depends on / 依赖: NatTrans, NatTrans.congr_app, Subtype, Subtype.ext_iff, ULift.ext, congr_app, congr_hom, ext_iff
-/
instance uliftFunctorInclusion_is_mono (S : Sieve X) :
    Mono (Sieve.uliftFunctorInclusion.{w} S) :=
  ⟨fun _ _ h => by
    ext Y y
    refine ULift.ext _ _ (Subtype.ext_iff.2 ?_)
    simpa using congr_hom (NatTrans.congr_app h Y) y⟩

/-- A variant of `Sieve.sieveOfSubfunctor` with universe lifting. -/
@[simps]
/--
Definition of `sieveOfUliftSubfunctor` / `sieveOfUliftSubfunctor` 的定义

English:
definition sieveOfUliftSubfunctor
  signature: {R : Cᵒᵖ ⥤ Type max w v₁} (f : R ⟶ uliftYoneda.{w}.obj X)
  body: exists t, f.app (Opposite.op Y) t = { down := g }
  downward_closed := by
    intro Y Z _ ⟨t, ht⟩ g
    refine ⟨R.map g.op t, ?_⟩
    simp [ht]

中文:
定义 sieveOfUliftSubfunctor
  签名: {R : Cᵒᵖ ⥤ 类型 最大值 w v₁} (f : R ⟶ uliftYoneda.{w}.obj X)
  定义体: exists t, f.app (Opposite.op Y) t = { down := g }
  downward_closed := by
    intro Y Z _ ⟨t, ht⟩ g
    refine ⟨R.map g.op t, ?_⟩
    simp [ht]

Depends on / 依赖: Opposite, Opposite.op, f.app
-/
def sieveOfUliftSubfunctor {R : Cᵒᵖ ⥤ Type max w v₁} (f : R ⟶ uliftYoneda.{w}.obj X) :
    Sieve X where
  arrows Y g := exists t, f.app (Opposite.op Y) t = { down := g }
  downward_closed := by
    intro Y Z _ ⟨t, ht⟩ g
    refine ⟨R.map g.op t, ?_⟩
    simp [ht]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `sieveOfUliftSubfunctor_uliftFunctorInclusion` / 定理 `sieveOfUliftSubfunctor_uliftFunctorInclusion`

English:
theorem sieveOfUliftSubfunctor_uliftFunctorInclusion
  given: {S : Sieve X}
  proof: by
  cat_disch

中文:
定理 sieveOfUliftSubfunctor_uliftFunctorInclusion
  条件: {S : 筛 X}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem sieveOfUliftSubfunctor_uliftFunctorInclusion {S : Sieve X} :
    Sieve.sieveOfUliftSubfunctor.{w} (S.uliftFunctorInclusion) = S := by
  cat_disch

/--
Instance `uliftFunctorInclusion_top_isIso` / 实例 `uliftFunctorInclusion_top_isIso`

English:
instance uliftFunctorInclusion_top_isIso
  signature: : IsIso (Sieve.uliftFunctorInclusion.{w} (⊤ : Sieve X))
  body: ⟨⟨{ app := fun _ => ↾fun a => ⟨a.down, ⟨⟩⟩ }, rfl, rfl⟩⟩

中文:
实例 uliftFunctorInclusion_top_isIso
  签名: : 是同构 (筛.uliftFunctorInclusion.{w} (⊤ : 筛 X))
  定义体: ⟨⟨{ app := fun _ => ↾fun a => ⟨a.down, ⟨⟩⟩ }, rfl, rfl⟩⟩

Depends on / 依赖: a.down
-/
instance uliftFunctorInclusion_top_isIso : IsIso (Sieve.uliftFunctorInclusion.{w} (⊤ : Sieve X)) :=
  ⟨⟨{ app := fun _ => ↾fun a => ⟨a.down, ⟨⟩⟩ }, rfl, rfl⟩⟩

/--
lemma `ofArrows_eq_pullback_of_isPullback` / 引理 `ofArrows_eq_pullback_of_isPullback`

English:
lemma ofArrows_eq_pullback_of_isPullback
  statement: {ι : Type*} {S : C} {X : ι -> C} (f : (i : ι) -> X i ⟶ S)
  proof: by
  refine le_antisymm ?_ ?_
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    use X i, p₂ i, f i, ⟨i⟩
    exact (h i).w.symm
  · rintro W u ⟨Z, v, s, ⟨i⟩, heq⟩
    use P i, (h i).lift u v heq.symm, p₁ i, ⟨i⟩
    simp

中文:
引理 ofArrows_eq_pullback_of_isPullback
  结论: {ι : 类型} {S : C} {X : ι -> C} (f : (i : ι) -> X i ⟶ S)
  证明: by
  refine le_antisymm ?_ ?_
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    use X i, p₂ i, f i, ⟨i⟩
    exact (h i).w.symm
  · rintro W u ⟨Z, v, s, ⟨i⟩, heq⟩
    use P i, (h i).lift u v heq.symm, p₁ i, ⟨i⟩
    simp

Depends on / 依赖: Sieve.generate_le_iff, Sieve.ofArrows, generate_le_iff, heq.symm, le_antisymm, ofArrows, w.symm
-/
lemma ofArrows_eq_pullback_of_isPullback {ι : Type*} {S : C} {X : ι -> C} (f : (i : ι) -> X i ⟶ S)
    {Y : C} {g : Y ⟶ S} {P : ι -> C} {p₁ : (i : ι) -> P i ⟶ Y} {p₂ : (i : ι) -> P i ⟶ X i}
    (h : forall (i : ι), IsPullback (p₁ i) (p₂ i) g (f i)) :
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
/--
Definition of `shrinkFunctor` / `shrinkFunctor` 的定义

English:
definition shrinkFunctor
  signature: [LocallySmall.{w} C] {X : C} (S : Sieve X)
  body: { f | S (shrinkYonedaObjObjEquiv f) }
  map {Y Z} g f hf := by
    simpa [shrinkYonedaObjObjEquiv_obj_map] using S.downward_closed hf _

中文:
定义 shrinkFunctor
  签名: [LocallySmall.{w} C] {X : C} (S : 筛 X)
  定义体: { f | S (shrinkYonedaObjObjEquiv f) }
  map {Y Z} g f hf := by
    simpa [shrinkYonedaObjObjEquiv_obj_map] using S.downward_closed hf _

Depends on / 依赖: shrinkYonedaObjObjEquiv
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
/--
Definition of `shrinkFunctorUliftFunctorIso` / `shrinkFunctorUliftFunctorIso` 的定义

English:
definition shrinkFunctorUliftFunctorIso
  signature: [LocallySmall.{w} C] [LocallySmall.{max w' w} C]
  body: NatIso.ofComponents
    (fun X => Equiv.toIso
      (.trans Equiv.ulift
        (Equiv.subtypeEquiv (shrinkYonedaObjObjEquiv.trans shrinkYonedaObjObjEquiv.symm)
        fun a => by simp)))
    fun {U V} f => by
      dsimp
      ext
      dsimp [Equiv.subtypeEquiv_apply]
      rw [shrinkYonedaObjObj

中文:
定义 shrinkFunctorUliftFunctorIso
  签名: [LocallySmall.{w} C] [LocallySmall.{最大值 w' w} C]
  定义体: NatIso.ofComponents
    (fun X => Equiv.toIso
      (.trans Equiv.ulift
        (Equiv.subtypeEquiv (shrinkYonedaObjObjEquiv.trans shrinkYonedaObjObjEquiv.symm)
        fun a => by simp)))
    fun {U V} f => by
      dsimp
      ext
      dsimp [Equiv.subtypeEquiv_apply]
      rw [shrinkYonedaObjObj

Depends on / 依赖: Equiv.subtypeEquiv, Equiv.subtypeEquiv_apply, Equiv.toIso, Equiv.ulift, NatIso, NatIso.ofComponents, ofComponents, shrinkYonedaObjObjEquiv, shrinkYonedaObjObjEquiv.symm, shrinkYonedaObjObjEquiv.trans, shrinkYonedaObjObjEquiv_obj_map, shrinkYonedaObjObjEquiv_symm_comp, subtypeEquiv, subtypeEquiv_apply
-/
def shrinkFunctorUliftFunctorIso [LocallySmall.{w} C] [LocallySmall.{max w' w} C] :
    (shrinkFunctor.{w} S).toFunctor ⋙ CategoryTheory.uliftFunctor.{w', w} ≅
      (shrinkFunctor.{max w' w} S).toFunctor :=
  NatIso.ofComponents
    (fun X => Equiv.toIso
      (.trans Equiv.ulift
        (Equiv.subtypeEquiv (shrinkYonedaObjObjEquiv.trans shrinkYonedaObjObjEquiv.symm)
        fun a => by simp)))
    fun {U V} f => by
      dsimp
      ext
      dsimp [Equiv.subtypeEquiv_apply]
      rw [shrinkYonedaObjObjEquiv_obj_map]; rw [shrinkYonedaObjObjEquiv_symm_comp]
      simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `shrinkFunctorUliftFunctorIso_inv_ι` / 引理 `shrinkFunctorUliftFunctorIso_inv_ι`

English:
lemma shrinkFunctorUliftFunctorIso_inv_ι
  given: [LocallySmall.{w} C] [LocallySmall.{max w' w} C]
  proof: rfl

中文:
引理 shrinkFunctorUliftFunctorIso_inv_ι
  条件: [LocallySmall.{w} C] [LocallySmall.{最大值 w' w} C]
  证明: rfl
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
/--
Definition of `shrinkFunctorIsoFunctor` / `shrinkFunctorIsoFunctor` 的定义

English:
definition shrinkFunctorIsoFunctor
  signature: : (shrinkFunctor.{v₁} S).toFunctor ≅ S.functor
  body: NatIso.ofComponents (fun Y => Equiv.toIso <| Equiv.subtypeEquiv shrinkYonedaObjObjEquiv (by simp))
    fun {U V} f => by
      dsimp [Equiv.subtypeEquiv_apply]
      ext
      simp [shrinkYonedaObjObjEquiv_obj_map]

中文:
定义 shrinkFunctorIsoFunctor
  签名: : (shrinkFunctor.{v₁} S).toFunctor ≅ S.functor
  定义体: NatIso.ofComponents (fun Y => Equiv.toIso <| Equiv.subtypeEquiv shrinkYonedaObjObjEquiv (by simp))
    fun {U V} f => by
      dsimp [Equiv.subtypeEquiv_apply]
      ext
      simp [shrinkYonedaObjObjEquiv_obj_map]

Depends on / 依赖: Equiv.subtypeEquiv, Equiv.subtypeEquiv_apply, Equiv.toIso, NatIso, NatIso.ofComponents, ofComponents, shrinkYonedaObjObjEquiv, shrinkYonedaObjObjEquiv_obj_map, subtypeEquiv, subtypeEquiv_apply
-/
noncomputable def shrinkFunctorIsoFunctor : (shrinkFunctor.{v₁} S).toFunctor ≅ S.functor :=
  NatIso.ofComponents (fun Y => Equiv.toIso <| Equiv.subtypeEquiv shrinkYonedaObjObjEquiv (by simp))
    fun {U V} f => by
      dsimp [Equiv.subtypeEquiv_apply]
      ext
      simp [shrinkYonedaObjObjEquiv_obj_map]

end Sieve

/--
lemma `Presieve.functorPullback_arrows` / 引理 `Presieve.functorPullback_arrows`

English:
lemma Presieve.functorPullback_arrows
  given: {X : C} (S : Sieve (F.obj X))
  proof: rfl

中文:
引理 Presieve.functorPullback_arrows
  条件: {X : C} (S : 筛 (F.obj X))
  证明: rfl
-/
lemma Presieve.functorPullback_arrows {X : C} (S : Sieve (F.obj X)) :
    Presieve.functorPullback F S.arrows = Sieve.functorPullback F S :=
  rfl

/--
theorem `Presieve.map_le_functorPushforward` / 定理 `Presieve.map_le_functorPushforward`

English:
theorem Presieve.map_le_functorPushforward
  given: (S : Presieve X)
  statement: S.map F <= S.functorPushforward F
  proof: by
  grw [← Sieve.arrows_generate_map_eq_functorPushforward, ← Sieve.le_generate]

中文:
定理 Presieve.map_le_functorPushforward
  条件: (S : Presieve X)
  结论: S.map F <= S.functorPushforward F
  证明: by
  grw [← Sieve.arrows_generate_map_eq_functorPushforward, ← Sieve.le_generate]

Depends on / 依赖: Sieve.arrows_generate_map_eq_functorPushforward, Sieve.le_generate, arrows_generate_map_eq_functorPushforward, le_generate
-/
theorem Presieve.map_le_functorPushforward (S : Presieve X) : S.map F <= S.functorPushforward F := by
  grw [← Sieve.arrows_generate_map_eq_functorPushforward, ← Sieve.le_generate]

/--
lemma `Presieve.bind_ofArrows_le_bindOfArrows` / 引理 `Presieve.bind_ofArrows_le_bindOfArrows`

English:
lemma Presieve.bind_ofArrows_le_bindOfArrows
  statement: {ι : Type*} {X : C} (Z : ι -> C)
  proof: by
  rintro T g ⟨W, v, v', hv', ⟨S, u, u', h, hu⟩, rfl⟩
  rw [← Sieve.ofArrows.fac hv']; rw [← reassoc_of% hu]
  exact ⟨S, u, u' ≫ f _, ⟨_, _, h⟩, rfl⟩

@[deprecated "Use Sieve.arrows_generate_map_eq_functorPushforward instead." (since := "2026-07-09")]

中文:
引理 Presieve.bind_ofArrows_le_bindOfArrows
  结论: {ι : 类型} {X : C} (Z : ι -> C)
  证明: by
  rintro T g ⟨W, v, v', hv', ⟨S, u, u', h, hu⟩, rfl⟩
  rw [← Sieve.ofArrows.fac hv']; rw [← reassoc_of% hu]
  exact ⟨S, u, u' ≫ f _, ⟨_, _, h⟩, rfl⟩

@[deprecated "Use Sieve.arrows_generate_map_eq_functorPushforward instead." (since := "2026-07-09")]

Depends on / 依赖: Sieve.ofArrows.fac, ofArrows, reassoc_of
-/
lemma Presieve.bind_ofArrows_le_bindOfArrows {ι : Type*} {X : C} (Z : ι -> C)
    (f : forall i, Z i ⟶ X) (R : forall i, Presieve (Z i)) :
    Sieve.bind (Sieve.ofArrows Z f)
      (fun _ _ hg => Sieve.pullback
        (Sieve.ofArrows.h hg) (.generate <| R (Sieve.ofArrows.i hg))) <=
    Sieve.generate (Presieve.bindOfArrows Z f R) := by
  rintro T g ⟨W, v, v', hv', ⟨S, u, u', h, hu⟩, rfl⟩
  rw [← Sieve.ofArrows.fac hv']; rw [← reassoc_of% hu]
  exact ⟨S, u, u' ≫ f _, ⟨_, _, h⟩, rfl⟩

@[deprecated "Use Sieve.arrows_generate_map_eq_functorPushforward instead." (since := "2026-07-09")]
/--
lemma `Presieve.functorPushforward_overForget` / 引理 `Presieve.functorPushforward_overForget`

English:
lemma Presieve.functorPushforward_overForget
  proof: (Sieve.arrows_generate_map_eq_functorPushforward (Over.forget S)).symm

中文:
引理 Presieve.functorPushforward_overForget
  证明: (Sieve.arrows_generate_map_eq_functorPushforward (Over.forget S)).symm

Depends on / 依赖: Over.forget, Sieve.arrows_generate_map_eq_functorPushforward, arrows_generate_map_eq_functorPushforward, forget
-/
lemma Presieve.functorPushforward_overForget
    {S : C} {X : Over S} (R : Presieve X) :
    Presieve.functorPushforward (Over.forget S) R =
      (Sieve.generate (Presieve.map (Over.forget S) R)).arrows :=
  (Sieve.arrows_generate_map_eq_functorPushforward (Over.forget S)).symm

end CategoryTheory

-- pushed over the edge in `nightly-testing`, should be split after landing on master
set_option linter.style.longFile 1600
