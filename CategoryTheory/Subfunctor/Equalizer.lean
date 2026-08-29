/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# The equalizer of two morphisms of functors, as a subfunctor

If `F₁` and `F₂` are type-valued functors, `A : Subfunctor F₁`, and
`f` and `g` are two morphisms `A.toFunctor ⟶ F₂`, we introduce
`Subcomplex.equalizer f g`, which is the subfunctor of `F₁` contained in `A`
where `f` and `g` coincide.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F₁ F₂ : C ⥤ Type w} {A : Subfunctor F₁}
  (f g : A.toFunctor ⟶ F₂)

namespace Subfunctor

/-- The equalizer of two morphisms of type-valued functors of types of the form
`A.toFunctor ⟶ F₂` with `A : Subfunctor F₁`, as a subcomplex of `F₁`. -/
@[simps -isSimp]
/--
Definition of `equalizer` / `equalizer` 的定义

English:
definition equalizer
  signature: : Subfunctor F₁ where
  body: Set.ofPred (fun x => exists (hx : x in A.obj _), f.app _ ⟨x, hx⟩ = g.app _ ⟨x, hx⟩)
  map φ x := by
    rintro ⟨hx, h⟩
    exact ⟨A.map _ hx,
      (NatTrans.naturality_apply f φ ⟨x, hx⟩).trans (Eq.trans (by rw [h])
        (NatTrans.naturality_apply g φ ⟨x, hx⟩).symm)⟩

中文:
定义 equalizer
  签名: : 子函子 F₁ where
  定义体: Set.ofPred (fun x => exists (hx : x in A.obj _), f.app _ ⟨x, hx⟩ = g.app _ ⟨x, hx⟩)
  map φ x := by
    rintro ⟨hx, h⟩
    exact ⟨A.map _ hx,
      (NatTrans.naturality_apply f φ ⟨x, hx⟩).trans (Eq.trans (by rw [h])
        (NatTrans.naturality_apply g φ ⟨x, hx⟩).symm)⟩
-/
protected def equalizer : Subfunctor F₁ where
  obj U := Set.ofPred (fun x => exists (hx : x in A.obj _), f.app _ ⟨x, hx⟩ = g.app _ ⟨x, hx⟩)
  map φ x := by
    rintro ⟨hx, h⟩
    exact ⟨A.map _ hx,
      (NatTrans.naturality_apply f φ ⟨x, hx⟩).trans (Eq.trans (by rw [h])
        (NatTrans.naturality_apply g φ ⟨x, hx⟩).symm)⟩

attribute [local simp] equalizer_obj

/--
lemma `equalizer_le` / 引理 `equalizer_le`

English:
lemma equalizer_le
  statement: Subfunctor.equalizer f g <= A
  proof: fun _ _ h => h.1

@[simp]

中文:
引理 equalizer_le
  结论: 子函子.equalizer f g <= A
  证明: fun _ _ h => h.1

@[simp]
-/
lemma equalizer_le : Subfunctor.equalizer f g <= A :=
  fun _ _ h => h.1

@[simp]
/--
lemma `equalizer_self` / 引理 `equalizer_self`

English:
lemma equalizer_self
  statement: Subfunctor.equalizer f f = A
  proof: by aesop

中文:
引理 equalizer_self
  结论: 子函子.equalizer f f = A
  证明: by aesop
-/
lemma equalizer_self : Subfunctor.equalizer f f = A := by aesop

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mem_equalizer_iff` / 引理 `mem_equalizer_iff`

English:
lemma mem_equalizer_iff
  given: {i : C} (x : A.toFunctor.obj i)
  proof: by
  simp

中文:
引理 mem_equalizer_iff
  条件: {i : C} (x : A.toFunctor.obj i)
  证明: by
  simp
-/
lemma mem_equalizer_iff {i : C} (x : A.toFunctor.obj i) :
    x.1 in (Subfunctor.equalizer f g).obj i ↔ f.app i x = g.app i x := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `range_le_equalizer_iff` / 引理 `range_le_equalizer_iff`

English:
lemma range_le_equalizer_iff
  given: {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
  proof: by
  rw [NatTrans.ext_iff]
  simp [le_def, Set.subset_def, ConcreteCategory.hom_ext_iff, funext_iff]

中文:
引理 range_le_equalizer_iff
  条件: {G : C ⥤ 类型 w} (φ : G ⟶ A.toFunctor)
  证明: by
  rw [NatTrans.ext_iff]
  simp [le_def, Set.subset_def, ConcreteCategory.hom_ext_iff, funext_iff]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext_iff, NatTrans, NatTrans.ext_iff, Set.subset_def, ext_iff, funext_iff, hom_ext_iff, le_def, subset_def
-/
lemma range_le_equalizer_iff {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor) :
    range (φ ≫ A.ι) <= Subfunctor.equalizer f g ↔ φ ≫ f = φ ≫ g := by
  rw [NatTrans.ext_iff]
  simp [le_def, Set.subset_def, ConcreteCategory.hom_ext_iff, funext_iff]

/--
lemma `equalizer_eq_iff` / 引理 `equalizer_eq_iff`

English:
lemma equalizer_eq_iff
  proof: by
  have := range_le_equalizer_iff f g (𝟙 _)
  simp only [Category.id_comp, range_ι] at this
  rw [← this]
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm (equalizer_le f g) h

中文:
引理 equalizer_eq_iff
  证明: by
  have := range_le_equalizer_iff f g (𝟙 _)
  simp only [Category.id_comp, range_ι] at this
  rw [← this]
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm (equalizer_le f g) h

Depends on / 依赖: Category, Category.id_comp, equalizer_le, id_comp, le_antisymm, range_le_equalizer_iff
-/
lemma equalizer_eq_iff :
    Subfunctor.equalizer f g = A ↔ f = g := by
  have := range_le_equalizer_iff f g (𝟙 _)
  simp only [Category.id_comp, range_ι] at this
  rw [← this]
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm (equalizer_le f g) h

/--
Definition of `equalizer.ι` / `equalizer.ι` 的定义

English:
definition equalizer.ι
  signature: : (Subfunctor.equalizer f g).toFunctor ⟶ A.toFunctor
  body: homOfLe (equalizer_le f g)

中文:
定义 equalizer.ι
  签名: : (子函子.equalizer f g).toFunctor ⟶ A.toFunctor
  定义体: homOfLe (equalizer_le f g)
-/
def equalizer.ι : (Subfunctor.equalizer f g).toFunctor ⟶ A.toFunctor :=
  homOfLe (equalizer_le f g)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (equalizer.ι f g)
  body: by
  dsimp [equalizer.ι]
  infer_instance

@[reassoc (attr := simp)]

中文:
实例 :
  签名: 单态射 (equalizer.ι f g)
  定义体: by
  dsimp [equalizer.ι]
  infer_instance

@[reassoc (attr := simp)]

Depends on / 依赖: equalizer, infer_instance
-/
instance : Mono (equalizer.ι f g) := by
  dsimp [equalizer.ι]
  infer_instance

@[reassoc (attr := simp)]
/--
lemma `equalizer.ι_ι` / 引理 `equalizer.ι_ι`

English:
lemma equalizer.ι_ι
  statement: equalizer.ι f g ≫ A.ι = (Subfunctor.equalizer f g).ι
  proof: rfl

@[reassoc]

中文:
引理 equalizer.ι_ι
  结论: equalizer.ι f g ≫ A.ι = (子函子.equalizer f g).ι
  证明: rfl

@[reassoc]
-/
lemma equalizer.ι_ι : equalizer.ι f g ≫ A.ι = (Subfunctor.equalizer f g).ι := rfl

@[reassoc]
/--
lemma `equalizer.condition` / 引理 `equalizer.condition`

English:
lemma equalizer.condition
  statement: equalizer.ι f g ≫ f = equalizer.ι f g ≫ g
  proof: by
  simp [← range_le_equalizer_iff]

中文:
引理 equalizer.condition
  结论: equalizer.ι f g ≫ f = equalizer.ι f g ≫ g
  证明: by
  simp [← range_le_equalizer_iff]
-/
lemma equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g := by
  simp [← range_le_equalizer_iff]

/--
Definition of `equalizer.lift` / `equalizer.lift` 的定义

English:
definition equalizer.lift
  signature: {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
  body: Subfunctor.lift (φ ≫ A.ι) (by simpa only [range_le_equalizer_iff] using w)

@[reassoc (attr := simp)]

中文:
定义 equalizer.lift
  签名: {G : C ⥤ 类型 w} (φ : G ⟶ A.toFunctor)
  定义体: Subfunctor.lift (φ ≫ A.ι) (by simpa only [range_le_equalizer_iff] using w)

@[reassoc (attr := simp)]
-/
def equalizer.lift {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
    (w : φ ≫ f = φ ≫ g) :
    G ⟶ (Subfunctor.equalizer f g).toFunctor :=
  Subfunctor.lift (φ ≫ A.ι) (by simpa only [range_le_equalizer_iff] using w)

@[reassoc (attr := simp)]
/--
lemma `equalizer.lift_ι'` / 引理 `equalizer.lift_ι'`

English:
lemma equalizer.lift_ι'
  statement: {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 equalizer.lift_ι'
  结论: {G : C ⥤ 类型 w} (φ : G ⟶ A.toFunctor)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma equalizer.lift_ι' {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
    (w : φ ≫ f = φ ≫ g) :
    equalizer.lift f g φ w ≫ (Subfunctor.equalizer f g).ι = φ ≫ A.ι :=
  rfl

@[reassoc (attr := simp)]
/--
lemma `equalizer.lift_ι` / 引理 `equalizer.lift_ι`

English:
lemma equalizer.lift_ι
  statement: {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
  proof: rfl

中文:
引理 equalizer.lift_ι
  结论: {G : C ⥤ 类型 w} (φ : G ⟶ A.toFunctor)
  证明: rfl
-/
lemma equalizer.lift_ι {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
    (w : φ ≫ f = φ ≫ g) :
    equalizer.lift f g φ w ≫ equalizer.ι f g = φ :=
  rfl

/-- The (limit) fork which expresses `(Subfunctor.equalizer f g).toFunctor` as
the equalizer of `f` and `g`. -/
@[simps! pt]
/--
Definition of `equalizer.fork` / `equalizer.fork` 的定义

English:
definition equalizer.fork
  signature: : Limits.Fork f g
  body: Limits.Fork.ofι (equalizer.ι f g) (equalizer.condition f g)

@[simp]

中文:
定义 equalizer.fork
  签名: : Limits.叉 f g
  定义体: Limits.Fork.ofι (equalizer.ι f g) (equalizer.condition f g)

@[simp]
-/
def equalizer.fork : Limits.Fork f g :=
  Limits.Fork.ofι (equalizer.ι f g) (equalizer.condition f g)

@[simp]
/--
lemma `equalizer.fork_ι` / 引理 `equalizer.fork_ι`

English:
lemma equalizer.fork_ι
  proof: rfl

中文:
引理 equalizer.fork_ι
  证明: rfl
-/
lemma equalizer.fork_ι :
    (equalizer.fork f g).ι = equalizer.ι f g := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `equalizer.forkIsLimit` / `equalizer.forkIsLimit` 的定义

English:
definition equalizer.forkIsLimit
  signature: : Limits.IsLimit (equalizer.fork f g)
  body: Limits.Fork.IsLimit.mk _
    (fun s => equalizer.lift _ _ s.ι s.condition)
    (fun s => by dsimp)
    (fun s m hm => by simp [← cancel_mono (Subfunctor.equalizer f g).ι, ← hm])

中文:
定义 equalizer.forkIsLimit
  签名: : Limits.是极限 (equalizer.fork f g)
  定义体: Limits.Fork.IsLimit.mk _
    (fun s => equalizer.lift _ _ s.ι s.condition)
    (fun s => by dsimp)
    (fun s m hm => by simp [← cancel_mono (Subfunctor.equalizer f g).ι, ← hm])

Depends on / 依赖: IsLimit, Limits, Limits.Fork.IsLimit.mk, Subfunctor, Subfunctor.equalizer, cancel_mono, condition, equalizer, equalizer.lift, s.condition
-/
def equalizer.forkIsLimit : Limits.IsLimit (equalizer.fork f g) :=
  Limits.Fork.IsLimit.mk _
    (fun s => equalizer.lift _ _ s.ι s.condition)
    (fun s => by dsimp)
    (fun s m hm => by simp [← cancel_mono (Subfunctor.equalizer f g).ι, ← hm])

end Subfunctor

end CategoryTheory
