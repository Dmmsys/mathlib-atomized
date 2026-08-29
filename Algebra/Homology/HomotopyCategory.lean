/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
public import Mathlib.CategoryTheory.Quotient.Linear
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The homotopy category

`HomotopyCategory V c` gives the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic.
-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

/--
Definition of `homotopic` / `homotopic` 的定义

English:
definition homotopic
  signature: : HomRel (HomologicalComplex V c)
  body: fun _ _ f g => Nonempty (Homotopy f g)

中文:
定义 homotopic
  签名: : HomRel (同调复形 V c)
  定义体: fun _ _ f g => Nonempty (Homotopy f g)

Depends on / 依赖: Homotopy, Nonempty
-/
def homotopic : HomRel (HomologicalComplex V c) := fun _ _ f g => Nonempty (Homotopy f g)

/--
Instance `homotopy_congruence` / 实例 `homotopy_congruence`

English:
instance homotopy_congruence
  signature: : Congruence (homotopic V c) where
  body: { refl := fun C => ⟨Homotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

中文:
实例 homotopy_congruence
  签名: : 余ngruence (homotopic V c) where
  定义体: { refl := fun C => ⟨Homotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

Depends on / 依赖: Homotopy, Homotopy.refl, compLeft, compRight, comp_left, comp_right, i.compLeft, i.compRight, w.symm
-/
instance homotopy_congruence : Congruence (homotopic V c) where
  equivalence :=
    { refl := fun C => ⟨Homotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

/--
Definition of `HomotopyCategory` / `HomotopyCategory` 的定义

English:
definition HomotopyCategory
  body: CategoryTheory.Quotient (homotopic V c)

中文:
定义 HomotopyCategory
  定义体: CategoryTheory.Quotient (homotopic V c)

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient, Quotient, homotopic
-/
def HomotopyCategory :=
  CategoryTheory.Quotient (homotopic V c)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (HomotopyCategory V c)
  body: inferInstanceAs Category (CategoryTheory.Quotient (homotopic V c))

中文:
实例 :
  签名: 范畴 (HomotopyCategory V c)
  定义体: inferInstanceAs Category (CategoryTheory.Quotient (homotopic V c))

Depends on / 依赖: Category, CategoryTheory, CategoryTheory.Quotient, Quotient, homotopic
-/
instance : Category (HomotopyCategory V c) :=
inferInstanceAs Category (CategoryTheory.Quotient (homotopic V c))

namespace HomotopyCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (CategoryTheory.Quotient (homotopic V c))
  body: Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨Homotopy.add h h'⟩)

中文:
实例 :
  签名: 预加性 (范畴论.商 (homotopic V c))
  定义体: Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨Homotopy.add h h'⟩)

Depends on / 依赖: Homotopy, Homotopy.add, Quotient, Quotient.preadditive, preadditive
-/
instance : Preadditive (CategoryTheory.Quotient (homotopic V c)) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨Homotopy.add h h'⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (HomotopyCategory V c)
  body: inferInstanceAs Preadditive (CategoryTheory.Quotient (homotopic V c))

中文:
实例 :
  签名: 预加性 (HomotopyCategory V c)
  定义体: inferInstanceAs Preadditive (CategoryTheory.Quotient (homotopic V c))

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient, Preadditive, Quotient, homotopic
-/
instance : Preadditive (HomotopyCategory V c) :=
inferInstanceAs Preadditive (CategoryTheory.Quotient (homotopic V c))

/--
Definition of `quotient` / `quotient` 的定义

English:
definition quotient
  signature: : HomologicalComplex V c ⥤ HomotopyCategory V c
  body: CategoryTheory.Quotient.functor _

中文:
定义 quotient
  签名: : 同调复形 V c ⥤ HomotopyCategory V c
  定义体: CategoryTheory.Quotient.functor _

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.functor, Quotient, functor
-/
def quotient : HomologicalComplex V c ⥤ HomotopyCategory V c :=
  CategoryTheory.Quotient.functor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quotient V c).Full
  body: Quotient.full_functor _

中文:
实例 :
  签名: (quotient V c).满
  定义体: Quotient.full_functor _

Depends on / 依赖: Quotient, Quotient.full_functor, full_functor
-/
instance : (quotient V c).Full := Quotient.full_functor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quotient V c).EssSurj
  body: Quotient.essSurj_functor _

中文:
实例 :
  签名: (quotient V c).本质满射
  定义体: Quotient.essSurj_functor _

Depends on / 依赖: Quotient, Quotient.essSurj_functor, essSurj_functor
-/
instance : (quotient V c).EssSurj := Quotient.essSurj_functor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quotient V c).Additive

中文:
实例 :
  签名: (quotient V c).加性
-/
instance : (quotient V c).Additive where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Additive (Quotient.functor (homotopic V c))

中文:
实例 :
  签名: 函子.加性 (商.functor (homotopic V c))
-/
instance : Functor.Additive (Quotient.functor (homotopic V c)) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Linear
  signature: R V] : Linear R (HomotopyCategory V c)
  body: Quotient.linear R (homotopic V c) (fun _ _ _ _ _ h => ⟨h.some.smul _⟩)

中文:
实例 [线性
  签名: R V] : 线性 R (HomotopyCategory V c)
  定义体: Quotient.linear R (homotopic V c) (fun _ _ _ _ _ h => ⟨h.some.smul _⟩)

Depends on / 依赖: Quotient, Quotient.linear, h.some.smul, homotopic, linear
-/
instance [Linear R V] : Linear R (HomotopyCategory V c) :=
  Quotient.linear R (homotopic V c) (fun _ _ _ _ _ h => ⟨h.some.smul _⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Linear
  signature: R V] : Functor.Linear R (quotient V c)
  body: Quotient.linear_functor _ (homotopic V c) _

中文:
实例 [线性
  签名: R V] : 函子.线性 R (quotient V c)
  定义体: Quotient.linear_functor _ (homotopic V c) _

Depends on / 依赖: Quotient, Quotient.linear_functor, homotopic, linear_functor
-/
instance [Linear R V] : Functor.Linear R (quotient V c) :=
  Quotient.linear_functor _ (homotopic V c) _

open ZeroObject

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: V] : Inhabited (HomotopyCategory V c)
  body: ⟨(quotient V c).obj 0⟩

中文:
实例 [有ZeroObject
  签名: V] : 可居 (HomotopyCategory V c)
  定义体: ⟨(quotient V c).obj 0⟩

Depends on / 依赖: quotient
-/
instance [HasZeroObject V] : Inhabited (HomotopyCategory V c) :=
  ⟨(quotient V c).obj 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: V] : HasZeroObject (HomotopyCategory V c)
  body: ⟨(quotient V c).obj 0, by
    rw [IsZero.iff_id_eq_zero]; rw [← (quotient V c).map_id]; rw [id_zero]; rw [Functor.map_zero]⟩

中文:
实例 [有ZeroObject
  签名: V] : 有ZeroObject (HomotopyCategory V c)
  定义体: ⟨(quotient V c).obj 0, by
    rw [IsZero.iff_id_eq_zero]; rw [← (quotient V c).map_id]; rw [id_zero]; rw [Functor.map_zero]⟩

Depends on / 依赖: Functor, Functor.map_zero, IsZero, IsZero.iff_id_eq_zero, id_zero, iff_id_eq_zero, map_id, map_zero, quotient
-/
instance [HasZeroObject V] : HasZeroObject (HomotopyCategory V c) :=
  ⟨(quotient V c).obj 0, by
    rw [IsZero.iff_id_eq_zero]; rw [← (quotient V c).map_id]; rw [id_zero]; rw [Functor.map_zero]⟩

instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (quotient V c)).Full :=
  Quotient.full_whiskeringLeft_functor _ _

instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (quotient V c)).Faithful :=
  Quotient.faithful_whiskeringLeft_functor _ _

variable {V c}

/--
lemma `quotient_obj_surjective` / 引理 `quotient_obj_surjective`

English:
lemma quotient_obj_surjective
  given: (X : HomotopyCategory V c)
  proof: ⟨_, rfl⟩

中文:
引理 quotient_obj_surjective
  条件: (X : HomotopyCategory V c)
  证明: ⟨_, rfl⟩
-/
lemma quotient_obj_surjective (X : HomotopyCategory V c) :
    exists (K : HomologicalComplex V c), (quotient _ _).obj K = X :=
  ⟨_, rfl⟩

-- Not `@[simp]` because it hinders the automatic application of the more useful `quotient_map_out`
/--
theorem `quotient_obj_as` / 定理 `quotient_obj_as`

English:
theorem quotient_obj_as
  given: (C : HomologicalComplex V c)
  statement: ((quotient V c).obj C).as = C
  proof: rfl

@[simp]

中文:
定理 quotient_obj_as
  条件: (C : 同调复形 V c)
  结论: ((quotient V c).obj C).as = C
  证明: rfl

@[simp]
-/
theorem quotient_obj_as (C : HomologicalComplex V c) : ((quotient V c).obj C).as = C :=
  rfl

@[simp]
/--
theorem `quotient_map_out` / 定理 `quotient_map_out`

English:
theorem quotient_map_out
  given: {C D : HomotopyCategory V c} (f : C ⟶ D)
  statement: (quotient V c).map f.out = f
  proof: Quot.out_eq _

中文:
定理 quotient_map_out
  条件: {C D : HomotopyCategory V c} (f : C ⟶ D)
  结论: (quotient V c).map f.out = f
  证明: Quot.out_eq _

Depends on / 依赖: Quot.out_eq, out_eq
-/
theorem quotient_map_out {C D : HomotopyCategory V c} (f : C ⟶ D) : (quotient V c).map f.out = f :=
  Quot.out_eq _

/--
theorem `quot_mk_eq_quotient_map` / 定理 `quot_mk_eq_quotient_map`

English:
theorem quot_mk_eq_quotient_map
  given: {C D : HomologicalComplex V c} (f : C ⟶ D)
  proof: rfl

中文:
定理 quot_mk_eq_quotient_map
  条件: {C D : 同调复形 V c} (f : C ⟶ D)
  证明: rfl
-/
theorem quot_mk_eq_quotient_map {C D : HomologicalComplex V c} (f : C ⟶ D) :
    Quot.mk _ f = (quotient V c).map f := rfl

/--
theorem `eq_of_homotopy` / 定理 `eq_of_homotopy`

English:
theorem eq_of_homotopy
  given: {C D : HomologicalComplex V c} (f g : C ⟶ D) (h : Homotopy f g)
  proof: CategoryTheory.Quotient.sound _ ⟨h⟩

中文:
定理 eq_of_homotopy
  条件: {C D : 同调复形 V c} (f g : C ⟶ D) (h : 同伦 f g)
  证明: CategoryTheory.Quotient.sound _ ⟨h⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, Quotient
-/
theorem eq_of_homotopy {C D : HomologicalComplex V c} (f g : C ⟶ D) (h : Homotopy f g) :
    (quotient V c).map f = (quotient V c).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/--
Definition of `homotopyOfEq` / `homotopyOfEq` 的定义

English:
definition homotopyOfEq
  signature: {C D : HomologicalComplex V c} (f g : C ⟶ D)
  body: ((Quotient.functor_map_eq_iff _ _ _).mp w).some

中文:
定义 homotopyOfEq
  签名: {C D : 同调复形 V c} (f g : C ⟶ D)
  定义体: ((Quotient.functor_map_eq_iff _ _ _).mp w).some

Depends on / 依赖: Quotient, Quotient.functor_map_eq_iff, functor_map_eq_iff
-/
def homotopyOfEq {C D : HomologicalComplex V c} (f g : C ⟶ D)
    (w : (quotient V c).map f = (quotient V c).map g) : Homotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some

/--
lemma `quotient_map_eq_zero_iff` / 引理 `quotient_map_eq_zero_iff`

English:
lemma quotient_map_eq_zero_iff
  given: {C D : HomologicalComplex V c} (f : C ⟶ D)
  proof: ⟨fun h => ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ => by simpa using eq_of_homotopy _ _ h⟩

中文:
引理 quotient_map_eq_zero_iff
  条件: {C D : 同调复形 V c} (f : C ⟶ D)
  证明: ⟨fun h => ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ => by simpa using eq_of_homotopy _ _ h⟩

Depends on / 依赖: eq_of_homotopy, homotopyOfEq
-/
lemma quotient_map_eq_zero_iff {C D : HomologicalComplex V c} (f : C ⟶ D) :
    (quotient V c).map f = 0 ↔ Nonempty (Homotopy f 0) :=
  ⟨fun h => ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ => by simpa using eq_of_homotopy _ _ h⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `homotopyOutMap` / `homotopyOutMap` 的定义

English:
definition homotopyOutMap
  signature: {C D : HomologicalComplex V c} (f : C ⟶ D)
  body: by
  apply homotopyOfEq
  simp

中文:
定义 homotopyOutMap
  签名: {C D : 同调复形 V c} (f : C ⟶ D)
  定义体: by
  apply homotopyOfEq
  simp

Depends on / 依赖: homotopyOfEq
-/
def homotopyOutMap {C D : HomologicalComplex V c} (f : C ⟶ D) :
    Homotopy ((quotient V c).map f).out f := by
  apply homotopyOfEq
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `quotient_map_out_comp_out` / 定理 `quotient_map_out_comp_out`

English:
theorem quotient_map_out_comp_out
  given: {C D E : HomotopyCategory V c} (f : C ⟶ D) (g : D ⟶ E)
  proof: by simp

中文:
定理 quotient_map_out_comp_out
  条件: {C D E : HomotopyCategory V c} (f : C ⟶ D) (g : D ⟶ E)
  证明: by simp
-/
theorem quotient_map_out_comp_out {C D E : HomotopyCategory V c} (f : C ⟶ D) (g : D ⟶ E) :
    (quotient V c).map (Quot.out f ≫ Quot.out g) = f ≫ g := by simp

/-- Homotopy equivalent complexes become isomorphic in the homotopy category. -/
@[simps]
/--
Definition of `isoOfHomotopyEquiv` / `isoOfHomotopyEquiv` 的定义

English:
definition isoOfHomotopyEquiv
  signature: {C D : HomologicalComplex V c} (f : HomotopyEquiv C D)
  body: (quotient V c).map f.hom
  inv := (quotient V c).map f.inv
  hom_inv_id := by
    rw [← (quotient V c).map_comp]; rw [← (quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopyHomInvId
  inv_hom_id := by
    rw [← (quotient V c).map_comp]; rw [← (quotient V c).map_id]
    exact eq_of_homotopy 

中文:
定义 isoOfHomotopyEquiv
  签名: {C D : 同调复形 V c} (f : 同伦等价 C D)
  定义体: (quotient V c).map f.hom
  inv := (quotient V c).map f.inv
  hom_inv_id := by
    rw [← (quotient V c).map_comp]; rw [← (quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopyHomInvId
  inv_hom_id := by
    rw [← (quotient V c).map_comp]; rw [← (quotient V c).map_id]
    exact eq_of_homotopy 

Depends on / 依赖: f.hom, quotient
-/
def isoOfHomotopyEquiv {C D : HomologicalComplex V c} (f : HomotopyEquiv C D) :
    (quotient V c).obj C ≅ (quotient V c).obj D where
  hom := (quotient V c).map f.hom
  inv := (quotient V c).map f.inv
  hom_inv_id := by
    rw [← (quotient V c).map_comp]; rw [← (quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopyHomInvId
  inv_hom_id := by
    rw [← (quotient V c).map_comp]; rw [← (quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopyInvHomId

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `homotopyEquivOfIso` / `homotopyEquivOfIso` 的定义

English:
definition homotopyEquivOfIso
  signature: {C D : HomologicalComplex V c}
  body: Quot.out i.hom
  inv := Quot.out i.inv
  homotopyHomInvId :=
    homotopyOfEq _ _
      (by rw [quotient_map_out_comp_out, i.hom_inv_id, (quotient V c).map_id])
  homotopyInvHomId :=
    homotopyOfEq _ _
      (by rw [quotient_map_out_comp_out, i.inv_hom_id, (quotient V c).map_id])

中文:
定义 homotopyEquivOfIso
  签名: {C D : 同调复形 V c}
  定义体: Quot.out i.hom
  inv := Quot.out i.inv
  homotopyHomInvId :=
    homotopyOfEq _ _
      (by rw [quotient_map_out_comp_out, i.hom_inv_id, (quotient V c).map_id])
  homotopyInvHomId :=
    homotopyOfEq _ _
      (by rw [quotient_map_out_comp_out, i.inv_hom_id, (quotient V c).map_id])

Depends on / 依赖: Quot.out, i.hom
-/
def homotopyEquivOfIso {C D : HomologicalComplex V c}
    (i : (quotient V c).obj C ≅ (quotient V c).obj D) : HomotopyEquiv C D where
  hom := Quot.out i.hom
  inv := Quot.out i.inv
  homotopyHomInvId :=
    homotopyOfEq _ _
      (by rw [quotient_map_out_comp_out, i.hom_inv_id, (quotient V c).map_id])
  homotopyInvHomId :=
    homotopyOfEq _ _
      (by rw [quotient_map_out_comp_out, i.inv_hom_id, (quotient V c).map_id])

variable (V c) in
/--
lemma `quotient_inverts_homotopyEquivalences` / 引理 `quotient_inverts_homotopyEquivalences`

English:
lemma quotient_inverts_homotopyEquivalences
  proof: by
  rintro K L _ ⟨e, rfl⟩
  change IsIso (isoOfHomotopyEquiv e).hom
  infer_instance

中文:
引理 quotient_inverts_homotopyEquivalences
  证明: by
  rintro K L _ ⟨e, rfl⟩
  change IsIso (isoOfHomotopyEquiv e).hom
  infer_instance

Depends on / 依赖: infer_instance, isoOfHomotopyEquiv
-/
lemma quotient_inverts_homotopyEquivalences :
    (HomologicalComplex.homotopyEquivalences V c).IsInvertedBy (quotient V c) := by
  rintro K L _ ⟨e, rfl⟩
  change IsIso (isoOfHomotopyEquiv e).hom
  infer_instance

variable (V c) in
/--
lemma `inverseImage_quotient_isomorphisms` / 引理 `inverseImage_quotient_isomorphisms`

English:
lemma inverseImage_quotient_isomorphisms
  proof: by
  ext K L f
  simp only [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]
  refine ⟨fun _ => ?_, fun hf => quotient_inverts_homotopyEquivalences _ _ _ hf⟩
  obtain ⟨g, hg⟩ := (quotient V c).map_surjective (inv ((quotient _ _).map f))
  exact ⟨{
    hom := f
    inv := g
    h

中文:
引理 inverseImage_quotient_isomorphisms
  证明: by
  ext K L f
  simp only [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]
  refine ⟨fun _ => ?_, fun hf => quotient_inverts_homotopyEquivalences _ _ _ hf⟩
  obtain ⟨g, hg⟩ := (quotient V c).map_surjective (inv ((quotient _ _).map f))
  exact ⟨{
    hom := f
    inv := g
    h

Depends on / 依赖: MorphismProperty, MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff, homotopyHomInvId, homotopyInvHomId, homotopyOfEq, inverseImage_iff, isomorphisms, map_surjective, quotient, quotient_inverts_homotopyEquivalences
-/
lemma inverseImage_quotient_isomorphisms :
    (MorphismProperty.isomorphisms _).inverseImage (HomotopyCategory.quotient V c) =
      homotopyEquivalences V c := by
  ext K L f
  simp only [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]
  refine ⟨fun _ => ?_, fun hf => quotient_inverts_homotopyEquivalences _ _ _ hf⟩
  obtain ⟨g, hg⟩ := (quotient V c).map_surjective (inv ((quotient _ _).map f))
  exact ⟨{
    hom := f
    inv := g
    homotopyHomInvId := homotopyOfEq _ _ (by simp [hg])
    homotopyInvHomId := homotopyOfEq _ _ (by simp [hg]) }, rfl⟩

/--
lemma `isZero_quotient_obj_iff` / 引理 `isZero_quotient_obj_iff`

English:
lemma isZero_quotient_obj_iff
  given: (C : HomologicalComplex V c)
  proof: by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    exact ⟨(homotopyOfEq _ _ (by simp [h]))⟩
  · rintro ⟨h⟩
    simpa using (eq_of_homotopy _ _ h)

中文:
引理 isZero_quotient_obj_iff
  条件: (C : 同调复形 V c)
  证明: by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    exact ⟨(homotopyOfEq _ _ (by simp [h]))⟩
  · rintro ⟨h⟩
    simpa using (eq_of_homotopy _ _ h)

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, eq_of_homotopy, homotopyOfEq, iff_id_eq_zero
-/
lemma isZero_quotient_obj_iff (C : HomologicalComplex V c) :
    IsZero ((quotient _ _).obj C) ↔ Nonempty (Homotopy (𝟙 C) 0) := by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    exact ⟨(homotopyOfEq _ _ (by simp [h]))⟩
  · rintro ⟨h⟩
    simpa using (eq_of_homotopy _ _ h)

variable (V c)

section

variable [CategoryWithHomology V]

/--
Definition of `homologyFunctor` / `homologyFunctor` 的定义

English:
definition homologyFunctor
  signature: (i : ι)
  body: CategoryTheory.Quotient.lift _ (HomologicalComplex.homologyFunctor V c i) (by
    rintro K L f g ⟨h⟩
    exact h.homologyMap_eq i)

中文:
定义 homologyFunctor
  签名: (i : ι)
  定义体: CategoryTheory.Quotient.lift _ (HomologicalComplex.homologyFunctor V c i) (by
    rintro K L f g ⟨h⟩
    exact h.homologyMap_eq i)

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.lift, HomologicalComplex, HomologicalComplex.homologyFunctor, Quotient, h.homologyMap_eq, homologyFunctor, homologyMap_eq
-/
noncomputable def homologyFunctor (i : ι) : HomotopyCategory V c ⥤ V :=
  CategoryTheory.Quotient.lift _ (HomologicalComplex.homologyFunctor V c i) (by
    rintro K L f g ⟨h⟩
    exact h.homologyMap_eq i)

/--
Definition of `homologyFunctorFactors` / `homologyFunctorFactors` 的定义

English:
definition homologyFunctorFactors
  signature: (i : ι)
  body: Quotient.lift.isLift _ _ _

中文:
定义 homologyFunctorFactors
  签名: (i : ι)
  定义体: Quotient.lift.isLift _ _ _

Depends on / 依赖: Quotient, Quotient.lift.isLift, isLift
-/
noncomputable def homologyFunctorFactors (i : ι) :
    quotient V c ⋙ homologyFunctor V c i ≅
      HomologicalComplex.homologyFunctor V c i :=
  Quotient.lift.isLift _ _ _

-- this is to prevent any abuse of defeq
attribute [irreducible] homologyFunctor homologyFunctorFactors

instance (i : ι) : (homologyFunctor V c i).Additive := by
  have := Functor.additive_of_iso (homologyFunctorFactors V c i).symm
  exact Functor.additive_of_full_essSurj_comp (quotient V c) _

end

end HomotopyCategory

namespace CategoryTheory

variable {V} {W : Type*} [Category* W] [Preadditive W]

/-- An additive functor induces a functor between homotopy categories. -/
@[simps! obj]
/--
Definition of `Functor.mapHomotopyCategory` / `Functor.mapHomotopyCategory` 的定义

English:
definition Functor.mapHomotopyCategory
  signature: (F : V ⥤ W) [F.Additive] (c : ComplexShape ι)
  body: CategoryTheory.Quotient.lift _ (F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c)
    (fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy h))

@[simp]

中文:
定义 函子.mapHomotopyCategory
  签名: (F : V ⥤ W) [F.加性] (c : 余mplexShape ι)
  定义体: CategoryTheory.Quotient.lift _ (F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c)
    (fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy h))

@[simp]

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.lift, F.mapHomologicalComplex, F.mapHomotopy, HomotopyCategory, HomotopyCategory.eq_of_homotopy, HomotopyCategory.quotient, Quotient, eq_of_homotopy, mapHomologicalComplex, mapHomotopy, quotient
-/
def Functor.mapHomotopyCategory (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    HomotopyCategory V c ⥤ HomotopyCategory W c :=
  CategoryTheory.Quotient.lift _ (F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c)
    (fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy h))

@[simp]
/--
lemma `Functor.mapHomotopyCategory_map` / 引理 `Functor.mapHomotopyCategory_map`

English:
lemma Functor.mapHomotopyCategory_map
  statement: (F : V ⥤ W) [F.Additive] {c : ComplexShape ι}
  proof: rfl

中文:
引理 函子.mapHomotopyCategory_map
  结论: (F : V ⥤ W) [F.加性] {c : 余mplexShape ι}
  证明: rfl
-/
lemma Functor.mapHomotopyCategory_map (F : V ⥤ W) [F.Additive] {c : ComplexShape ι}
    {K L : HomologicalComplex V c} (f : K ⟶ L) :
    (F.mapHomotopyCategory c).map ((HomotopyCategory.quotient V c).map f) =
      (HomotopyCategory.quotient W c).map ((F.mapHomologicalComplex c).map f) :=
  rfl

/--
Definition of `Functor.mapHomotopyCategoryFactors` / `Functor.mapHomotopyCategoryFactors` 的定义

English:
definition Functor.mapHomotopyCategoryFactors
  signature: (F : V ⥤ W) [F.Additive] (c : ComplexShape ι)
  body: CategoryTheory.Quotient.lift.isLift _ _ _

中文:
定义 函子.mapHomotopyCategoryFactors
  签名: (F : V ⥤ W) [F.加性] (c : 余mplexShape ι)
  定义体: CategoryTheory.Quotient.lift.isLift _ _ _

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.lift.isLift, Quotient, isLift
-/
def Functor.mapHomotopyCategoryFactors (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    HomotopyCategory.quotient V c ⋙ F.mapHomotopyCategory c ≅
      F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c :=
  CategoryTheory.Quotient.lift.isLift _ _ _

set_option backward.isDefEq.respectTransparency false in
-- TODO develop lifting of natural transformations for general quotient categories so that
-- `NatTrans.mapHomotopyCategory` become a particular case of it
/-- A natural transformation induces a natural transformation between
  the induced functors on the homotopy category. -/
@[simps]
/--
Definition of `NatTrans.mapHomotopyCategory` / `NatTrans.mapHomotopyCategory` 的定义

English:
definition NatTrans.mapHomotopyCategory
  signature: {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ⟶ G)
  body: (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex α c).app C.as)
  naturality := by
    rintro ⟨C⟩ ⟨D⟩ ⟨f : C ⟶ D⟩
    simp only [HomotopyCategory.quot_mk_eq_quotient_map, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp, NatTrans.naturality]

@[simp]

中文:
定义 自然变换.mapHomotopyCategory
  签名: {F G : V ⥤ W} [F.加性] [G.加性] (α : F ⟶ G)
  定义体: (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex α c).app C.as)
  naturality := by
    rintro ⟨C⟩ ⟨D⟩ ⟨f : C ⟶ D⟩
    simp only [HomotopyCategory.quot_mk_eq_quotient_map, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp, NatTrans.naturality]

@[simp]

Depends on / 依赖: C.as, HomotopyCategory, HomotopyCategory.quotient, NatTrans, NatTrans.mapHomologicalComplex, mapHomologicalComplex, quotient
-/
def NatTrans.mapHomotopyCategory {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ⟶ G)
    (c : ComplexShape ι) : F.mapHomotopyCategory c ⟶ G.mapHomotopyCategory c where
  app C := (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex α c).app C.as)
  naturality := by
    rintro ⟨C⟩ ⟨D⟩ ⟨f : C ⟶ D⟩
    simp only [HomotopyCategory.quot_mk_eq_quotient_map, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp, NatTrans.naturality]

@[simp]
/--
theorem `NatTrans.mapHomotopyCategory_id` / 定理 `NatTrans.mapHomotopyCategory_id`

English:
theorem NatTrans.mapHomotopyCategory_id
  given: (c : ComplexShape ι) (F : V ⥤ W) [F.Additive]
  proof: by cat_disch

@[simp]

中文:
定理 自然变换.mapHomotopyCategory_id
  条件: (c : 余mplexShape ι) (F : V ⥤ W) [F.加性]
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
theorem NatTrans.mapHomotopyCategory_id (c : ComplexShape ι) (F : V ⥤ W) [F.Additive] :
    NatTrans.mapHomotopyCategory (𝟙 F) c = 𝟙 (F.mapHomotopyCategory c) := by cat_disch

@[simp]
/--
theorem `NatTrans.mapHomotopyCategory_comp` / 定理 `NatTrans.mapHomotopyCategory_comp`

English:
theorem NatTrans.mapHomotopyCategory_comp
  statement: (c : ComplexShape ι) {F G H : V ⥤ W} [F.Additive]
  proof: by cat_disch

中文:
定理 自然变换.mapHomotopyCategory_comp
  结论: (c : 余mplexShape ι) {F G H : V ⥤ W} [F.加性]
  证明: by cat_disch

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.smul_, cat_disch, leftHomologyMap
-/
theorem NatTrans.mapHomotopyCategory_comp (c : ComplexShape ι) {F G H : V ⥤ W} [F.Additive]
    [G.Additive] [H.Additive] (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.mapHomotopyCategory (α ≫ β) c =
      NatTrans.mapHomotopyCategory α c ≫ NatTrans.mapHomotopyCategory β c := by cat_disch

instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    (F.mapHomotopyCategory c).Additive :=
  have := Functor.additive_of_iso (F.mapHomotopyCategoryFactors c).symm
  (HomotopyCategory.quotient V c).additive_of_full_essSurj_comp (F.mapHomotopyCategory c)

instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) [Linear R V] [Linear R W] [F.Linear R] :
    Functor.Linear R (F.mapHomotopyCategory c) :=
  have := Functor.linear_of_iso R (F.mapHomotopyCategoryFactors c).symm
  (HomotopyCategory.quotient V c).linear_of_full_essSurj_comp (F.mapHomotopyCategory c)

/--
Definition of `Functor.mapHomotopyCategoryCompIso` / `Functor.mapHomotopyCategoryCompIso` 的定义

English:
definition Functor.mapHomotopyCategoryCompIso
  signature: {W' : Type*} [Category W'] [Preadditive W']
  body: Quotient.natIsoLift _ (isoWhiskerRight (Functor.mapHomologicalComplexCompIso e c)
    (HomotopyCategory.quotient W' c))

中文:
定义 函子.mapHomotopyCategoryCompIso
  签名: {W' : 类型} [范畴 W'] [预加性 W']
  定义体: Quotient.natIsoLift _ (isoWhiskerRight (Functor.mapHomologicalComplexCompIso e c)
    (HomotopyCategory.quotient W' c))

Depends on / 依赖: Functor, Functor.mapHomologicalComplexCompIso, HomotopyCategory, HomotopyCategory.quotient, LeftHomologyMapData, LeftHomologyMapData.smul_, Quotient, Quotient.natIsoLift, cyclesMap, isoWhiskerRight, mapHomologicalComplexCompIso, natIsoLift, quotient
-/
def Functor.mapHomotopyCategoryCompIso {W' : Type*} [Category W'] [Preadditive W']
    {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] (c : ComplexShape ι) :
    F.mapHomotopyCategory c ⋙ G.mapHomotopyCategory c ≅ H.mapHomotopyCategory c :=
  Quotient.natIsoLift _ (isoWhiskerRight (Functor.mapHomologicalComplexCompIso e c)
    (HomotopyCategory.quotient W' c))

variable {c} in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Functor.preimageHomotopy` / `Functor.preimageHomotopy` 的定义

English:
definition Functor.preimageHomotopy
  body: F.preimage (H.hom i j)
  zero i j hij := F.map_injective (by simp only [map_preimage, Functor.map_zero, H.zero i j hij])
  comm i := F.map_injective (by simp [dsimp% H.comm i, dNext, prevD])

中文:
定义 函子.preimageHomotopy
  定义体: F.preimage (H.hom i j)
  zero i j hij := F.map_injective (by simp only [map_preimage, Functor.map_zero, H.zero i j hij])
  comm i := F.map_injective (by simp [dsimp% H.comm i, dNext, prevD])

Depends on / 依赖: F.preimage, H.hom, preimage
-/
def Functor.preimageHomotopy
    (F : V ⥤ W) [F.Additive] [F.Full] [F.Faithful]
    {K L : HomologicalComplex V c} {f₁ f₂ : K ⟶ L}
    (H : Homotopy ((F.mapHomologicalComplex c).map f₁) ((F.mapHomologicalComplex c).map f₂)) :
    Homotopy f₁ f₂ where
  hom i j := F.preimage (H.hom i j)
  zero i j hij := F.map_injective (by simp only [map_preimage, Functor.map_zero, H.zero i j hij])
  comm i := F.map_injective (by simp [dsimp% H.comm i, dNext, prevD])

instance (F : V ⥤ W) [F.Full] [F.Faithful] [F.Additive] :
    (F.mapHomotopyCategory c).Faithful where
  map_injective := by
    rintro ⟨K⟩ ⟨L⟩ f₁ f₂ h
    obtain ⟨f₁, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f₁
    obtain ⟨f₂, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f₂
    exact HomotopyCategory.eq_of_homotopy _ _
      (F.preimageHomotopy (HomotopyCategory.homotopyOfEq _ _ h))

instance (F : V ⥤ W) [F.Full] [F.Faithful] [F.Additive] :
    (F.mapHomotopyCategory c).Full where
  map_surjective := by
    rintro ⟨K⟩ ⟨L⟩ ⟨f⟩
    obtain ⟨g : K ⟶ L, rfl⟩ := (F.mapHomologicalComplex c).map_surjective f
    exact ⟨(HomotopyCategory.quotient V c).map g, rfl⟩

end CategoryTheory

namespace HomologicalComplex

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}

open HomotopyCategory in
/--
lemma `isIso_quotient_map_iff_homotopyEquivalences` / 引理 `isIso_quotient_map_iff_homotopyEquivalences`

English:
lemma isIso_quotient_map_iff_homotopyEquivalences
  proof: by
  refine ⟨fun _ => ?_, fun hf => quotient_inverts_homotopyEquivalences V c f hf⟩
  obtain ⟨g, hg⟩ := (quotient V c).map_surjective (inv ((quotient V c).map f))
  let e : HomotopyEquiv K L :=
    { hom := f
      inv := g
      homotopyHomInvId := HomotopyCategory.homotopyOfEq _ _ (by cat_disch)
 

中文:
引理 isIso_quotient_map_iff_homotopyEquivalences
  证明: by
  refine ⟨fun _ => ?_, fun hf => quotient_inverts_homotopyEquivalences V c f hf⟩
  obtain ⟨g, hg⟩ := (quotient V c).map_surjective (inv ((quotient V c).map f))
  let e : HomotopyEquiv K L :=
    { hom := f
      inv := g
      homotopyHomInvId := HomotopyCategory.homotopyOfEq _ _ (by cat_disch)
 

Depends on / 依赖: HomotopyCategory, HomotopyCategory.homotopyOfEq, HomotopyEquiv, cat_disch, homotopyHomInvId, homotopyInvHomId, homotopyOfEq, map_surjective, quotient, quotient_inverts_homotopyEquivalences
-/
lemma isIso_quotient_map_iff_homotopyEquivalences
    {K L : HomologicalComplex V c} (f : K ⟶ L) :
    IsIso ((quotient _ _).map f) ↔
      homotopyEquivalences _ _ f := by
  refine ⟨fun _ => ?_, fun hf => quotient_inverts_homotopyEquivalences V c f hf⟩
  obtain ⟨g, hg⟩ := (quotient V c).map_surjective (inv ((quotient V c).map f))
  let e : HomotopyEquiv K L :=
    { hom := f
      inv := g
      homotopyHomInvId := HomotopyCategory.homotopyOfEq _ _ (by cat_disch)
      homotopyInvHomId := HomotopyCategory.homotopyOfEq _ _ (by cat_disch) }
  exact ⟨e, rfl⟩

end HomologicalComplex
