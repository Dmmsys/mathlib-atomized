/-
Copyright (c) 2025 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHomProperties

/-!
# The category of finitely generated `R`-algebras

We define the category of finitely generated `R`-algebras and show it is essentially small.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

variable (R : Type u) [CommRing R]

/--
Definition of `FGAlgCat` / `FGAlgCat` 的定义

English:
abbreviation FGAlgCat
  body: ObjectProperty.FullSubcategory
  fun A : CommAlgCat.{v, u} R => Algebra.FiniteType R A

中文:
缩写 FGAlgCat
  定义体: ObjectProperty.FullSubcategory
  fun A : CommAlgCat.{v, u} R => Algebra.FiniteType R A

Depends on / 依赖: FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory
-/
abbrev FGAlgCat := ObjectProperty.FullSubcategory
  fun A : CommAlgCat.{v, u} R => Algebra.FiniteType R A

instance (A : FGAlgCat R) : Algebra.FiniteType R A.1 := A.2

/--
Definition of `FGAlgCatSkeleton` / `FGAlgCatSkeleton` 的定义

English:
structure FGAlgCatSkeleton
  parameters: : Type u where
  axioms and operations (2):
    - n : Nat
    - I : Ideal (MvPolynomial (Fin n) R)

中文:
结构 FGAlgCatSkeleton
  参数: : 类型u where
  公理与运算 (2 个):
    - n : 自然数
    - I : Ideal (MvPolynomial (Fin n) R)
-/
structure FGAlgCatSkeleton : Type u where
  /-- The number of generators. -/
  n : Nat
  /-- The defining ideal. -/
  I : Ideal (MvPolynomial (Fin n) R)

/--
Definition of `FGAlgCatSkeleton.eval` / `FGAlgCatSkeleton.eval` 的定义

English:
definition FGAlgCatSkeleton.eval
  signature: (A : FGAlgCatSkeleton R)
  body: ⟨CommAlgCat.of R (MvPolynomial (Fin A.n) R ⧸ A.I), inferInstanceAs Algebra.FiniteType _ _⟩

中文:
定义 FGAlgCatSkeleton.eval
  签名: (A : FGAlgCatSkeleton R)
  定义体: ⟨CommAlgCat.of R (MvPolynomial (Fin A.n) R ⧸ A.I), inferInstanceAs Algebra.FiniteType _ _⟩

Depends on / 依赖: Algebra, Algebra.FiniteType, CommAlgCat, CommAlgCat.of, FiniteType, MvPolynomial
-/
noncomputable def FGAlgCatSkeleton.eval (A : FGAlgCatSkeleton R) : FGAlgCat.{u} R :=
⟨CommAlgCat.of R (MvPolynomial (Fin A.n) R ⧸ A.I), inferInstanceAs Algebra.FiniteType _ _⟩

/--
lemma `Algebra.FiniteType.exists_fgAlgCatSkeleton` / 引理 `Algebra.FiniteType.exists_fgAlgCatSkeleton`

English:
lemma Algebra.FiniteType.exists_fgAlgCatSkeleton
  statement: (A : Type v) [CommRing A] [Algebra R A]
  proof: by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
  exact ⟨⟨n, RingHom.ker f⟩, ⟨(Ideal.quotientKerAlgEquivOfSurjective hf).symm⟩⟩

中文:
引理 Algebra.FiniteType.exists_fgAlgCatSkeleton
  结论: (A : 类型v) [CommRing A] [Algebra R A]
  证明: by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
  exact ⟨⟨n, RingHom.ker f⟩, ⟨(Ideal.quotientKerAlgEquivOfSurjective hf).symm⟩⟩

Depends on / 依赖: Algebra, Algebra.FiniteType.iff_quotient_mvPolynomial, FiniteType, Ideal.quotientKerAlgEquivOfSurjective, RingHom, RingHom.ker, iff_quotient_mvPolynomial, quotientKerAlgEquivOfSurjective
-/
lemma Algebra.FiniteType.exists_fgAlgCatSkeleton (A : Type v) [CommRing A] [Algebra R A]
    [h : Algebra.FiniteType R A] :
    exists (P : FGAlgCatSkeleton R), Nonempty (A ≃ₐ[R] P.eval.obj) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
  exact ⟨⟨n, RingHom.ker f⟩, ⟨(Ideal.quotientKerAlgEquivOfSurjective hf).symm⟩⟩

/--
lemma `RingHom.FiniteType.exists_smallRepr` / 引理 `RingHom.FiniteType.exists_smallRepr`

English:
lemma RingHom.FiniteType.exists_smallRepr
  statement: {S : Type v} [CommRing S] {f : R ->+* S}
  proof: by
  algebraize [f]
  obtain ⟨T, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R S
  exact ⟨T, e.symm.toRingEquiv, e.symm.toAlgHom.comp_algebraMap.symm⟩

中文:
引理 RingHom.FiniteType.exists_smallRepr
  结论: {S : 类型v} [CommRing S] {f : R ->+* S}
  证明: by
  algebraize [f]
  obtain ⟨T, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R S
  exact ⟨T, e.symm.toRingEquiv, e.symm.toAlgHom.comp_algebraMap.symm⟩

Depends on / 依赖: Algebra, Algebra.FiniteType.exists_fgAlgCatSkeleton, FiniteType, algebraize, comp_algebraMap, e.symm.toAlgHom.comp_algebraMap.symm, e.symm.toRingEquiv, exists_fgAlgCatSkeleton, toAlgHom, toRingEquiv
-/
lemma RingHom.FiniteType.exists_smallRepr {S : Type v} [CommRing S] {f : R ->+* S}
    (hf : f.FiniteType) :
    exists (T : FGAlgCatSkeleton R) (e : T.eval.obj ≃+* S), f = e.toRingHom.comp (algebraMap _ _) := by
  algebraize [f]
  obtain ⟨T, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R S
  exact ⟨T, e.symm.toRingEquiv, e.symm.toAlgHom.comp_algebraMap.symm⟩

/--
Definition of `FGAlgCat.uliftFunctor` / `FGAlgCat.uliftFunctor` 的定义

English:
definition FGAlgCat.uliftFunctor
  signature: : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R where
  body: ⟨.of R ULift A.1, .equiv inferInstance ULift.algEquiv.symm⟩
map {A B} f := ConcreteCategory.ofHom
ULift.algEquiv.symm.toAlgHom.comp f.hom.hom.comp ULift.algEquiv.toAlgHom

中文:
定义 FGAlgCat.uliftFunctor
  签名: : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R where
  定义体: ⟨.of R ULift A.1, .equiv inferInstance ULift.algEquiv.symm⟩
map {A B} f := ConcreteCategory.ofHom
ULift.algEquiv.symm.toAlgHom.comp f.hom.hom.comp ULift.algEquiv.toAlgHom

Depends on / 依赖: ULift.algEquiv.symm, algEquiv
-/
def FGAlgCat.uliftFunctor : FGAlgCat.{v} R ⥤ FGAlgCat.{max v w} R where
obj A := ⟨.of R ULift A.1, .equiv inferInstance ULift.algEquiv.symm⟩
map {A B} f := ConcreteCategory.ofHom
ULift.algEquiv.symm.toAlgHom.comp f.hom.hom.comp ULift.algEquiv.toAlgHom

/--
Definition of `FGAlgCat.fullyFaithfulUliftFunctor` / `FGAlgCat.fullyFaithfulUliftFunctor` 的定义

English:
definition FGAlgCat.fullyFaithfulUliftFunctor
  signature: : (FGAlgCat.uliftFunctor R).FullyFaithful where
  body: ConcreteCategory.ofHom ULift.algEquiv.toAlgHom.comp
      f.hom.hom.comp ULift.algEquiv.symm.toAlgHom

中文:
定义 FGAlgCat.fullyFaithfulUliftFunctor
  签名: : (FGAlgCat.uliftFunctor R).FullyFaithful where
  定义体: ConcreteCategory.ofHom ULift.algEquiv.toAlgHom.comp
      f.hom.hom.comp ULift.algEquiv.symm.toAlgHom

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, ULift.algEquiv.symm.toAlgHom, ULift.algEquiv.toAlgHom.comp, algEquiv, f.hom.hom.comp, toAlgHom
-/
def FGAlgCat.fullyFaithfulUliftFunctor : (FGAlgCat.uliftFunctor R).FullyFaithful where
  preimage {A B} f :=
ConcreteCategory.ofHom ULift.algEquiv.toAlgHom.comp
      f.hom.hom.comp ULift.algEquiv.symm.toAlgHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (FGAlgCat.uliftFunctor R).Full
  body: (FGAlgCat.fullyFaithfulUliftFunctor R).full

中文:
实例 :
  签名: (FGAlgCat.uliftFunctor R).Full
  定义体: (FGAlgCat.fullyFaithfulUliftFunctor R).full

Depends on / 依赖: FGAlgCat, FGAlgCat.fullyFaithfulUliftFunctor, fullyFaithfulUliftFunctor
-/
instance : (FGAlgCat.uliftFunctor R).Full :=
  (FGAlgCat.fullyFaithfulUliftFunctor R).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (FGAlgCat.uliftFunctor R).Faithful
  body: (FGAlgCat.fullyFaithfulUliftFunctor R).faithful

中文:
实例 :
  签名: (FGAlgCat.uliftFunctor R).Faithful
  定义体: (FGAlgCat.fullyFaithfulUliftFunctor R).faithful

Depends on / 依赖: FGAlgCat, FGAlgCat.fullyFaithfulUliftFunctor, faithful, fullyFaithfulUliftFunctor
-/
instance : (FGAlgCat.uliftFunctor R).Faithful :=
  (FGAlgCat.fullyFaithfulUliftFunctor R).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EssentiallySmall.{u} (FGAlgCat.{v} R)
  body: by
  suffices h : EssentiallySmall.{u} (FGAlgCat.{max u v} R) by
    exact essentiallySmall_of_fully_faithful (FGAlgCat.uliftFunctor R)
  rw [essentiallySmall_iff]
  refine ⟨?_, ?_⟩
  · let f := toSkeleton ∘ (FGAlgCat.uliftFunctor R).obj ∘ FGAlgCatSkeleton.eval R
    refine small_of_surjective (f :=

中文:
实例 :
  签名: EssentiallySmall.{u} (FGAlgCat.{v} R)
  定义体: by
  suffices h : EssentiallySmall.{u} (FGAlgCat.{max u v} R) by
    exact essentiallySmall_of_fully_faithful (FGAlgCat.uliftFunctor R)
  rw [essentiallySmall_iff]
  refine ⟨?_, ?_⟩
  · let f := toSkeleton ∘ (FGAlgCat.uliftFunctor R).obj ∘ FGAlgCatSkeleton.eval R
    refine small_of_surjective (f :=

Depends on / 依赖: Algebra, Algebra.FiniteType.exists_fgAlgCatSkeleton, CommAlg, EssentiallySmall, FGAlgCat, FGAlgCat.uliftFunctor, FGAlgCatSkeleton, FGAlgCatSkeleton.eval, FiniteType, Function, Function.comp_apply, ObjectProperty, ObjectProperty.isoMk, comp_apply, essentiallySmall_iff, essentiallySmall_of_fully_faithful, exists_fgAlgCatSkeleton, fromSkeleton, small_of_surjective, toSkeleton
-/
instance : EssentiallySmall.{u} (FGAlgCat.{v} R) := by
  suffices h : EssentiallySmall.{u} (FGAlgCat.{max u v} R) by
    exact essentiallySmall_of_fully_faithful (FGAlgCat.uliftFunctor R)
  rw [essentiallySmall_iff]
  refine ⟨?_, ?_⟩
  · let f := toSkeleton ∘ (FGAlgCat.uliftFunctor R).obj ∘ FGAlgCatSkeleton.eval R
    refine small_of_surjective (f := f) fun A => ?_
    simp only [Function.comp_apply, f, toSkeleton_eq_iff]
    obtain ⟨P, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R
      ((fromSkeleton (FGAlgCat R)).obj A).obj
    exact ⟨P, ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk <| ULift.algEquiv.trans e.symm)⟩⟩
  · refine ⟨fun A B => ?_⟩
    obtain ⟨PA, ⟨eA⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R A.obj
    obtain ⟨PB, ⟨eB⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R B.obj
    let f (g : A ⟶ B) (x : PA.eval.obj) : PB.eval.obj := eB (g.hom (eA.symm x))
    refine small_of_injective (f := f) fun u v h => ?_
    ext a
    obtain ⟨a, rfl⟩ := eA.symm.surjective a
    exact eB.injective (congr_fun h a)

section Under

open RingHom

/--
Definition of `FGAlgCat.equivUnder` / `FGAlgCat.equivUnder` 的定义

English:
definition FGAlgCat.equivUnder
  signature: (R : CommRingCat.{u})
  body: ⟨(commAlgCatEquivUnder R).functor.obj A.obj,
    (RingHom.finiteType_algebraMap (A := R) (B := A.obj)).mpr A.2⟩
  functor.map {A B} f := ⟨(commAlgCatEquivUnder R).functor.map f.hom, trivial, trivial⟩
  inverse.obj A := ⟨(commAlgCatEquivUnder R).inverse.obj A.1, A.2⟩
  inverse.map {A B} f := ObjectPr

中文:
定义 FGAlgCat.equivUnder
  签名: (R : CommRingCat.{u})
  定义体: ⟨(commAlgCatEquivUnder R).functor.obj A.obj,
    (RingHom.finiteType_algebraMap (A := R) (B := A.obj)).mpr A.2⟩
  functor.map {A B} f := ⟨(commAlgCatEquivUnder R).functor.map f.hom, trivial, trivial⟩
  inverse.obj A := ⟨(commAlgCatEquivUnder R).inverse.obj A.1, A.2⟩
  inverse.map {A B} f := ObjectPr

Depends on / 依赖: A.obj, commAlgCatEquivUnder, functor, functor.obj
-/
def FGAlgCat.equivUnder (R : CommRingCat.{u}) :
    FGAlgCat R ≌ MorphismProperty.Under (toMorphismProperty FiniteType) ⊤ R where
  functor.obj A := ⟨(commAlgCatEquivUnder R).functor.obj A.obj,
    (RingHom.finiteType_algebraMap (A := R) (B := A.obj)).mpr A.2⟩
  functor.map {A B} f := ⟨(commAlgCatEquivUnder R).functor.map f.hom, trivial, trivial⟩
  inverse.obj A := ⟨(commAlgCatEquivUnder R).inverse.obj A.1, A.2⟩
  inverse.map {A B} f := ObjectProperty.homMk ((commAlgCatEquivUnder R).inverse.map f.hom)
  unitIso := NatIso.ofComponents fun A =>
    ObjectProperty.isoMk _ (CommAlgCat.isoMk { toRingEquiv := .refl A.1, commutes' _ := rfl })
  counitIso := .refl _

variable {Q : MorphismProperty CommRingCat.{u}}

/--
lemma `essentiallySmall_of_le` / 引理 `essentiallySmall_of_le`

English:
lemma essentiallySmall_of_le
  given: (hQ : Q <= toMorphismProperty FiniteType) (R : CommRingCat.{u})
  proof: essentiallySmall_of_fully_faithful
    (MorphismProperty.Comma.changeProp _ _ hQ
      le_rfl le_rfl ⋙ (FGAlgCat.equivUnder R).inverse)

中文:
引理 essentiallySmall_of_le
  条件: (hQ : Q <= toMorphism命题erty FiniteType) (R : CommRingCat.{u})
  证明: essentiallySmall_of_fully_faithful
    (MorphismProperty.Comma.changeProp _ _ hQ
      le_rfl le_rfl ⋙ (FGAlgCat.equivUnder R).inverse)

Depends on / 依赖: FGAlgCat, FGAlgCat.equivUnder, MorphismProperty, MorphismProperty.Comma.changeProp, changeProp, equivUnder, essentiallySmall_of_fully_faithful, inverse, le_rfl
-/
lemma essentiallySmall_of_le (hQ : Q <= toMorphismProperty FiniteType) (R : CommRingCat.{u}) :
    EssentiallySmall.{u} (MorphismProperty.Under Q ⊤ R) :=
  essentiallySmall_of_fully_faithful
    (MorphismProperty.Comma.changeProp _ _ hQ
      le_rfl le_rfl ⋙ (FGAlgCat.equivUnder R).inverse)

end Under
