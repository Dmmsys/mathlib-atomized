/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.RingTheory.TotallySplit

/-!
# Category of finite étale `R`-algebras

In this file we define the category of finite étale `R`-algebras over a ring `R`. For any
geometric point `Ω` of `R`, we define a fiber functor sending a finite étale `R`-algebra
`S` to the finite set of `R`-algebra homomorphisms `S →ₐ[R] Ω`.

## Main definitions

- `CommAlgCat.FiniteEtale`: The category of finite étale `R`-algebras.
- `CommAlgCat.FiniteEtale.fiber`: For a geometric point `Ω` of `R`, the fiber functor
  `S ↦ (S →ₐ[R] Ω)`.

## Main results

- `CommAlgCat.FiniteEtale.equivOfIsSepClosed`: If `R = Ω` is separably closed,
  the category of finite étale `Ω`-algebras is anti-equivalent to `FintypeCat`.
  In particular, the functor `CommAlgCat.FiniteEtale.fiber` is an equivalence
  of categories in this case.
-/

public section

open CategoryTheory TensorProduct

universe v w u

namespace CommAlgCat

variable (R : Type u) [CommRing R] (k : Type u) [Field k]

section

/--
Definition of `finite` / `finite` 的定义

English:
abbreviation finite
  signature: : ObjectProperty (CommAlgCat.{v} R)
  body: fun S => Module.Finite R S

中文:
缩写 finite
  签名: : Object命题erty (CommAlgCat.{v} R)
  定义体: fun S => Module.Finite R S

Depends on / 依赖: Finite, Module, Module.Finite
-/
abbrev finite : ObjectProperty (CommAlgCat.{v} R) :=
  fun S => Module.Finite R S

/--
Definition of `etale` / `etale` 的定义

English:
abbreviation etale
  signature: : ObjectProperty (CommAlgCat.{v} R)
  body: fun S => Algebra.Etale R S

中文:
缩写 etale
  签名: : Object命题erty (CommAlgCat.{v} R)
  定义体: fun S => Algebra.Etale R S

Depends on / 依赖: Algebra, Algebra.Etale
-/
abbrev etale : ObjectProperty (CommAlgCat.{v} R) :=
  fun S => Algebra.Etale R S

/--
Definition of `finiteEtale` / `finiteEtale` 的定义

English:
abbreviation finiteEtale
  signature: : ObjectProperty (CommAlgCat.{v} R)
  body: finite R ⊓ etale R

中文:
缩写 finiteEtale
  签名: : Object命题erty (CommAlgCat.{v} R)
  定义体: finite R ⊓ etale R

Depends on / 依赖: finite
-/
abbrev finiteEtale : ObjectProperty (CommAlgCat.{v} R) :=
  finite R ⊓ etale R

/--
Definition of `FiniteEtale` / `FiniteEtale` 的定义

English:
abbreviation FiniteEtale
  signature: (R : Type u) [CommRing R]
  body: (finiteEtale.{v} R).FullSubcategory

中文:
缩写 FiniteEtale
  签名: (R : 类型u) [CommRing R]
  定义体: (finiteEtale.{v} R).FullSubcategory

Depends on / 依赖: FullSubcategory, finiteEtale
-/
abbrev FiniteEtale (R : Type u) [CommRing R] : Type _ :=
  (finiteEtale.{v} R).FullSubcategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (FiniteEtale.{v} R) (Type v)
  body: ⟨fun R => R.obj⟩

中文:
实例 :
  签名: CoeSort (FiniteEtale.{v} R) (类型v)
  定义体: ⟨fun R => R.obj⟩

Depends on / 依赖: R.obj
-/
instance : CoeSort (FiniteEtale.{v} R) (Type v) := ⟨fun R => R.obj⟩

instance (S : FiniteEtale.{v} R) : Algebra.Etale R S :=
  S.property.right

instance (S : FiniteEtale.{v} R) : Module.Finite R S :=
  S.property.left

/-- Construct a term of `FiniteEtale R` from a finite étale `R`-algebra. -/
@[simps obj]
/--
Definition of `FiniteEtale.of` / `FiniteEtale.of` 的定义

English:
abbreviation FiniteEtale.of
  signature: (S : Type v) [CommRing S] [Algebra R S]
  body: .of R S
  property := ⟨‹_›, ‹_›⟩

中文:
缩写 FiniteEtale.of
  签名: (S : 类型v) [CommRing S] [Algebra R S]
  定义体: .of R S
  property := ⟨‹_›, ‹_›⟩
-/
abbrev FiniteEtale.of (S : Type v) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.Etale R S] :
    FiniteEtale.{v} R where
  obj := .of R S
  property := ⟨‹_›, ‹_›⟩

variable {R}

/-- Construct a morphism in `FiniteEtale R` from an algebra map. -/
@[simps]
/--
Definition of `FiniteEtale.ofHom` / `FiniteEtale.ofHom` 的定义

English:
abbreviation FiniteEtale.ofHom
  signature: {S T : Type v} [CommRing S] [CommRing T]
  body: CommAlgCat.ofHom f

中文:
缩写 FiniteEtale.ofHom
  签名: {S T : 类型v} [CommRing S] [CommRing T]
  定义体: CommAlgCat.ofHom f

Depends on / 依赖: CommAlgCat, CommAlgCat.ofHom
-/
abbrev FiniteEtale.ofHom {S T : Type v} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.Finite R S] [Algebra.Etale R S] [Module.Finite R T]
    [Algebra.Etale R T] (f : S ->ₐ[R] T) :
    FiniteEtale.of R S ⟶ FiniteEtale.of R T where
  hom := CommAlgCat.ofHom f

/--
Definition of `FiniteEtale.isoMk` / `FiniteEtale.isoMk` 的定义

English:
abbreviation FiniteEtale.isoMk
  signature: {S T : FiniteEtale R} (e : S.obj ≃ₐ[R] T.obj)
  body: ObjectProperty.isoMk _ (CommAlgCat.isoMk e)

中文:
缩写 FiniteEtale.isoMk
  签名: {S T : FiniteEtale R} (e : S.obj ≃ₐ[R] T.obj)
  定义体: ObjectProperty.isoMk _ (CommAlgCat.isoMk e)

Depends on / 依赖: CommAlgCat, CommAlgCat.isoMk, ObjectProperty, ObjectProperty.isoMk
-/
abbrev FiniteEtale.isoMk {S T : FiniteEtale R} (e : S.obj ≃ₐ[R] T.obj) :
    S ≅ T :=
  ObjectProperty.isoMk _ (CommAlgCat.isoMk e)

end

instance (R : FiniteEtale k) : IsArtinianRing R :=
  have := Algebra.FormallyUnramified.finite_of_free k R
  isArtinian_of_tower k inferInstance

variable (Ω : Type w) [Field Ω] [Algebra R Ω]
  (S : Type w) [CommRing S] [Algebra R S] [Algebra S Ω] [IsScalarTower R S Ω]

/-- If `S` is an `R`-algebra, this is the base change functor `A ↦ S ⊗[R] A`. -/
@[expose, simps]
/--
Definition of `FiniteEtale.baseChange` / `FiniteEtale.baseChange` 的定义

English:
definition FiniteEtale.baseChange
  signature: : FiniteEtale.{v} R ⥤ FiniteEtale.{max w v} S where
  body: .of S (S otimes[R] A)
  map {A B} f := FiniteEtale.ofHom (Algebra.TensorProduct.map (.id _ _) f.hom.hom)

中文:
定义 FiniteEtale.baseChange
  签名: : FiniteEtale.{v} R ⥤ FiniteEtale.{max w v} S where
  定义体: .of S (S otimes[R] A)
  map {A B} f := FiniteEtale.ofHom (Algebra.TensorProduct.map (.id _ _) f.hom.hom)

Depends on / 依赖: otimes
-/
def FiniteEtale.baseChange : FiniteEtale.{v} R ⥤ FiniteEtale.{max w v} S where
  obj A := .of S (S otimes[R] A)
  map {A B} f := FiniteEtale.ofHom (Algebra.TensorProduct.map (.id _ _) f.hom.hom)

/-- Base change from `R` to `R` is isomorphic to the identity. -/
@[expose]
/--
Definition of `FiniteEtale.baseChangeSelfIso` / `FiniteEtale.baseChangeSelfIso` 的定义

English:
definition FiniteEtale.baseChangeSelfIso
  signature: : baseChange R R ≅ 𝟭 (FiniteEtale R)
  body: NatIso.ofComponents (fun A => isoMk (Algebra.TensorProduct.lid _ _)) fun {A B} f => by
    dsimp [baseChange]
    ext
    simp

中文:
定义 FiniteEtale.baseChangeSelfIso
  签名: : baseChange R R ≅ 𝟭 (FiniteEtale R)
  定义体: NatIso.ofComponents (fun A => isoMk (Algebra.TensorProduct.lid _ _)) fun {A B} f => by
    dsimp [baseChange]
    ext
    simp

Depends on / 依赖: Algebra, Algebra.TensorProduct.lid, NatIso, NatIso.ofComponents, TensorProduct, baseChange, ofComponents
-/
def FiniteEtale.baseChangeSelfIso : baseChange R R ≅ 𝟭 (FiniteEtale R) :=
NatIso.ofComponents (fun A => isoMk (Algebra.TensorProduct.lid _ _)) fun {A B} f => by
    dsimp [baseChange]
    ext
    simp

/-- The fiber functor for finite étale `R`-algebras at the geometric point `Ω`: This is the
functor sending `S` to `R`-algebra homomorphisms `S →ₐ[R] Ω`. -/
@[expose, simps]
/--
Definition of `FiniteEtale.fiber` / `FiniteEtale.fiber` 的定义

English:
definition FiniteEtale.fiber
  signature: (R : Type u) [CommRing R] (Ω : Type w) [Field Ω] [Algebra R Ω]
  body: .of (S.unop ->ₐ[R] Ω)
  map {S T} f := FintypeCat.homMk (·.comp f.unop.hom.hom)

中文:
定义 FiniteEtale.fiber
  签名: (R : 类型u) [CommRing R] (Ω : Type w) [Field Ω] [Algebra R Ω]
  定义体: .of (S.unop ->ₐ[R] Ω)
  map {S T} f := FintypeCat.homMk (·.comp f.unop.hom.hom)

Depends on / 依赖: S.unop
-/
def FiniteEtale.fiber (R : Type u) [CommRing R] (Ω : Type w) [Field Ω] [Algebra R Ω] :
    (FiniteEtale.{v} R)ᵒᵖ ⥤ FintypeCat.{max v w} where
  obj S := .of (S.unop ->ₐ[R] Ω)
  map {S T} f := FintypeCat.homMk (·.comp f.unop.hom.hom)

/-- If `k` is a field, this is the `Spec` functor sending a finite étale `k`-algebra `R`
to its finite prime spectrum. -/
@[expose, simps]
/--
Definition of `FiniteEtale.finiteSpec` / `FiniteEtale.finiteSpec` 的定义

English:
definition FiniteEtale.finiteSpec
  signature: (k : Type u) [Field k]
  body: .of (PrimeSpectrum R.unop.obj)
  map f := FintypeCat.homMk (PrimeSpectrum.comap f.unop.hom.hom)

中文:
定义 FiniteEtale.finiteSpec
  签名: (k : 类型u) [Field k]
  定义体: .of (PrimeSpectrum R.unop.obj)
  map f := FintypeCat.homMk (PrimeSpectrum.comap f.unop.hom.hom)

Depends on / 依赖: PrimeSpectrum, R.unop.obj
-/
def FiniteEtale.finiteSpec (k : Type u) [Field k] : (FiniteEtale.{v} k)ᵒᵖ ⥤ FintypeCat.{v} where
  obj R := .of (PrimeSpectrum R.unop.obj)
  map f := FintypeCat.homMk (PrimeSpectrum.comap f.unop.hom.hom)

set_option backward.defeqAttrib.useBackward true in
/-- If the geometric point `Ω` factors through `S`, the fiber can be computed after base change
to `S`. -/
@[expose]
/--
Definition of `FiniteEtale.fiberIsoBaseChangeFiber` / `FiniteEtale.fiberIsoBaseChangeFiber` 的定义

English:
definition FiniteEtale.fiberIsoBaseChangeFiber
  signature: :
  body: NatIso.ofComponents
    (fun A => FintypeCat.equivEquivIso (Algebra.TensorProduct.liftEquivRight _ _ _ _))

中文:
定义 FiniteEtale.fiberIsoBaseChangeFiber
  签名: :
  定义体: NatIso.ofComponents
    (fun A => FintypeCat.equivEquivIso (Algebra.TensorProduct.liftEquivRight _ _ _ _))

Depends on / 依赖: Algebra, Algebra.TensorProduct.liftEquivRight, FintypeCat, FintypeCat.equivEquivIso, NatIso, NatIso.ofComponents, TensorProduct, equivEquivIso, liftEquivRight, ofComponents
-/
def FiniteEtale.fiberIsoBaseChangeFiber :
    FiniteEtale.fiber.{v} R Ω ≅
      (FiniteEtale.baseChange.{v} R S).op ⋙ FiniteEtale.fiber S Ω :=
  NatIso.ofComponents
    (fun A => FintypeCat.equivEquivIso (Algebra.TensorProduct.liftEquivRight _ _ _ _))

/-- If `Ω` is separably closed, the fiber functor for finite étale `Ω`-algebras
is naturally isomorphic to the (finite) `Spec` functor. -/
@[expose]
/--
Definition of `FiniteEtale.fiberIsoFiniteSpec` / `FiniteEtale.fiberIsoFiniteSpec` 的定义

English:
definition FiniteEtale.fiberIsoFiniteSpec
  signature: [IsSepClosed Ω]
  body: NatIso.ofComponents
    fun R => FintypeCat.equivEquivIso (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum _ _)

中文:
定义 FiniteEtale.fiberIsoFiniteSpec
  签名: [IsSepClosed Ω]
  定义体: NatIso.ofComponents
    fun R => FintypeCat.equivEquivIso (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum _ _)

Depends on / 依赖: Algebra, Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum, FintypeCat, FintypeCat.equivEquivIso, IsFiniteSplit, NatIso, NatIso.ofComponents, algHomEquivPrimeSpectrum, equivEquivIso, ofComponents
-/
noncomputable def FiniteEtale.fiberIsoFiniteSpec [IsSepClosed Ω] :
    FiniteEtale.fiber Ω Ω ≅ FiniteEtale.finiteSpec Ω :=
  NatIso.ofComponents
    fun R => FintypeCat.equivEquivIso (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum _ _)

/-- If `Ω` is separably closed, the fiber `S →ₐ[R] Ω`
is isomorphic to the prime spectrum of the base change `Ω ⊗[R] S`. -/
@[expose]
/--
Definition of `FiniteEtale.fiberIsoComp` / `FiniteEtale.fiberIsoComp` 的定义

English:
definition FiniteEtale.fiberIsoComp
  signature: [IsSepClosed Ω]
  body: fiberIsoBaseChangeFiber _ _ Ω ≪≫ Functor.isoWhiskerLeft _ (fiberIsoFiniteSpec _)

中文:
定义 FiniteEtale.fiberIsoComp
  签名: [IsSepClosed Ω]
  定义体: fiberIsoBaseChangeFiber _ _ Ω ≪≫ Functor.isoWhiskerLeft _ (fiberIsoFiniteSpec _)

Depends on / 依赖: Functor, Functor.isoWhiskerLeft, fiberIsoBaseChangeFiber, fiberIsoFiniteSpec, isoWhiskerLeft
-/
noncomputable def FiniteEtale.fiberIsoComp [IsSepClosed Ω] :
    FiniteEtale.fiber.{v} R Ω ≅
      (FiniteEtale.baseChange.{v} R Ω).op ⋙ FiniteEtale.finiteSpec.{max w v} Ω :=
  fiberIsoBaseChangeFiber _ _ Ω ≪≫ Functor.isoWhiskerLeft _ (fiberIsoFiniteSpec _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `Ω` is a separably closed field, the category of finite étale `Ω`-algebras is
anti-equivalent to `FintypeCat`. -/
@[expose, simps! functor inverse_obj inverse_map]
/--
Definition of `FiniteEtale.equivOfIsSepClosed` / `FiniteEtale.equivOfIsSepClosed` 的定义

English:
definition FiniteEtale.equivOfIsSepClosed
  signature: (Ω : Type u) [Field Ω] [IsSepClosed Ω]
  body: .symm
  { functor.obj X := .op (.of _ (X -> Ω))
    functor.map {X Y} f := .op (FiniteEtale.ofHom <| AlgHom.pi fun i => Pi.evalAlgHom _ _ (f i))
    inverse := FiniteEtale.finiteSpec Ω
    counitIso :=
      NatIso.ofComponents
        (fun R => (FiniteEtale.isoMk (Algebra.FormallyEtale.equivPiOfIsS

中文:
定义 FiniteEtale.equivOfIsSepClosed
  签名: (Ω : 类型u) [Field Ω] [IsSepClosed Ω]
  定义体: .symm
  { functor.obj X := .op (.of _ (X -> Ω))
    functor.map {X Y} f := .op (FiniteEtale.ofHom <| AlgHom.pi fun i => Pi.evalAlgHom _ _ (f i))
    inverse := FiniteEtale.finiteSpec Ω
    counitIso :=
      NatIso.ofComponents
        (fun R => (FiniteEtale.isoMk (Algebra.FormallyEtale.equivPiOfIsS
-/
noncomputable def FiniteEtale.equivOfIsSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (FiniteEtale.{u} Ω)ᵒᵖ ≌ FintypeCat.{u} := .symm
  { functor.obj X := .op (.of _ (X -> Ω))
    functor.map {X Y} f := .op (FiniteEtale.ofHom <| AlgHom.pi fun i => Pi.evalAlgHom _ _ (f i))
    inverse := FiniteEtale.finiteSpec Ω
    counitIso :=
      NatIso.ofComponents
        (fun R => (FiniteEtale.isoMk (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω R.unop)).op)
        fun {R S} f => by
          apply Quiver.Hom.unop_inj
          ext x
          exact funext fun p => Algebra.FormallyEtale.equivPiOfIsSepClosed_comap _ _ _
    unitIso := NatIso.ofComponents
fun X => FintypeCat.equivEquivIso
        (Equiv.sigmaUnique _ _).symm.trans (PrimeSpectrum.sigmaToPiHomeo _).toEquiv
    functor_unitIso_comp X := by
      dsimp [FiniteEtale.finiteSpec]
      apply Quiver.Hom.unop_inj
      ext x i
      dsimp
      rw [FintypeCat.equivEquivIso_apply_hom]; rw [FintypeCat.homMk_apply]
      dsimp
      rw [← Pi.coe_evalAlgHom Ω]
      simp [Algebra.FormallyEtale.equivPiOfIsSepClosed_comap,
        Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply] }

instance (Ω : Type u) [Field Ω] [IsSepClosed Ω] : (FiniteEtale.finiteSpec.{u} Ω).IsEquivalence :=
  (FiniteEtale.equivOfIsSepClosed.{u} Ω).isEquivalence_functor

instance (Ω : Type u) [Field Ω] [IsSepClosed Ω] : (FiniteEtale.fiber.{u} Ω Ω).IsEquivalence :=
  Functor.isEquivalence_of_iso (FiniteEtale.fiberIsoFiniteSpec _).symm

end CommAlgCat
