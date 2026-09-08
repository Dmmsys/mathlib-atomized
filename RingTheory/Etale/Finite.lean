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

/-- The object property of finite `R`-algebras. -/
/-
**CommAlgCat.finite** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommAlgCat`。
形式化陈述：finite : ObjectProperty (CommAlgCat.{v} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object property of finite `R`-algebras.
-/
abbrev finite : ObjectProperty (CommAlgCat.{v} R) :=
  fun S ↦ Module.Finite R S

/-- The object property of étale `R`-algebras. -/
/-
**CommAlgCat.etale** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommAlgCat`。
形式化陈述：etale : ObjectProperty (CommAlgCat.{v} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object property of étale `R`-algebras.
-/
abbrev etale : ObjectProperty (CommAlgCat.{v} R) :=
  fun S ↦ Algebra.Etale R S

/-- The object property of finite étale `R`-algebras. -/
/-
**CommAlgCat.finiteEtale** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommAlgCat`。
形式化陈述：finiteEtale : ObjectProperty (CommAlgCat.{v} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object property of finite étale `R`-algebras.
-/
abbrev finiteEtale : ObjectProperty (CommAlgCat.{v} R) :=
  finite R ⊓ etale R

/-- The category of finite étale `R`-algebras. -/
/-
**CommAlgCat.FiniteEtale** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommAlgCat`。
形式化陈述：FiniteEtale (R : Type u) [CommRing R] : Type _
参数：R : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finite étale `R`-algebras.
-/
abbrev FiniteEtale (R : Type u) [CommRing R] : Type _ :=
  (finiteEtale.{v} R).FullSubcategory
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (FiniteEtale.{v} R) (Type v) := ⟨fun R ↦ R.obj⟩
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : FiniteEtale.{v} R) : Algebra.Etale R S :=
  S.property.right
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : FiniteEtale.{v} R) : Module.Finite R S :=
  S.property.left

/-- Construct a term of `FiniteEtale R` from a finite étale `R`-algebra. -/
@[simps obj]
/-
**CommAlgCat.FiniteEtale.of** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat.FiniteEtale`。
形式化陈述：(R : Type u) →   [inst : CommRing R] →     (S : Type v) →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] → [Module.Finite R S] → [Algebra.Et
ale R S] → CommAlgCat.FiniteEtale R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a term of `FiniteEtale R` from a finite étale `R`-algebra.
-/
abbrev FiniteEtale.of (S : Type v) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.Etale R S] :
    FiniteEtale.{v} R where
  obj := .of R S
  property := ⟨‹_›, ‹_›⟩

variable {R}

/-- Construct a morphism in `FiniteEtale R` from an algebra map. -/
@[simps]
/-
**CommAlgCat.FiniteEtale.ofHom** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat.FiniteEtale
`。
形式化陈述：{R : Type u} →   [inst : CommRing R] →     {S T : Type v} →       [inst_1 
: CommRing S] →         [inst_2 : CommRing T] →           [inst_3 : Algebra R S]
 →             [inst_4 : Algebra R T] →               [inst_5 : Module.Finite R 
S] →                 [inst_6 : Algebra.Etale R S] →                   [inst_7 : 
Module.Finite R T] →                     [inst_8 : Algebra.Etale R T] →         
              (S →ₐ[R] T) → (CommAlgCat.FiniteEtale.of R S ⟶ CommAlgCat.FiniteEt
ale.of R T)
参数：S →ₐ[R] T；CommAlgCat.FiniteEtale.of R S ⟶ CommAlgCat.FiniteEtale.of R T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism in `FiniteEtale R` from an algebra map.
-/
abbrev FiniteEtale.ofHom {S T : Type v} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.Finite R S] [Algebra.Etale R S] [Module.Finite R T]
    [Algebra.Etale R T] (f : S →ₐ[R] T) :
    FiniteEtale.of R S ⟶ FiniteEtale.of R T where
  hom := CommAlgCat.ofHom f

/-- Construct an isomorphism in `FiniteEtale R` from an algebra equivalence. -/
/-
**CommAlgCat.FiniteEtale.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat.FiniteEtale
`。
形式化陈述：{R : Type u} → [inst : CommRing R] → {S T : CommAlgCat.FiniteEtale R} → (↑
S.obj ≃ₐ[R] ↑T.obj) → (S ≅ T)
参数：↑S.obj ≃ₐ[R] ↑T.obj；S ≅ T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism in `FiniteEtale R` from an algebra equivalence.
-/
abbrev FiniteEtale.isoMk {S T : FiniteEtale R} (e : S.obj ≃ₐ[R] T.obj) :
    S ≅ T :=
  ObjectProperty.isoMk _ (CommAlgCat.isoMk e)

end

/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : FiniteEtale k) : IsArtinianRing R :=
  have := Algebra.FormallyUnramified.finite_of_free k R
  isArtinian_of_tower k inferInstance

variable (Ω : Type w) [Field Ω] [Algebra R Ω]
  (S : Type w) [CommRing S] [Algebra R S] [Algebra S Ω] [IsScalarTower R S Ω]

/-- If `S` is an `R`-algebra, this is the base change functor `A ↦ S ⊗[R] A`. -/
@[expose, simps]
/-
**CommAlgCat.FiniteEtale.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat.Finite
Etale`。
形式化陈述：(R : Type u) →   [inst : CommRing R] →     (S : Type w) →       [inst_1 : 
CommRing S] →         [Algebra R S] → CategoryTheory.Functor (CommAlgCat.FiniteE
tale R) (CommAlgCat.FiniteEtale S)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is an `R`-algebra, this is the base change functor `A ↦ S ⊗[R] A`.
-/
def FiniteEtale.baseChange : FiniteEtale.{v} R ⥤ FiniteEtale.{max w v} S where
  obj A := .of S (S ⊗[R] A)
  map {A B} f := FiniteEtale.ofHom (Algebra.TensorProduct.map (.id _ _) f.hom.hom)

/-- Base change from `R` to `R` is isomorphic to the identity. -/
@[expose]
/-
**CommAlgCat.FiniteEtale.baseChangeSelfIso** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat
.FiniteEtale`。
形式化陈述：(R : Type u) →   [inst : CommRing R] → CommAlgCat.FiniteEtale.baseChange R
 R ≅ CategoryTheory.Functor.id (CommAlgCat.FiniteEtale R)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Base change from `R` to `R` is isomorphic to the identity.
-/
def FiniteEtale.baseChangeSelfIso : baseChange R R ≅ 𝟭 (FiniteEtale R) :=
  NatIso.ofComponents (fun A ↦ isoMk (Algebra.TensorProduct.lid _ _)) <| fun {A B} f ↦ by
    dsimp [baseChange]
    ext
    simp

/-- The fiber functor for finite étale `R`-algebras at the geometric point `Ω`: This is the
functor sending `S` to `R`-algebra homomorphisms `S →ₐ[R] Ω`. -/
@[expose, simps]
/-
**CommAlgCat.FiniteEtale.fiber** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat.FiniteEtale
`。
形式化陈述：(R : Type u) →   [inst : CommRing R] →     (Ω : Type w) → [inst_1 : Field 
Ω] → [Algebra R Ω] → CategoryTheory.Functor (CommAlgCat.FiniteEtale R)ᵒᵖ Fintype
Cat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber functor for finite étale `R`-algebras at the geometric point `Ω`: This
 is the
functor sending `S` to `R`-algebra homomorphisms `S →ₐ[R] Ω`.
-/
def FiniteEtale.fiber (R : Type u) [CommRing R] (Ω : Type w) [Field Ω] [Algebra R Ω] :
    (FiniteEtale.{v} R)ᵒᵖ ⥤ FintypeCat.{max v w} where
  obj S := .of (S.unop →ₐ[R] Ω)
  map {S T} f := FintypeCat.homMk (·.comp f.unop.hom.hom)

/-- If `k` is a field, this is the `Spec` functor sending a finite étale `k`-algebra `R`
to its finite prime spectrum. -/
@[expose, simps]
/-
**CommAlgCat.FiniteEtale.finiteSpec** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat.Finite
Etale`。
形式化陈述：(k : Type u) → [inst : Field k] → CategoryTheory.Functor (CommAlgCat.Finit
eEtale k)ᵒᵖ FintypeCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `k` is a field, this is the `Spec` functor sending a finite étale `k`-algebra
 `R`
to its finite prime spectrum.
-/
def FiniteEtale.finiteSpec (k : Type u) [Field k] : (FiniteEtale.{v} k)ᵒᵖ ⥤ FintypeCat.{v} where
  obj R := .of (PrimeSpectrum R.unop.obj)
  map f := FintypeCat.homMk (PrimeSpectrum.comap f.unop.hom.hom)

set_option backward.defeqAttrib.useBackward true in
/-- If the geometric point `Ω` factors through `S`, the fiber can be computed after base change
to `S`. -/
@[expose]
/-
**CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber** 是 Mathlib 中的一个定义，位于命名空间 `Comm
AlgCat.FiniteEtale`。
形式化陈述：(R : Type u) →   [inst : CommRing R] →     (Ω : Type w) →       [inst_1 : 
Field Ω] →         [inst_2 : Algebra R Ω] →           (S : Type w) →            
 [inst_3 : CommRing S] →               [inst_4 : Algebra R S] →                 
[inst_5 : Algebra S Ω] →                   [IsScalarTower R S Ω] →              
       CommAlgCat.FiniteEtale.fiber R Ω ≅                       (CommAlgCat.Fini
teEtale.baseChange R S).op.comp (CommAlgCat.FiniteEtale.fiber S Ω)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the geometric point `Ω` factors through `S`, the fiber can be computed after 
base change
to `S`.
-/
def FiniteEtale.fiberIsoBaseChangeFiber :
    FiniteEtale.fiber.{v} R Ω ≅
      (FiniteEtale.baseChange.{v} R S).op ⋙ FiniteEtale.fiber S Ω :=
  NatIso.ofComponents
    (fun A ↦ FintypeCat.equivEquivIso (Algebra.TensorProduct.liftEquivRight _ _ _ _))

/-- If `Ω` is separably closed, the fiber functor for finite étale `Ω`-algebras
is naturally isomorphic to the (finite) `Spec` functor. -/
@[expose]
/-
**CommAlgCat.FiniteEtale.fiberIsoFiniteSpec** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCa
t.FiniteEtale`。
形式化陈述：(Ω : Type w) →   [inst : Field Ω] → [IsSepClosed Ω] → CommAlgCat.FiniteEta
le.fiber Ω Ω ≅ CommAlgCat.FiniteEtale.finiteSpec Ω
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Ω` is separably closed, the fiber functor for finite étale `Ω`-algebras
is naturally isomorphic to the (finite) `Spec` functor.
-/
noncomputable def FiniteEtale.fiberIsoFiniteSpec [IsSepClosed Ω] :
    FiniteEtale.fiber Ω Ω ≅ FiniteEtale.finiteSpec Ω :=
  NatIso.ofComponents
    fun R ↦ FintypeCat.equivEquivIso (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum _ _)

/-- If `Ω` is separably closed, the fiber `S →ₐ[R] Ω`
is isomorphic to the prime spectrum of the base change `Ω ⊗[R] S`. -/
@[expose]
/-
**CommAlgCat.FiniteEtale.fiberIsoComp** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCat.Fini
teEtale`。
形式化陈述：(R : Type u) →   [inst : CommRing R] →     (Ω : Type w) →       [inst_1 : 
Field Ω] →         [inst_2 : Algebra R Ω] →           [IsSepClosed Ω] →         
    CommAlgCat.FiniteEtale.fiber R Ω ≅               (CommAlgCat.FiniteEtale.bas
eChange R Ω).op.comp (CommAlgCat.FiniteEtale.finiteSpec Ω)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Ω` is separably closed, the fiber `S →ₐ[R] Ω`
is isomorphic to the prime spectrum of the base change `Ω ⊗[R] S`.
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
/-
**CommAlgCat.FiniteEtale.equivOfIsSepClosed** 是 Mathlib 中的一个定义，位于命名空间 `CommAlgCa
t.FiniteEtale`。
形式化陈述：(Ω : Type u) → [inst : Field Ω] → [IsSepClosed Ω] → (CommAlgCat.FiniteEtal
e Ω)ᵒᵖ ≌ FintypeCat
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `Ω` is a separably closed field, the category of finite étale `Ω`-algebras is
anti-equivalent to `FintypeCat`.
-/
noncomputable def FiniteEtale.equivOfIsSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (FiniteEtale.{u} Ω)ᵒᵖ ≌ FintypeCat.{u} := .symm
  { functor.obj X := .op (.of _ (X → Ω))
    functor.map {X Y} f := .op (FiniteEtale.ofHom <| AlgHom.pi fun i ↦ Pi.evalAlgHom _ _ (f i))
    inverse := FiniteEtale.finiteSpec Ω
    counitIso :=
      NatIso.ofComponents
        (fun R ↦ (FiniteEtale.isoMk (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω R.unop)).op)
        fun {R S} f ↦ by
          apply Quiver.Hom.unop_inj
          ext x
          exact funext fun p ↦ Algebra.FormallyEtale.equivPiOfIsSepClosed_comap _ _ _
    unitIso := NatIso.ofComponents
      fun X ↦ FintypeCat.equivEquivIso <|
        (Equiv.sigmaUnique _ _).symm.trans (PrimeSpectrum.sigmaToPiHomeo _).toEquiv
    functor_unitIso_comp X := by
      dsimp [FiniteEtale.finiteSpec]
      apply Quiver.Hom.unop_inj
      ext x i
      dsimp
      rw [FintypeCat.equivEquivIso_apply_hom, FintypeCat.homMk_apply]
      dsimp
      rw [← Pi.coe_evalAlgHom Ω]
      simp [Algebra.FormallyEtale.equivPiOfIsSepClosed_comap,
        Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply] }
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Ω : Type u) [Field Ω] [IsSepClosed Ω] : (FiniteEtale.finiteSpec.{u} Ω).IsEquivalence :=
  (FiniteEtale.equivOfIsSepClosed.{u} Ω).isEquivalence_functor
/-
**CommAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Ω : Type u) [Field Ω] [IsSepClosed Ω] : (FiniteEtale.fiber.{u} Ω Ω).IsEquivalence :=
  Functor.isEquivalence_of_iso (FiniteEtale.fiberIsoFiniteSpec _).symm

end CommAlgCat

