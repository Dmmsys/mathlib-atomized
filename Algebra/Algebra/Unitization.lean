/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Unitization of a non-unital algebra

Given a non-unital `R`-algebra `A` (given via the type classes
`[NonUnitalRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]`) we construct
the minimal unital `R`-algebra containing `A` as an ideal. This object `Unitization R A` is
a type synonym for `R × A` on which we place a different multiplicative structure, namely,
`(r₁, a₁) * (r₂, a₂) = (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂)` where the multiplicative identity
is `(1, 0)`.

Note, when `A` is a *unital* `R`-algebra, then `Unitization R A` constructs a new multiplicative
identity different from the old one, and so in general `Unitization R A` and `A` will not be
isomorphic even in the unital case. This approach actually has nice functorial properties.

There is a natural coercion from `A` to `Unitization R A` given by `fun a ↦ (0, a)`, the image
of which is a proper ideal (TODO), and when `R` is a field this ideal is maximal. Moreover,
this ideal is always an essential ideal (it has nontrivial intersection with every other nontrivial
ideal).

Every non-unital algebra homomorphism from `A` into a *unital* `R`-algebra `B` has a unique
extension to a (unital) algebra homomorphism from `Unitization R A` to `B`.

## Main definitions

* `Unitization R A`: the unitization of a non-unital `R`-algebra `A`.
* `Unitization.algebra`: the unitization of `A` as a (unital) `R`-algebra.
* `Unitization.coeNonUnitalAlgHom`: coercion as a non-unital algebra homomorphism.
* `NonUnitalAlgHom.toAlgHom φ`: the extension of a non-unital algebra homomorphism `φ : A → B`
  into a unital `R`-algebra `B` to an algebra homomorphism `Unitization R A →ₐ[R] B`.
* `Unitization.lift`: the universal property of the unitization, the extension
  `NonUnitalAlgHom.toAlgHom` actually implements an equivalence
  `(A →ₙₐ[R] B) ≃ (Unitization R A ≃ₐ[R] B)`

## Main results

* `AlgHom.ext'`: an extensionality lemma for algebra homomorphisms whose domain is
  `Unitization R A`; it suffices that they agree on `A`.

## TODO

* prove the unitization operation is a functor between the appropriate categories
* prove the image of the coercion is an essential ideal, maximal if scalars are a field.
-/

@[expose] public section


/-- The minimal unitization of a non-unital `R`-algebra `A`. This is just a structure wrapper for
`R × A`. -/
@[ext]
/--
Definition of `Unitization` / `Unitization` 的定义

English:
structure Unitization
  parameters: (R A : Type*)
  extends: R × A
  (no additional axioms)

中文:
结构 Unitization
  参数: (R A : 类型)
  继承: R × A
  (无附加公理)
-/
structure Unitization (R A : Type*) extends R × A

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `mk x` being printed as `{ toProd := x }` by `delabStructureInstance`. -/
@[app_delab Unitization.mk]
meta def Unitization.delabMk : Delab := delabApp

end Notation

namespace Unitization

section Basic

variable {R A : Type*}

/--
lemma `mk_toProd` / 引理 `mk_toProd`

English:
lemma mk_toProd
  given: (x : Unitization R A)
  statement: mk x.toProd = x
  proof: rfl

中文:
引理 mk_toProd
  条件: (x : Unitization R A)
  结论: mk x.toProd = x
  证明: rfl
-/
lemma mk_toProd (x : Unitization R A) : mk x.toProd = x := rfl
/--
lemma `toProd_mk` / 引理 `toProd_mk`

English:
lemma toProd_mk
  given: (x : R × A)
  statement: toProd (mk x) = x
  proof: rfl

中文:
引理 toProd_mk
  条件: (x : R × A)
  结论: toProd (mk x) = x
  证明: rfl
-/
lemma toProd_mk (x : R × A) : toProd (mk x) = x := rfl

/-- The canonical equivalence between `Unitization R A` and `R × A`. -/
@[simps apply symm_apply]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : Unitization R A ≃ R × A where
  body: toProd
  invFun := mk
  left_inv := mk_toProd
  right_inv := toProd_mk

中文:
定义 equiv
  签名: : Unitization R A ≃ R × A where
  定义体: toProd
  invFun := mk
  left_inv := mk_toProd
  right_inv := toProd_mk

Depends on / 依赖: toProd
-/
def equiv : Unitization R A ≃ R × A where
  toFun := toProd
  invFun := mk
  left_inv := mk_toProd
  right_inv := toProd_mk

/--
lemma `toProd_injective` / 引理 `toProd_injective`

English:
lemma toProd_injective
  statement: (toProd : Unitization R A -> R × A).Injective
  proof: equiv.injective

中文:
引理 toProd_injective
  结论: (toProd : Unitization R A -> R × A).Injective
  证明: equiv.injective

Depends on / 依赖: equiv.injective, injective
-/
lemma toProd_injective : (toProd : Unitization R A -> R × A).Injective :=
  equiv.injective

/--
lemma `toProd_surjective` / 引理 `toProd_surjective`

English:
lemma toProd_surjective
  statement: (toProd : Unitization R A -> R × A).Surjective
  proof: equiv.surjective

中文:
引理 toProd_surjective
  结论: (toProd : Unitization R A -> R × A).Surjective
  证明: equiv.surjective

Depends on / 依赖: equiv.surjective, surjective
-/
lemma toProd_surjective : (toProd : Unitization R A -> R × A).Surjective :=
  equiv.surjective

/--
lemma `toProd_bijective` / 引理 `toProd_bijective`

English:
lemma toProd_bijective
  statement: (toProd : Unitization R A -> R × A).Bijective
  proof: equiv.bijective

中文:
引理 toProd_bijective
  结论: (toProd : Unitization R A -> R × A).Bijective
  证明: equiv.bijective

Depends on / 依赖: bijective, equiv.bijective
-/
lemma toProd_bijective : (toProd : Unitization R A -> R × A).Bijective :=
  equiv.bijective

/--
lemma `mk_injective` / 引理 `mk_injective`

English:
lemma mk_injective
  statement: (mk : R × A -> Unitization R A).Injective
  proof: equiv.symm.injective

中文:
引理 mk_injective
  结论: (mk : R × A -> Unitization R A).Injective
  证明: equiv.symm.injective

Depends on / 依赖: equiv.symm.injective, injective
-/
lemma mk_injective : (mk : R × A -> Unitization R A).Injective :=
  equiv.symm.injective

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  statement: (mk : R × A -> Unitization R A).Surjective
  proof: equiv.symm.surjective

中文:
引理 mk_surjective
  结论: (mk : R × A -> Unitization R A).Surjective
  证明: equiv.symm.surjective

Depends on / 依赖: equiv.symm.surjective, surjective
-/
lemma mk_surjective : (mk : R × A -> Unitization R A).Surjective :=
  equiv.symm.surjective

/--
lemma `mk_bijective` / 引理 `mk_bijective`

English:
lemma mk_bijective
  statement: (mk : R × A -> Unitization R A).Bijective
  proof: equiv.symm.bijective

@[simp]

中文:
引理 mk_bijective
  结论: (mk : R × A -> Unitization R A).Bijective
  证明: equiv.symm.bijective

@[simp]

Depends on / 依赖: bijective, equiv.symm.bijective
-/
lemma mk_bijective : (mk : R × A -> Unitization R A).Bijective :=
  equiv.symm.bijective

@[simp]
/--
lemma `toProd_inj_iff` / 引理 `toProd_inj_iff`

English:
lemma toProd_inj_iff
  given: {x y : Unitization R A}
  statement: toProd x = toProd y ↔ x = y
  proof: toProd_injective.eq_iff

中文:
引理 toProd_inj_iff
  条件: {x y : Unitization R A}
  结论: toProd x = toProd y ↔ x = y
  证明: toProd_injective.eq_iff

Depends on / 依赖: eq_iff, toProd_injective, toProd_injective.eq_iff
-/
lemma toProd_inj_iff {x y : Unitization R A} : toProd x = toProd y ↔ x = y :=
  toProd_injective.eq_iff

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: [Zero A] (r : R)
  body: mk (r, 0)

中文:
定义 inl
  签名: [Zero A] (r : R)
  定义体: mk (r, 0)
-/
def inl [Zero A] (r : R) : Unitization R A :=
  mk (r, 0)

/-- The canonical inclusion `A → Unitization R A`. -/
@[coe]
/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: [Zero R] (a : A)
  body: mk (0, a)

中文:
定义 inr
  签名: [Zero R] (a : A)
  定义体: mk (0, a)
-/
def inr [Zero R] (a : A) : Unitization R A :=
  mk (0, a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] : Coe A (Unitization R A) where
  body: inr

中文:
实例 [Zero
  签名: R] : Coe A (Unitization R A) where
  定义体: inr
-/
instance [Zero R] : Coe A (Unitization R A) where
  coe := inr

section

variable (A)

@[simp]
/--
theorem `fst_inl` / 定理 `fst_inl`

English:
theorem fst_inl
  given: [Zero A] (r : R)
  statement: (inl r : Unitization R A).fst = r
  proof: rfl

@[simp]

中文:
定理 fst_inl
  条件: [Zero A] (r : R)
  结论: (inl r : Unitization R A).fst = r
  证明: rfl

@[simp]
-/
theorem fst_inl [Zero A] (r : R) : (inl r : Unitization R A).fst = r :=
  rfl

@[simp]
/--
theorem `snd_inl` / 定理 `snd_inl`

English:
theorem snd_inl
  given: [Zero A] (r : R)
  statement: (inl r : Unitization R A).snd = 0
  proof: rfl

中文:
定理 snd_inl
  条件: [Zero A] (r : R)
  结论: (inl r : Unitization R A).snd = 0
  证明: rfl
-/
theorem snd_inl [Zero A] (r : R) : (inl r : Unitization R A).snd = 0 :=
  rfl

end

section

variable (R)

@[simp]
/--
theorem `fst_inr` / 定理 `fst_inr`

English:
theorem fst_inr
  given: [Zero R] (a : A)
  statement: (a : Unitization R A).fst = 0
  proof: rfl

@[simp]

中文:
定理 fst_inr
  条件: [Zero R] (a : A)
  结论: (a : Unitization R A).fst = 0
  证明: rfl

@[simp]
-/
theorem fst_inr [Zero R] (a : A) : (a : Unitization R A).fst = 0 :=
  rfl

@[simp]
/--
theorem `snd_inr` / 定理 `snd_inr`

English:
theorem snd_inr
  given: [Zero R] (a : A)
  statement: (a : Unitization R A).snd = a
  proof: rfl

中文:
定理 snd_inr
  条件: [Zero R] (a : A)
  结论: (a : Unitization R A).snd = a
  证明: rfl
-/
theorem snd_inr [Zero R] (a : A) : (a : Unitization R A).snd = a :=
  rfl

end

/--
theorem `inl_injective` / 定理 `inl_injective`

English:
theorem inl_injective
  given: [Zero A]
  statement: Function.Injective (inl : R -> Unitization R A)
  proof: Function.LeftInverse.injective (g := Prod.fst ∘ toProd) fst_inl _

中文:
定理 inl_injective
  条件: [Zero A]
  结论: Function.Injective (inl : R -> Unitization R A)
  证明: Function.LeftInverse.injective (g := Prod.fst ∘ toProd) fst_inl _

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, Prod.fst, fst_inl, injective, toProd
-/
theorem inl_injective [Zero A] : Function.Injective (inl : R -> Unitization R A) :=
Function.LeftInverse.injective (g := Prod.fst ∘ toProd) fst_inl _

/--
theorem `inr_injective` / 定理 `inr_injective`

English:
theorem inr_injective
  given: [Zero R]
  statement: Function.Injective ((↑) : A -> Unitization R A)
  proof: Function.LeftInverse.injective (g := Prod.snd ∘ toProd) snd_inr _

中文:
定理 inr_injective
  条件: [Zero R]
  结论: Function.Injective ((↑) : A -> Unitization R A)
  证明: Function.LeftInverse.injective (g := Prod.snd ∘ toProd) snd_inr _

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, Prod.snd, injective, snd_inr, toProd
-/
theorem inr_injective [Zero R] : Function.Injective ((↑) : A -> Unitization R A) :=
Function.LeftInverse.injective (g := Prod.snd ∘ toProd) snd_inr _

/--
theorem `inr_inj` / 定理 `inr_inj`

English:
theorem inr_inj
  given: [Zero R] {x y : A}
  proof: inr_injective.eq_iff

中文:
定理 inr_inj
  条件: [Zero R] {x y : A}
  证明: inr_injective.eq_iff
-/
@[simp, norm_cast] theorem inr_inj [Zero R] {x y : A} :
    (inr x : Unitization R A) = inr y ↔ x = y := inr_injective.eq_iff

/--
theorem `inl_inj` / 定理 `inl_inj`

English:
theorem inl_inj
  given: [Zero A] {x y : R}
  proof: inl_injective.eq_iff

中文:
定理 inl_inj
  条件: [Zero A] {x y : R}
  证明: inl_injective.eq_iff
-/
@[simp] theorem inl_inj [Zero A] {x y : R} :
    (inl x : Unitization R A) = inl y ↔ x = y :=
  inl_injective.eq_iff

/--
Instance `instNontrivialLeft` / 实例 `instNontrivialLeft`

English:
instance instNontrivialLeft
  signature: {𝕜 A} [Nontrivial 𝕜] [Nonempty A]
  body: equiv.nontrivial

中文:
实例 instNontrivialLeft
  签名: {𝕜 A} [Nontrivial 𝕜] [Nonempty A]
  定义体: equiv.nontrivial

Depends on / 依赖: equiv.nontrivial, nontrivial
-/
instance instNontrivialLeft {𝕜 A} [Nontrivial 𝕜] [Nonempty A] :
    Nontrivial (Unitization 𝕜 A) :=
  equiv.nontrivial

/--
Instance `instNontrivialRight` / 实例 `instNontrivialRight`

English:
instance instNontrivialRight
  signature: {𝕜 A} [Nonempty 𝕜] [Nontrivial A]
  body: equiv.nontrivial

中文:
实例 instNontrivialRight
  签名: {𝕜 A} [Nonempty 𝕜] [Nontrivial A]
  定义体: equiv.nontrivial

Depends on / 依赖: equiv.nontrivial, nontrivial
-/
instance instNontrivialRight {𝕜 A} [Nonempty 𝕜] [Nontrivial A] :
    Nontrivial (Unitization 𝕜 A) :=
  equiv.nontrivial

end Basic

/-! ### Structures inherited from `Prod`

Additive operators and scalar multiplication operate elementwise. -/


section Additive

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

/--
Instance `instCanLift` / 实例 `instCanLift`

English:
instance instCanLift
  signature: [Zero R]
  body: ⟨x.snd, Unitization.ext (hx ▸ fst_inr R x.snd) rfl⟩

中文:
实例 instCanLift
  签名: [Zero R]
  定义体: ⟨x.snd, Unitization.ext (hx ▸ fst_inr R x.snd) rfl⟩

Depends on / 依赖: Unitization, Unitization.ext, fst_inr, x.snd
-/
instance instCanLift [Zero R] : CanLift (Unitization R A) A inr (fun x => x.fst = 0) where
  prf x hx := ⟨x.snd, Unitization.ext (hx ▸ fst_inr R x.snd) rfl⟩

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: [Inhabited R] [Inhabited A]
  body: equiv.inhabited

中文:
实例 instInhabited
  签名: [Inhabited R] [Inhabited A]
  定义体: equiv.inhabited

Depends on / 依赖: equiv.inhabited, inhabited
-/
instance instInhabited [Inhabited R] [Inhabited A] : Inhabited (Unitization R A) :=
  equiv.inhabited

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: [Zero R] [Zero A]
  body: equiv.zero

中文:
实例 instZero
  签名: [Zero R] [Zero A]
  定义体: equiv.zero

Depends on / 依赖: equiv.zero
-/
instance instZero [Zero R] [Zero A] : Zero (Unitization R A) :=
  equiv.zero

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: [Add R] [Add A]
  body: equiv.add

中文:
实例 instAdd
  签名: [Add R] [Add A]
  定义体: equiv.add

Depends on / 依赖: equiv.add
-/
instance instAdd [Add R] [Add A] : Add (Unitization R A) :=
  equiv.add

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: [Sub R] [Sub A]
  body: equiv.sub

中文:
实例 instSub
  签名: [Sub R] [Sub A]
  定义体: equiv.sub

Depends on / 依赖: equiv.sub
-/
instance instSub [Sub R] [Sub A] : Sub (Unitization R A) :=
  equiv.sub

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: [Neg R] [Neg A]
  body: equiv.Neg

中文:
实例 instNeg
  签名: [Neg R] [Neg A]
  定义体: equiv.Neg

Depends on / 依赖: equiv.Neg
-/
instance instNeg [Neg R] [Neg A] : Neg (Unitization R A) :=
  equiv.Neg

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: [SMul S R] [SMul S A]
  body: equiv.smul S

中文:
实例 instSMul
  签名: [SMul S R] [SMul S A]
  定义体: equiv.smul S

Depends on / 依赖: equiv.smul
-/
instance instSMul [SMul S R] [SMul S A] : SMul S (Unitization R A) :=
  equiv.smul S

/--
Instance `instAddSemigroup` / 实例 `instAddSemigroup`

English:
instance instAddSemigroup
  signature: [AddSemigroup R] [AddSemigroup A]
  body: fast_instance% equiv.addSemigroup

中文:
实例 instAddSemigroup
  签名: [AddSemigroup R] [AddSemigroup A]
  定义体: fast_instance% equiv.addSemigroup

Depends on / 依赖: addSemigroup, equiv.addSemigroup, fast_instance
-/
instance instAddSemigroup [AddSemigroup R] [AddSemigroup A] : AddSemigroup (Unitization R A) :=
  fast_instance% equiv.addSemigroup

/--
Instance `instAddZeroClass` / 实例 `instAddZeroClass`

English:
instance instAddZeroClass
  signature: [AddZeroClass R] [AddZeroClass A]
  body: fast_instance% equiv.addZeroClass

中文:
实例 instAddZeroClass
  签名: [AddZeroClass R] [AddZeroClass A]
  定义体: fast_instance% equiv.addZeroClass

Depends on / 依赖: addZeroClass, equiv.addZeroClass, fast_instance
-/
instance instAddZeroClass [AddZeroClass R] [AddZeroClass A] : AddZeroClass (Unitization R A) :=
  fast_instance% equiv.addZeroClass

/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: [AddMonoid R] [AddMonoid A]
  body: fast_instance% equiv.addMonoid

中文:
实例 instAddMonoid
  签名: [AddMonoid R] [AddMonoid A]
  定义体: fast_instance% equiv.addMonoid

Depends on / 依赖: addMonoid, equiv.addMonoid, fast_instance
-/
instance instAddMonoid [AddMonoid R] [AddMonoid A] : AddMonoid (Unitization R A) :=
  fast_instance% equiv.addMonoid

/--
Instance `instAddGroup` / 实例 `instAddGroup`

English:
instance instAddGroup
  signature: [AddGroup R] [AddGroup A]
  body: fast_instance% equiv.addGroup

中文:
实例 instAddGroup
  签名: [AddGroup R] [AddGroup A]
  定义体: fast_instance% equiv.addGroup

Depends on / 依赖: addGroup, equiv.addGroup, fast_instance
-/
instance instAddGroup [AddGroup R] [AddGroup A] : AddGroup (Unitization R A) :=
  fast_instance% equiv.addGroup

/--
Instance `instAddCommSemigroup` / 实例 `instAddCommSemigroup`

English:
instance instAddCommSemigroup
  signature: [AddCommSemigroup R] [AddCommSemigroup A]
  body: fast_instance% equiv.addCommSemigroup

中文:
实例 instAddCommSemigroup
  签名: [AddCommSemigroup R] [AddCommSemigroup A]
  定义体: fast_instance% equiv.addCommSemigroup

Depends on / 依赖: addCommSemigroup, equiv.addCommSemigroup, fast_instance
-/
instance instAddCommSemigroup [AddCommSemigroup R] [AddCommSemigroup A] :
    AddCommSemigroup (Unitization R A) :=
  fast_instance% equiv.addCommSemigroup

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: [AddCommMonoid R] [AddCommMonoid A]
  body: fast_instance% equiv.addCommMonoid

中文:
实例 instAddCommMonoid
  签名: [AddCommMonoid R] [AddCommMonoid A]
  定义体: fast_instance% equiv.addCommMonoid

Depends on / 依赖: addCommMonoid, equiv.addCommMonoid, fast_instance
-/
instance instAddCommMonoid [AddCommMonoid R] [AddCommMonoid A] : AddCommMonoid (Unitization R A) :=
  fast_instance% equiv.addCommMonoid

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [AddCommGroup R] [AddCommGroup A]
  body: fast_instance% equiv.addCommGroup

@[simp]

中文:
实例 instAddCommGroup
  签名: [AddCommGroup R] [AddCommGroup A]
  定义体: fast_instance% equiv.addCommGroup

@[simp]

Depends on / 依赖: addCommGroup, equiv.addCommGroup, fast_instance
-/
instance instAddCommGroup [AddCommGroup R] [AddCommGroup A] : AddCommGroup (Unitization R A) :=
  fast_instance% equiv.addCommGroup

@[simp]
/--
theorem `toProd_zero` / 定理 `toProd_zero`

English:
theorem toProd_zero
  given: [Zero R] [Zero A]
  statement: (0 : Unitization R A).toProd = 0
  proof: rfl

@[simp]

中文:
定理 toProd_zero
  条件: [Zero R] [Zero A]
  结论: (0 : Unitization R A).toProd = 0
  证明: rfl

@[simp]
-/
theorem toProd_zero [Zero R] [Zero A] : (0 : Unitization R A).toProd = 0 :=
  rfl

@[simp]
/--
theorem `toProd_add` / 定理 `toProd_add`

English:
theorem toProd_add
  given: [Add R] [Add A] (x₁ x₂ : Unitization R A)
  proof: rfl

@[simp]

中文:
定理 toProd_add
  条件: [Add R] [Add A] (x₁ x₂ : Unitization R A)
  证明: rfl

@[simp]
-/
theorem toProd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) :
    (x₁ + x₂).toProd = x₁.toProd + x₂.toProd :=
  rfl

@[simp]
/--
theorem `toProd_neg` / 定理 `toProd_neg`

English:
theorem toProd_neg
  given: [Neg R] [Neg A] (x : Unitization R A)
  statement: (-x).toProd = -x.toProd
  proof: rfl

@[simp]

中文:
定理 toProd_neg
  条件: [Neg R] [Neg A] (x : Unitization R A)
  结论: (-x).toProd = -x.toProd
  证明: rfl

@[simp]
-/
theorem toProd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).toProd = -x.toProd :=
  rfl

@[simp]
/--
theorem `toProd_smul` / 定理 `toProd_smul`

English:
theorem toProd_smul
  given: [SMul S R] [SMul S A] (s : S) (x : Unitization R A)
  proof: rfl

中文:
定理 toProd_smul
  条件: [SMul S R] [SMul S A] (s : S) (x : Unitization R A)
  证明: rfl
-/
theorem toProd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) :
    (s • x).toProd = s • x.toProd :=
  rfl

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMul T S]
  body: equiv.isScalarTower T S

中文:
实例 instIsScalarTower
  签名: [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMul T S]
  定义体: equiv.isScalarTower T S

Depends on / 依赖: equiv.isScalarTower, isScalarTower
-/
instance instIsScalarTower [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMul T S]
    [IsScalarTower T S R] [IsScalarTower T S A] : IsScalarTower T S (Unitization R A) :=
  equiv.isScalarTower T S

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMulCommClass T S R]
  body: equiv.smulCommClass T S

中文:
实例 instSMulCommClass
  签名: [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMulCommClass T S R]
  定义体: equiv.smulCommClass T S

Depends on / 依赖: equiv.smulCommClass, smulCommClass
-/
instance instSMulCommClass [SMul T R] [SMul T A] [SMul S R] [SMul S A] [SMulCommClass T S R]
    [SMulCommClass T S A] : SMulCommClass T S (Unitization R A) :=
  equiv.smulCommClass T S

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [SMul S R] [SMul S A] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ A] [IsCentralScalar S R]
  body: equiv.isCentralScalar S

中文:
实例 instIsCentralScalar
  签名: [SMul S R] [SMul S A] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ A] [IsCentralScalar S R]
  定义体: equiv.isCentralScalar S

Depends on / 依赖: equiv.isCentralScalar, isCentralScalar
-/
instance instIsCentralScalar [SMul S R] [SMul S A] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ A] [IsCentralScalar S R]
    [IsCentralScalar S A] : IsCentralScalar S (Unitization R A) :=
  equiv.isCentralScalar S

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: [Monoid S] [MulAction S R] [MulAction S A]
  body: fast_instance% equiv.mulAction S

中文:
实例 instMulAction
  签名: [Monoid S] [MulAction S R] [MulAction S A]
  定义体: fast_instance% equiv.mulAction S

Depends on / 依赖: equiv.mulAction, fast_instance, mulAction
-/
instance instMulAction [Monoid S] [MulAction S R] [MulAction S A] : MulAction S (Unitization R A) :=
  fast_instance% equiv.mulAction S

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [Monoid S] [AddMonoid R] [AddMonoid A] [DistribMulAction S R]
  body: fast_instance% equiv.distribMulAction S

中文:
实例 instDistribMulAction
  签名: [Monoid S] [AddMonoid R] [AddMonoid A] [DistribMulAction S R]
  定义体: fast_instance% equiv.distribMulAction S

Depends on / 依赖: distribMulAction, equiv.distribMulAction, fast_instance
-/
instance instDistribMulAction [Monoid S] [AddMonoid R] [AddMonoid A] [DistribMulAction S R]
    [DistribMulAction S A] : DistribMulAction S (Unitization R A) :=
  fast_instance% equiv.distribMulAction S

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A]
  body: fast_instance% equiv.module S

中文:
实例 instModule
  签名: [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A]
  定义体: fast_instance% equiv.module S

Depends on / 依赖: equiv.module, fast_instance, module
-/
instance instModule [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A] :
    Module S (Unitization R A) :=
  fast_instance% equiv.module S

variable (R A) in
/-- The identity map between `Unitization R A` and `R × A` as an `AddEquiv`. -/
@[simps! apply symm_apply]
/--
Definition of `addEquiv` / `addEquiv` 的定义

English:
definition addEquiv
  signature: [Add R] [Add A]
  body: equiv
  map_add' _ _ := rfl

中文:
定义 addEquiv
  签名: [Add R] [Add A]
  定义体: equiv
  map_add' _ _ := rfl
-/
def addEquiv [Add R] [Add A] : Unitization R A ≃+ R × A where
  toEquiv := equiv
  map_add' _ _ := rfl

-- not marked `simp` because the LHS would not be in simp normal form.
/--
lemma `toEquiv_addEquiv` / 引理 `toEquiv_addEquiv`

English:
lemma toEquiv_addEquiv
  given: [Add R] [Add A]
  statement: (addEquiv R A).toEquiv = equiv
  proof: rfl

中文:
引理 toEquiv_addEquiv
  条件: [Add R] [Add A]
  结论: (addEquiv R A).toEquiv = equiv
  证明: rfl
-/
lemma toEquiv_addEquiv [Add R] [Add A] : (addEquiv R A).toEquiv = equiv :=
  rfl

variable (R S A) in
/-- The identity map between `Unitization R A` and `R × A` as a `LinearEquiv`. -/
@[simps! apply symm_apply]
/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A]
  body: addEquiv R A
  map_smul' _ _ := rfl

@[simp]

中文:
定义 linearEquiv
  签名: [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A]
  定义体: addEquiv R A
  map_smul' _ _ := rfl

@[simp]

Depends on / 依赖: addEquiv
-/
def linearEquiv [Semiring S] [AddCommMonoid R] [AddCommMonoid A] [Module S R] [Module S A] :
    Unitization R A ≃ₗ[S] R × A where
  toAddEquiv := addEquiv R A
  map_smul' _ _ := rfl

@[simp]
/--
lemma `toAddEquiv_linearEquiv` / 引理 `toAddEquiv_linearEquiv`

English:
lemma toAddEquiv_linearEquiv
  statement: [Semiring S] [AddCommMonoid R] [AddCommMonoid A]
  proof: rfl

@[simp]

中文:
引理 toAddEquiv_linearEquiv
  结论: [Semiring S] [AddCommMonoid R] [AddCommMonoid A]
  证明: rfl

@[simp]
-/
lemma toAddEquiv_linearEquiv [Semiring S] [AddCommMonoid R] [AddCommMonoid A]
    [Module S R] [Module S A] : (linearEquiv S R A).toAddEquiv = addEquiv R A :=
  rfl

@[simp]
/--
theorem `fst_zero` / 定理 `fst_zero`

English:
theorem fst_zero
  given: [Zero R] [Zero A]
  statement: (0 : Unitization R A).fst = 0
  proof: rfl

@[simp]

中文:
定理 fst_zero
  条件: [Zero R] [Zero A]
  结论: (0 : Unitization R A).fst = 0
  证明: rfl

@[simp]
-/
theorem fst_zero [Zero R] [Zero A] : (0 : Unitization R A).fst = 0 :=
  rfl

@[simp]
/--
theorem `snd_zero` / 定理 `snd_zero`

English:
theorem snd_zero
  given: [Zero R] [Zero A]
  statement: (0 : Unitization R A).snd = 0
  proof: rfl

@[simp]

中文:
定理 snd_zero
  条件: [Zero R] [Zero A]
  结论: (0 : Unitization R A).snd = 0
  证明: rfl

@[simp]
-/
theorem snd_zero [Zero R] [Zero A] : (0 : Unitization R A).snd = 0 :=
  rfl

@[simp]
/--
theorem `fst_add` / 定理 `fst_add`

English:
theorem fst_add
  given: [Add R] [Add A] (x₁ x₂ : Unitization R A)
  statement: (x₁ + x₂).fst = x₁.fst + x₂.fst
  proof: rfl

@[simp]

中文:
定理 fst_add
  条件: [Add R] [Add A] (x₁ x₂ : Unitization R A)
  结论: (x₁ + x₂).fst = x₁.fst + x₂.fst
  证明: rfl

@[simp]
-/
theorem fst_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).fst = x₁.fst + x₂.fst :=
  rfl

@[simp]
/--
theorem `snd_add` / 定理 `snd_add`

English:
theorem snd_add
  given: [Add R] [Add A] (x₁ x₂ : Unitization R A)
  statement: (x₁ + x₂).snd = x₁.snd + x₂.snd
  proof: rfl

@[simp]

中文:
定理 snd_add
  条件: [Add R] [Add A] (x₁ x₂ : Unitization R A)
  结论: (x₁ + x₂).snd = x₁.snd + x₂.snd
  证明: rfl

@[simp]
-/
theorem snd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).snd = x₁.snd + x₂.snd :=
  rfl

@[simp]
/--
theorem `fst_neg` / 定理 `fst_neg`

English:
theorem fst_neg
  given: [Neg R] [Neg A] (x : Unitization R A)
  statement: (-x).fst = -x.fst
  proof: rfl

@[simp]

中文:
定理 fst_neg
  条件: [Neg R] [Neg A] (x : Unitization R A)
  结论: (-x).fst = -x.fst
  证明: rfl

@[simp]
-/
theorem fst_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).fst = -x.fst :=
  rfl

@[simp]
/--
theorem `snd_neg` / 定理 `snd_neg`

English:
theorem snd_neg
  given: [Neg R] [Neg A] (x : Unitization R A)
  statement: (-x).snd = -x.snd
  proof: rfl

@[simp]

中文:
定理 snd_neg
  条件: [Neg R] [Neg A] (x : Unitization R A)
  结论: (-x).snd = -x.snd
  证明: rfl

@[simp]
-/
theorem snd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).snd = -x.snd :=
  rfl

@[simp]
/--
theorem `fst_smul` / 定理 `fst_smul`

English:
theorem fst_smul
  given: [SMul S R] [SMul S A] (s : S) (x : Unitization R A)
  statement: (s • x).fst = s • x.fst
  proof: rfl

@[simp]

中文:
定理 fst_smul
  条件: [SMul S R] [SMul S A] (s : S) (x : Unitization R A)
  结论: (s • x).fst = s • x.fst
  证明: rfl

@[simp]
-/
theorem fst_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).fst = s • x.fst :=
  rfl

@[simp]
/--
theorem `snd_smul` / 定理 `snd_smul`

English:
theorem snd_smul
  given: [SMul S R] [SMul S A] (s : S) (x : Unitization R A)
  statement: (s • x).snd = s • x.snd
  proof: rfl

中文:
定理 snd_smul
  条件: [SMul S R] [SMul S A] (s : S) (x : Unitization R A)
  结论: (s • x).snd = s • x.snd
  证明: rfl
-/
theorem snd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).snd = s • x.snd :=
  rfl

section

variable (A)

@[simp]
/--
theorem `inl_zero` / 定理 `inl_zero`

English:
theorem inl_zero
  given: [Zero R] [Zero A]
  statement: (inl 0 : Unitization R A) = 0
  proof: rfl

@[simp]

中文:
定理 inl_zero
  条件: [Zero R] [Zero A]
  结论: (inl 0 : Unitization R A) = 0
  证明: rfl

@[simp]
-/
theorem inl_zero [Zero R] [Zero A] : (inl 0 : Unitization R A) = 0 :=
  rfl

@[simp]
/--
theorem `inl_add` / 定理 `inl_add`

English:
theorem inl_add
  given: [Add R] [AddZeroClass A] (r₁ r₂ : R)
  proof: Unitization.ext rfl (add_zero 0).symm

@[simp]

中文:
定理 inl_add
  条件: [Add R] [AddZeroClass A] (r₁ r₂ : R)
  证明: Unitization.ext rfl (add_zero 0).symm

@[simp]

Depends on / 依赖: Unitization, Unitization.ext, add_zero
-/
theorem inl_add [Add R] [AddZeroClass A] (r₁ r₂ : R) :
    (inl (r₁ + r₂) : Unitization R A) = inl r₁ + inl r₂ :=
  Unitization.ext rfl (add_zero 0).symm

@[simp]
/--
theorem `inl_neg` / 定理 `inl_neg`

English:
theorem inl_neg
  given: [Neg R] [AddGroup A] (r : R)
  statement: (inl (-r) : Unitization R A) = -inl r
  proof: Unitization.ext rfl neg_zero.symm

@[simp]

中文:
定理 inl_neg
  条件: [Neg R] [AddGroup A] (r : R)
  结论: (inl (-r) : Unitization R A) = -inl r
  证明: Unitization.ext rfl neg_zero.symm

@[simp]

Depends on / 依赖: Unitization, Unitization.ext, neg_zero, neg_zero.symm
-/
theorem inl_neg [Neg R] [AddGroup A] (r : R) : (inl (-r) : Unitization R A) = -inl r :=
  Unitization.ext rfl neg_zero.symm

@[simp]
/--
theorem `inl_sub` / 定理 `inl_sub`

English:
theorem inl_sub
  given: [AddGroup R] [AddGroup A] (r₁ r₂ : R)
  proof: Unitization.ext rfl (sub_zero 0).symm

@[simp]

中文:
定理 inl_sub
  条件: [AddGroup R] [AddGroup A] (r₁ r₂ : R)
  证明: Unitization.ext rfl (sub_zero 0).symm

@[simp]

Depends on / 依赖: Unitization, Unitization.ext, sub_zero
-/
theorem inl_sub [AddGroup R] [AddGroup A] (r₁ r₂ : R) :
    (inl (r₁ - r₂) : Unitization R A) = inl r₁ - inl r₂ :=
  Unitization.ext rfl (sub_zero 0).symm

@[simp]
/--
theorem `inl_smul` / 定理 `inl_smul`

English:
theorem inl_smul
  given: [Zero A] [SMul S R] [SMulZeroClass S A] (s : S) (r : R)
  proof: Unitization.ext rfl (smul_zero s).symm

中文:
定理 inl_smul
  条件: [Zero A] [SMul S R] [SMulZeroClass S A] (s : S) (r : R)
  证明: Unitization.ext rfl (smul_zero s).symm

Depends on / 依赖: Unitization, Unitization.ext, smul_zero
-/
theorem inl_smul [Zero A] [SMul S R] [SMulZeroClass S A] (s : S) (r : R) :
    (inl (s • r) : Unitization R A) = s • inl r :=
  Unitization.ext rfl (smul_zero s).symm

end

section

variable (R)

@[simp, norm_cast]
/--
theorem `inr_zero` / 定理 `inr_zero`

English:
theorem inr_zero
  given: [Zero R] [Zero A]
  statement: ↑(0 : A) = (0 : Unitization R A)
  proof: rfl

@[simp, norm_cast]

中文:
定理 inr_zero
  条件: [Zero R] [Zero A]
  结论: ↑(0 : A) = (0 : Unitization R A)
  证明: rfl

@[simp, norm_cast]
-/
theorem inr_zero [Zero R] [Zero A] : ↑(0 : A) = (0 : Unitization R A) :=
  rfl

@[simp, norm_cast]
/--
theorem `inr_add` / 定理 `inr_add`

English:
theorem inr_add
  given: [AddZeroClass R] [Add A] (m₁ m₂ : A)
  statement: (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂
  proof: Unitization.ext (add_zero 0).symm rfl

@[simp, norm_cast]

中文:
定理 inr_add
  条件: [AddZeroClass R] [Add A] (m₁ m₂ : A)
  结论: (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂
  证明: Unitization.ext (add_zero 0).symm rfl

@[simp, norm_cast]

Depends on / 依赖: Unitization, Unitization.ext, add_zero
-/
theorem inr_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂ :=
  Unitization.ext (add_zero 0).symm rfl

@[simp, norm_cast]
/--
theorem `inr_neg` / 定理 `inr_neg`

English:
theorem inr_neg
  given: [AddGroup R] [Neg A] (m : A)
  statement: (↑(-m) : Unitization R A) = -m
  proof: Unitization.ext neg_zero.symm rfl

@[simp, norm_cast]

中文:
定理 inr_neg
  条件: [AddGroup R] [Neg A] (m : A)
  结论: (↑(-m) : Unitization R A) = -m
  证明: Unitization.ext neg_zero.symm rfl

@[simp, norm_cast]

Depends on / 依赖: Unitization, Unitization.ext, neg_zero, neg_zero.symm
-/
theorem inr_neg [AddGroup R] [Neg A] (m : A) : (↑(-m) : Unitization R A) = -m :=
  Unitization.ext neg_zero.symm rfl

@[simp, norm_cast]
/--
theorem `inr_sub` / 定理 `inr_sub`

English:
theorem inr_sub
  given: [AddGroup R] [AddGroup A] (m₁ m₂ : A)
  statement: (↑(m₁ - m₂) : Unitization R A) = m₁ - m₂
  proof: Unitization.ext (sub_zero 0).symm rfl

@[simp, norm_cast]

中文:
定理 inr_sub
  条件: [AddGroup R] [AddGroup A] (m₁ m₂ : A)
  结论: (↑(m₁ - m₂) : Unitization R A) = m₁ - m₂
  证明: Unitization.ext (sub_zero 0).symm rfl

@[simp, norm_cast]

Depends on / 依赖: Unitization, Unitization.ext, sub_zero
-/
theorem inr_sub [AddGroup R] [AddGroup A] (m₁ m₂ : A) : (↑(m₁ - m₂) : Unitization R A) = m₁ - m₂ :=
  Unitization.ext (sub_zero 0).symm rfl

@[simp, norm_cast]
/--
theorem `inr_smul` / 定理 `inr_smul`

English:
theorem inr_smul
  given: [Zero R] [SMulZeroClass S R] [SMul S A] (r : S) (m : A)
  proof: Unitization.ext (smul_zero _).symm rfl

中文:
定理 inr_smul
  条件: [Zero R] [SMulZeroClass S R] [SMul S A] (r : S) (m : A)
  证明: Unitization.ext (smul_zero _).symm rfl

Depends on / 依赖: Unitization, Unitization.ext, smul_zero
-/
theorem inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (r : S) (m : A) :
    (↑(r • m) : Unitization R A) = r • (m : Unitization R A) :=
  Unitization.ext (smul_zero _).symm rfl

end

/--
theorem `inl_fst_add_inr_snd_eq` / 定理 `inl_fst_add_inr_snd_eq`

English:
theorem inl_fst_add_inr_snd_eq
  given: [AddZeroClass R] [AddZeroClass A] (x : Unitization R A)
  proof: Unitization.ext (add_zero x.fst) (zero_add x.snd)

中文:
定理 inl_fst_add_inr_snd_eq
  条件: [AddZeroClass R] [AddZeroClass A] (x : Unitization R A)
  证明: Unitization.ext (add_zero x.fst) (zero_add x.snd)

Depends on / 依赖: Unitization, Unitization.ext, add_zero, x.fst, x.snd, zero_add
-/
theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass A] (x : Unitization R A) :
    inl x.fst + (x.snd : Unitization R A) = x :=
  Unitization.ext (add_zero x.fst) (zero_add x.snd)

/-- To show a property hold on all `Unitization R A` it suffices to show it holds
on terms of the form `inl r + a`.

This can be used as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  statement: {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A -> Prop}
  proof: inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.fst x.snd

@[ext]

中文:
定理 ind
  结论: {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A -> 命题}
  证明: inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.fst x.snd

@[ext]

Depends on / 依赖: inl_add_inr, inl_fst_add_inr_snd_eq, x.fst, x.snd
-/
theorem ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitization R A -> Prop}
    (inl_add_inr : forall (r : R) (a : A), P (inl r + (a : Unitization R A))) (x) : P x :=
  inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.fst x.snd

@[ext]
/--
theorem `linearMap_ext` / 定理 `linearMap_ext`

English:
theorem linearMap_ext
  statement: {N} [CommSemiring S] [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid N]
  proof: .injective (linearEquiv S R A).arrowCongr (.refl ..)
    LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

中文:
定理 linearMap_ext
  结论: {N} [CommSemiring S] [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid N]
  证明: .injective (linearEquiv S R A).arrowCongr (.refl ..)
    LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

Depends on / 依赖: LinearMap, LinearMap.ext, LinearMap.prod_ext, arrowCongr, injective, linearEquiv, prod_ext
-/
theorem linearMap_ext {N} [CommSemiring S] [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid N]
    [Module S R] [Module S A] [Module S N] ⦃f g : Unitization R A ->ₗ[S] N⦄
    (hl : forall r, f (inl r) = g (inl r)) (hr : forall a : A, f a = g a) : f = g :=
.injective (linearEquiv S R A).arrowCongr (.refl ..)
    LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

variable [Semiring S] [Semiring R] [AddCommMonoid A] [SMul R A] [Module S R] [Module S A]

variable (S R A) in
/-- The canonical `S`-linear inclusion `A → Unitization R A`. -/
@[simps apply]
/--
Definition of `inrHom` / `inrHom` 的定义

English:
definition inrHom
  signature: : A ->ₗ[S] Unitization R A where
  body: (↑)
  map_add' := inr_add R
  map_smul' := inr_smul R

omit [SMul R A] in

中文:
定义 inrHom
  签名: : A ->ₗ[S] Unitization R A where
  定义体: (↑)
  map_add' := inr_add R
  map_smul' := inr_smul R

omit [SMul R A] in
-/
def inrHom : A ->ₗ[S] Unitization R A where
  toFun := (↑)
  map_add' := inr_add R
  map_smul' := inr_smul R

omit [SMul R A] in
/--
lemma `inrHom_injective` / 引理 `inrHom_injective`

English:
lemma inrHom_injective
  statement: Function.Injective (inrHom S R A)
  proof: Unitization.inr_injective

中文:
引理 inrHom_injective
  结论: Function.Injective (inrHom S R A)
  证明: Unitization.inr_injective

Depends on / 依赖: Unitization, Unitization.inr_injective, inr_injective
-/
lemma inrHom_injective : Function.Injective (inrHom S R A) := Unitization.inr_injective

variable (S R A) in
/-- The canonical `S`-linear projection `Unitization R A → A`. -/
@[simps apply]
/--
Definition of `sndHom` / `sndHom` 的定义

English:
definition sndHom
  signature: : Unitization R A ->ₗ[S] A where
  body: a.snd
  map_add' := snd_add
  map_smul' := snd_smul

中文:
定义 sndHom
  签名: : Unitization R A ->ₗ[S] A where
  定义体: a.snd
  map_add' := snd_add
  map_smul' := snd_smul

Depends on / 依赖: a.snd
-/
def sndHom : Unitization R A ->ₗ[S] A where
  toFun a := a.snd
  map_add' := snd_add
  map_smul' := snd_smul

end Additive

/-! ### Multiplicative structure -/


section Mul

variable {R A : Type*}

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: [One R] [Zero A]
  body: ⟨.mk (1, 0)⟩

中文:
实例 instOne
  签名: [One R] [Zero A]
  定义体: ⟨.mk (1, 0)⟩
-/
instance instOne [One R] [Zero A] : One (Unitization R A) :=
  ⟨.mk (1, 0)⟩

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: [Mul R] [Add A] [Mul A] [SMul R A]
  body: ⟨fun x y => .mk (x.fst * y.fst, x.fst • y.snd + y.fst • x.snd + x.snd * y.snd)⟩

@[simp]

中文:
实例 instMul
  签名: [Mul R] [Add A] [Mul A] [SMul R A]
  定义体: ⟨fun x y => .mk (x.fst * y.fst, x.fst • y.snd + y.fst • x.snd + x.snd * y.snd)⟩

@[simp]

Depends on / 依赖: x.fst, x.snd, y.fst, y.snd
-/
instance instMul [Mul R] [Add A] [Mul A] [SMul R A] : Mul (Unitization R A) :=
  ⟨fun x y => .mk (x.fst * y.fst, x.fst • y.snd + y.fst • x.snd + x.snd * y.snd)⟩

@[simp]
/--
theorem `fst_one` / 定理 `fst_one`

English:
theorem fst_one
  given: [One R] [Zero A]
  statement: (1 : Unitization R A).fst = 1
  proof: rfl

@[simp]

中文:
定理 fst_one
  条件: [One R] [Zero A]
  结论: (1 : Unitization R A).fst = 1
  证明: rfl

@[simp]
-/
theorem fst_one [One R] [Zero A] : (1 : Unitization R A).fst = 1 :=
  rfl

@[simp]
/--
theorem `snd_one` / 定理 `snd_one`

English:
theorem snd_one
  given: [One R] [Zero A]
  statement: (1 : Unitization R A).snd = 0
  proof: rfl

@[simp]

中文:
定理 snd_one
  条件: [One R] [Zero A]
  结论: (1 : Unitization R A).snd = 0
  证明: rfl

@[simp]
-/
theorem snd_one [One R] [Zero A] : (1 : Unitization R A).snd = 0 :=
  rfl

@[simp]
/--
theorem `fst_mul` / 定理 `fst_mul`

English:
theorem fst_mul
  given: [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A)
  proof: rfl

@[simp]

中文:
定理 fst_mul
  条件: [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A)
  证明: rfl

@[simp]
-/
theorem fst_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst :=
  rfl

@[simp]
/--
theorem `snd_mul` / 定理 `snd_mul`

English:
theorem snd_mul
  given: [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A)
  proof: rfl

中文:
定理 snd_mul
  条件: [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A)
  证明: rfl
-/
theorem snd_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd + x₁.snd * x₂.snd :=
  rfl

section

variable (A)

@[simp]
/--
theorem `inl_one` / 定理 `inl_one`

English:
theorem inl_one
  given: [One R] [Zero A]
  statement: (inl 1 : Unitization R A) = 1
  proof: rfl

@[simp]

中文:
定理 inl_one
  条件: [One R] [Zero A]
  结论: (inl 1 : Unitization R A) = 1
  证明: rfl

@[simp]
-/
theorem inl_one [One R] [Zero A] : (inl 1 : Unitization R A) = 1 :=
  rfl

@[simp]
/--
theorem `inl_mul` / 定理 `inl_mul`

English:
theorem inl_mul
  given: [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ : R)
  proof: Unitization.ext rfl by simp

中文:
定理 inl_mul
  条件: [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ : R)
  证明: Unitization.ext rfl by simp

Depends on / 依赖: Unitization, Unitization.ext
-/
theorem inl_mul [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ : R) :
    (inl (r₁ * r₂) : Unitization R A) = inl r₁ * inl r₂ :=
Unitization.ext rfl by simp

/--
theorem `inl_mul_inl` / 定理 `inl_mul_inl`

English:
theorem inl_mul_inl
  given: [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ : R)
  proof: (inl_mul A r₁ r₂).symm

中文:
定理 inl_mul_inl
  条件: [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ : R)
  证明: (inl_mul A r₁ r₂).symm

Depends on / 依赖: inl_mul
-/
theorem inl_mul_inl [Mul R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r₁ r₂ : R) :
    (inl r₁ * inl r₂ : Unitization R A) = inl (r₁ * r₂) :=
  (inl_mul A r₁ r₂).symm

end

section

variable (R)

@[simp, norm_cast]
/--
theorem `inr_mul` / 定理 `inr_mul`

English:
theorem inr_mul
  given: [MulZeroClass R] [AddZeroClass A] [Mul A] [SMulWithZero R A] (a₁ a₂ : A)
  proof: Unitization.ext (mul_zero _).symm by simp

中文:
定理 inr_mul
  条件: [MulZeroClass R] [AddZeroClass A] [Mul A] [SMulWithZero R A] (a₁ a₂ : A)
  证明: Unitization.ext (mul_zero _).symm by simp

Depends on / 依赖: Unitization, Unitization.ext, mul_zero
-/
theorem inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [SMulWithZero R A] (a₁ a₂ : A) :
    (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂ :=
Unitization.ext (mul_zero _).symm by simp

end

@[norm_cast]
/--
theorem `inl_mul_inr` / 定理 `inl_mul_inr`

English:
theorem inl_mul_inr
  statement: [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
  proof: Unitization.ext (mul_zero r) by simp

@[norm_cast]

中文:
定理 inl_mul_inr
  结论: [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
  证明: Unitization.ext (mul_zero r) by simp

@[norm_cast]

Depends on / 依赖: Unitization, Unitization.ext, mul_zero
-/
theorem inl_mul_inr [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
    (a : A) : ((inl r : Unitization R A) * a) = ↑(r • a) :=
Unitization.ext (mul_zero r) by simp

@[norm_cast]
/--
theorem `inr_mul_inl` / 定理 `inr_mul_inl`

English:
theorem inr_mul_inl
  statement: [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
  proof: Unitization.ext (zero_mul r) by simp

中文:
定理 inr_mul_inl
  结论: [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
  证明: Unitization.ext (zero_mul r) by simp

Depends on / 依赖: Unitization, Unitization.ext, zero_mul
-/
theorem inr_mul_inl [MulZeroClass R] [NonUnitalNonAssocSemiring A] [SMulZeroClass R A] (r : R)
    (a : A) : a * (inl r : Unitization R A) = ↑(r • a) :=
Unitization.ext (zero_mul r) by simp

/--
Instance `instMulOneClass` / 实例 `instMulOneClass`

English:
instance instMulOneClass
  signature: [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
  body: fast_instance%
  { Unitization.instOne, Unitization.instMul with
one_mul x := Unitization.ext (one_mul x.fst) by simp
mul_one x := Unitization.ext (mul_one x.fst) by simp }

中文:
实例 instMulOneClass
  签名: [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
  定义体: fast_instance%
  { Unitization.instOne, Unitization.instMul with
one_mul x := Unitization.ext (one_mul x.fst) by simp
mul_one x := Unitization.ext (mul_one x.fst) by simp }

Depends on / 依赖: Unitization, Unitization.ext, Unitization.instMul, Unitization.instOne, fast_instance, instMul, instOne, mul_one, one_mul, x.fst
-/
instance instMulOneClass [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] :
    MulOneClass (Unitization R A) :=
  fast_instance%
  { Unitization.instOne, Unitization.instMul with
one_mul x := Unitization.ext (one_mul x.fst) by simp
mul_one x := Unitization.ext (mul_one x.fst) by simp }

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  body: fast_instance%
  { Unitization.instMulOneClass,
    Unitization.instAddCommMonoid with
zero_mul _ := Unitization.ext (zero_mul _) by simp
mul_zero _ := Unitization.ext (mul_zero _) by simp
left_distrib _ _ _ := Unitization.ext (mul_add ..) by
      simp [smul_add, add_smul, mul_add]
      abel
right

中文:
实例 instNonAssocSemiring
  签名: [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  定义体: fast_instance%
  { Unitization.instMulOneClass,
    Unitization.instAddCommMonoid with
zero_mul _ := Unitization.ext (zero_mul _) by simp
mul_zero _ := Unitization.ext (mul_zero _) by simp
left_distrib _ _ _ := Unitization.ext (mul_add ..) by
      simp [smul_add, add_smul, mul_add]
      abel
right

Depends on / 依赖: Unitization, Unitization.ext, Unitization.instAddCommMonoid, Unitization.instMulOneClass, add_mul, add_smul, fast_instance, instAddCommMonoid, instMulOneClass, left_distrib, mul_add, mul_zero, right_distrib, smul_add, zero_mul
-/
instance instNonAssocSemiring [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
    NonAssocSemiring (Unitization R A) :=
  fast_instance%
  { Unitization.instMulOneClass,
    Unitization.instAddCommMonoid with
zero_mul _ := Unitization.ext (zero_mul _) by simp
mul_zero _ := Unitization.ext (mul_zero _) by simp
left_distrib _ _ _ := Unitization.ext (mul_add ..) by
      simp [smul_add, add_smul, mul_add]
      abel
right_distrib _ _ _ := Unitization.ext (add_mul ..) by
      simp [smul_add, add_smul, add_mul]
      abel }

/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: [CommMonoid R] [NonUnitalSemiring A] [DistribMulAction R A]
  body: fast_instance%
  { Unitization.instMulOneClass with
mul_assoc x y z := Unitization.ext (mul_assoc ..) by
      simp only [snd_mul, fst_mul, smul_add, smul_smul, add_mul, smul_mul_assoc, mul_assoc, mul_add,
        mul_smul_comm, mul_comm z.fst x.fst, mul_comm z.fst y.fst]
      abel }

中文:
实例 instMonoid
  签名: [CommMonoid R] [NonUnitalSemiring A] [DistribMulAction R A]
  定义体: fast_instance%
  { Unitization.instMulOneClass with
mul_assoc x y z := Unitization.ext (mul_assoc ..) by
      simp only [snd_mul, fst_mul, smul_add, smul_smul, add_mul, smul_mul_assoc, mul_assoc, mul_add,
        mul_smul_comm, mul_comm z.fst x.fst, mul_comm z.fst y.fst]
      abel }

Depends on / 依赖: Unitization, Unitization.ext, Unitization.instMulOneClass, add_mul, fast_instance, fst_mul, instMulOneClass, mul_add, mul_assoc, mul_comm, mul_smul_comm, smul_add, smul_mul_assoc, smul_smul, snd_mul, x.fst, y.fst, z.fst
-/
instance instMonoid [CommMonoid R] [NonUnitalSemiring A] [DistribMulAction R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Monoid (Unitization R A) :=
  fast_instance%
  { Unitization.instMulOneClass with
mul_assoc x y z := Unitization.ext (mul_assoc ..) by
      simp only [snd_mul, fst_mul, smul_add, smul_smul, add_mul, smul_mul_assoc, mul_assoc, mul_add,
        mul_smul_comm, mul_comm z.fst x.fst, mul_comm z.fst y.fst]
      abel }

/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: [CommMonoid R] [NonUnitalCommSemiring A] [DistribMulAction R A]
  body: fast_instance%
  { Unitization.instMonoid with
mul_comm _ _ := Unitization.ext (mul_comm ..) by simp [add_comm, mul_comm] }

中文:
实例 instCommMonoid
  签名: [CommMonoid R] [NonUnitalCommSemiring A] [DistribMulAction R A]
  定义体: fast_instance%
  { Unitization.instMonoid with
mul_comm _ _ := Unitization.ext (mul_comm ..) by simp [add_comm, mul_comm] }

Depends on / 依赖: Unitization, Unitization.ext, Unitization.instMonoid, add_comm, fast_instance, instMonoid, mul_comm
-/
instance instCommMonoid [CommMonoid R] [NonUnitalCommSemiring A] [DistribMulAction R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : CommMonoid (Unitization R A) :=
  fast_instance%
  { Unitization.instMonoid with
mul_comm _ _ := Unitization.ext (mul_comm ..) by simp [add_comm, mul_comm] }

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  body: fast_instance%
  { Unitization.instMonoid, Unitization.instNonAssocSemiring with }

中文:
实例 instSemiring
  签名: [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  定义体: fast_instance%
  { Unitization.instMonoid, Unitization.instNonAssocSemiring with }

Depends on / 依赖: Unitization, Unitization.instMonoid, Unitization.instNonAssocSemiring, fast_instance, instMonoid, instNonAssocSemiring
-/
instance instSemiring [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Semiring (Unitization R A) :=
  fast_instance%
  { Unitization.instMonoid, Unitization.instNonAssocSemiring with }

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
  body: fast_instance%
  { Unitization.instCommMonoid, Unitization.instNonAssocSemiring with }

中文:
实例 instCommSemiring
  签名: [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
  定义体: fast_instance%
  { Unitization.instCommMonoid, Unitization.instNonAssocSemiring with }

Depends on / 依赖: Unitization, Unitization.instCommMonoid, Unitization.instNonAssocSemiring, fast_instance, instCommMonoid, instNonAssocSemiring
-/
instance instCommSemiring [CommSemiring R] [NonUnitalCommSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : CommSemiring (Unitization R A) :=
  fast_instance%
  { Unitization.instCommMonoid, Unitization.instNonAssocSemiring with }

/--
Instance `instNonAssocRing` / 实例 `instNonAssocRing`

English:
instance instNonAssocRing
  signature: [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  body: fast_instance%
  { Unitization.instAddCommGroup, Unitization.instNonAssocSemiring with }

中文:
实例 instNonAssocRing
  签名: [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  定义体: fast_instance%
  { Unitization.instAddCommGroup, Unitization.instNonAssocSemiring with }

Depends on / 依赖: Unitization, Unitization.instAddCommGroup, Unitization.instNonAssocSemiring, fast_instance, instAddCommGroup, instNonAssocSemiring
-/
instance instNonAssocRing [CommRing R] [NonUnitalNonAssocRing A] [Module R A] :
    NonAssocRing (Unitization R A) :=
  fast_instance%
  { Unitization.instAddCommGroup, Unitization.instNonAssocSemiring with }

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
  body: fast_instance%
  { Unitization.instAddCommGroup, Unitization.instSemiring with }

中文:
实例 instRing
  签名: [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
  定义体: fast_instance%
  { Unitization.instAddCommGroup, Unitization.instSemiring with }

Depends on / 依赖: Unitization, Unitization.instAddCommGroup, Unitization.instSemiring, fast_instance, instAddCommGroup, instSemiring
-/
instance instRing [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : Ring (Unitization R A) :=
  fast_instance%
  { Unitization.instAddCommGroup, Unitization.instSemiring with }

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: [CommRing R] [NonUnitalCommRing A] [Module R A] [IsScalarTower R A A]
  body: fast_instance%
  { Unitization.instAddCommGroup, Unitization.instCommSemiring with }

中文:
实例 instCommRing
  签名: [CommRing R] [NonUnitalCommRing A] [Module R A] [IsScalarTower R A A]
  定义体: fast_instance%
  { Unitization.instAddCommGroup, Unitization.instCommSemiring with }

Depends on / 依赖: Unitization, Unitization.instAddCommGroup, Unitization.instCommSemiring, fast_instance, instAddCommGroup, instCommSemiring
-/
instance instCommRing [CommRing R] [NonUnitalCommRing A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : CommRing (Unitization R A) :=
  fast_instance%
  { Unitization.instAddCommGroup, Unitization.instCommSemiring with }

variable (R A)

/-- The canonical inclusion of rings `R →+* Unitization R A`. -/
@[simps apply]
/--
Definition of `inlRingHom` / `inlRingHom` 的定义

English:
definition inlRingHom
  signature: [Semiring R] [NonUnitalSemiring A] [Module R A]
  body: inl
  map_one' := inl_one A
  map_mul' := inl_mul A
  map_zero' := inl_zero A
  map_add' := inl_add A

中文:
定义 inlRingHom
  签名: [Semiring R] [NonUnitalSemiring A] [Module R A]
  定义体: inl
  map_one' := inl_one A
  map_mul' := inl_mul A
  map_zero' := inl_zero A
  map_add' := inl_add A
-/
def inlRingHom [Semiring R] [NonUnitalSemiring A] [Module R A] : R ->+* Unitization R A where
  toFun := inl
  map_one' := inl_one A
  map_mul' := inl_mul A
  map_zero' := inl_zero A
  map_add' := inl_add A

end Mul

/-! ### Star structure -/


section Star

variable {R A : Type*}

/--
Instance `instStar` / 实例 `instStar`

English:
instance instStar
  signature: [Star R] [Star A]
  body: ⟨fun ra => .mk (star ra.fst, star ra.snd)⟩

@[simp]

中文:
实例 instStar
  签名: [Star R] [Star A]
  定义体: ⟨fun ra => .mk (star ra.fst, star ra.snd)⟩

@[simp]

Depends on / 依赖: ra.fst, ra.snd
-/
instance instStar [Star R] [Star A] : Star (Unitization R A) :=
  ⟨fun ra => .mk (star ra.fst, star ra.snd)⟩

@[simp]
/--
theorem `fst_star` / 定理 `fst_star`

English:
theorem fst_star
  given: [Star R] [Star A] (x : Unitization R A)
  statement: (star x).fst = star x.fst
  proof: rfl

@[simp]

中文:
定理 fst_star
  条件: [Star R] [Star A] (x : Unitization R A)
  结论: (star x).fst = star x.fst
  证明: rfl

@[simp]
-/
theorem fst_star [Star R] [Star A] (x : Unitization R A) : (star x).fst = star x.fst :=
  rfl

@[simp]
/--
theorem `snd_star` / 定理 `snd_star`

English:
theorem snd_star
  given: [Star R] [Star A] (x : Unitization R A)
  statement: (star x).snd = star x.snd
  proof: rfl

@[simp]

中文:
定理 snd_star
  条件: [Star R] [Star A] (x : Unitization R A)
  结论: (star x).snd = star x.snd
  证明: rfl

@[simp]
-/
theorem snd_star [Star R] [Star A] (x : Unitization R A) : (star x).snd = star x.snd :=
  rfl

@[simp]
/--
theorem `inl_star` / 定理 `inl_star`

English:
theorem inl_star
  given: [Star R] [AddMonoid A] [StarAddMonoid A] (r : R)
  proof: Unitization.ext rfl (by simp only [snd_star, star_zero, snd_inl])

@[simp, norm_cast]

中文:
定理 inl_star
  条件: [Star R] [AddMonoid A] [StarAddMonoid A] (r : R)
  证明: Unitization.ext rfl (by simp only [snd_star, star_zero, snd_inl])

@[simp, norm_cast]

Depends on / 依赖: Unitization, Unitization.ext, snd_inl, snd_star, star_zero
-/
theorem inl_star [Star R] [AddMonoid A] [StarAddMonoid A] (r : R) :
    inl (star r) = star (inl r : Unitization R A) :=
  Unitization.ext rfl (by simp only [snd_star, star_zero, snd_inl])

@[simp, norm_cast]
/--
theorem `inr_star` / 定理 `inr_star`

English:
theorem inr_star
  given: [AddMonoid R] [StarAddMonoid R] [Star A] (a : A)
  proof: Unitization.ext (by simp only [fst_star, star_zero, fst_inr]) rfl

中文:
定理 inr_star
  条件: [AddMonoid R] [StarAddMonoid R] [Star A] (a : A)
  证明: Unitization.ext (by simp only [fst_star, star_zero, fst_inr]) rfl

Depends on / 依赖: Unitization, Unitization.ext, fst_inr, fst_star, star_zero
-/
theorem inr_star [AddMonoid R] [StarAddMonoid R] [Star A] (a : A) :
    ↑(star a) = star (a : Unitization R A) :=
  Unitization.ext (by simp only [fst_star, star_zero, fst_inr]) rfl

/--
Instance `instStarAddMonoid` / 实例 `instStarAddMonoid`

English:
instance instStarAddMonoid
  signature: [AddMonoid R] [AddMonoid A] [StarAddMonoid R] [StarAddMonoid A]
  body: Unitization.ext (star_star x.fst) (star_star x.snd)
  star_add x y := Unitization.ext (star_add x.fst y.fst) (star_add x.snd y.snd)

中文:
实例 instStarAddMonoid
  签名: [AddMonoid R] [AddMonoid A] [StarAddMonoid R] [StarAddMonoid A]
  定义体: Unitization.ext (star_star x.fst) (star_star x.snd)
  star_add x y := Unitization.ext (star_add x.fst y.fst) (star_add x.snd y.snd)

Depends on / 依赖: Unitization, Unitization.ext, star_star, x.fst, x.snd
-/
instance instStarAddMonoid [AddMonoid R] [AddMonoid A] [StarAddMonoid R] [StarAddMonoid A] :
    StarAddMonoid (Unitization R A) where
  star_involutive x := Unitization.ext (star_star x.fst) (star_star x.snd)
  star_add x y := Unitization.ext (star_add x.fst y.fst) (star_add x.snd y.snd)

/--
Instance `instStarModule` / 实例 `instStarModule`

English:
instance instStarModule
  signature: [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A]
  body: Unitization.ext (by simp) (by simp)

中文:
实例 instStarModule
  签名: [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A]
  定义体: Unitization.ext (by simp) (by simp)

Depends on / 依赖: Unitization, Unitization.ext
-/
instance instStarModule [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A]
    [Module R A] [StarModule R A] : StarModule R (Unitization R A) where
  star_smul _ _ := Unitization.ext (by simp) (by simp)

/--
Instance `instStarRing` / 实例 `instStarRing`

English:
instance instStarRing
  signature: [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A] [StarRing A]
  body: fast_instance%
  { Unitization.instStarAddMonoid with
    star_mul x y := Unitization.ext
      (by simp [-star_mul']) (by simp [-star_mul', add_comm (star x.fst • star y.snd)]) }

中文:
实例 instStarRing
  签名: [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A] [StarRing A]
  定义体: fast_instance%
  { Unitization.instStarAddMonoid with
    star_mul x y := Unitization.ext
      (by simp [-star_mul']) (by simp [-star_mul', add_comm (star x.fst • star y.snd)]) }

Depends on / 依赖: Unitization, Unitization.ext, Unitization.instStarAddMonoid, add_comm, fast_instance, instStarAddMonoid, star_mul, x.fst, y.snd
-/
instance instStarRing [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A] [StarRing A]
    [Module R A] [StarModule R A] :
    StarRing (Unitization R A) :=
  fast_instance%
  { Unitization.instStarAddMonoid with
    star_mul x y := Unitization.ext
      (by simp [-star_mul']) (by simp [-star_mul', add_comm (star x.fst • star y.snd)]) }

end Star

/-! ### Algebra structure -/


section Algebra

variable (S R A : Type*) [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [Algebra S R] [DistribMulAction S A]
  [IsScalarTower S R A]

/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: : Algebra S (Unitization R A) where
  body: (Unitization.inlRingHom R A).comp (algebraMap S R)
  commutes' := fun s x => by
    induction x with
    | inl_add_inr =>
      change inl (algebraMap S R s) * _ = _ * inl (algebraMap S R s)
      rw [mul_add]; rw [add_mul]; rw [inl_mul_inl]; rw [inl_mul_inl]; rw [inl_mul_inr]; rw [inr_mul_inl]; rw 

中文:
实例 instAlgebra
  签名: : Algebra S (Unitization R A) where
  定义体: (Unitization.inlRingHom R A).comp (algebraMap S R)
  commutes' := fun s x => by
    induction x with
    | inl_add_inr =>
      change inl (algebraMap S R s) * _ = _ * inl (algebraMap S R s)
      rw [mul_add]; rw [add_mul]; rw [inl_mul_inl]; rw [inl_mul_inl]; rw [inl_mul_inr]; rw [inr_mul_inl]; rw 

Depends on / 依赖: Unitization, Unitization.inlRingHom, algebraMap, inlRingHom
-/
instance instAlgebra : Algebra S (Unitization R A) where
  algebraMap := (Unitization.inlRingHom R A).comp (algebraMap S R)
  commutes' := fun s x => by
    induction x with
    | inl_add_inr =>
      change inl (algebraMap S R s) * _ = _ * inl (algebraMap S R s)
      rw [mul_add]; rw [add_mul]; rw [inl_mul_inl]; rw [inl_mul_inl]; rw [inl_mul_inr]; rw [inr_mul_inl]; rw [mul_comm]
  smul_def' := fun s x => by
    induction x with
    | inl_add_inr =>
      change _ = inl (algebraMap S R s) * _
      rw [mul_add]; rw [smul_add]; rw [Algebra.algebraMap_eq_smul_one]; rw [inl_mul_inl]; rw [inl_mul_inr]; rw [smul_one_mul]; rw [inl_smul]; rw [inr_smul]; rw [smul_one_smul]

/--
theorem `algebraMap_eq_inl_comp` / 定理 `algebraMap_eq_inl_comp`

English:
theorem algebraMap_eq_inl_comp
  statement: ⇑(algebraMap S (Unitization R A)) = inl ∘ algebraMap S R
  proof: rfl

中文:
定理 algebraMap_eq_inl_comp
  结论: ⇑(algebraMap S (Unitization R A)) = inl ∘ algebraMap S R
  证明: rfl
-/
theorem algebraMap_eq_inl_comp : ⇑(algebraMap S (Unitization R A)) = inl ∘ algebraMap S R :=
  rfl

/--
theorem `algebraMap_eq_inlRingHom_comp` / 定理 `algebraMap_eq_inlRingHom_comp`

English:
theorem algebraMap_eq_inlRingHom_comp
  proof: rfl

中文:
定理 algebraMap_eq_inlRingHom_comp
  证明: rfl
-/
theorem algebraMap_eq_inlRingHom_comp :
    algebraMap S (Unitization R A) = (inlRingHom R A).comp (algebraMap S R) :=
  rfl

/--
theorem `algebraMap_eq_inl` / 定理 `algebraMap_eq_inl`

English:
theorem algebraMap_eq_inl
  statement: ⇑(algebraMap R (Unitization R A)) = inl
  proof: rfl

中文:
定理 algebraMap_eq_inl
  结论: ⇑(algebraMap R (Unitization R A)) = inl
  证明: rfl
-/
theorem algebraMap_eq_inl : ⇑(algebraMap R (Unitization R A)) = inl :=
  rfl

/--
theorem `algebraMap_eq_inlRingHom` / 定理 `algebraMap_eq_inlRingHom`

English:
theorem algebraMap_eq_inlRingHom
  statement: algebraMap R (Unitization R A) = inlRingHom R A
  proof: rfl

中文:
定理 algebraMap_eq_inlRingHom
  结论: algebraMap R (Unitization R A) = inlRingHom R A
  证明: rfl
-/
theorem algebraMap_eq_inlRingHom : algebraMap R (Unitization R A) = inlRingHom R A :=
  rfl

/-- The canonical `R`-algebra projection `Unitization R A → R`. -/
@[simps]
/--
Definition of `fstHom` / `fstHom` 的定义

English:
definition fstHom
  signature: : Unitization R A ->ₐ[R] R where
  body: a.fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (A := A)
  map_add' := fst_add
  commutes' := fst_inl A

中文:
定义 fstHom
  签名: : Unitization R A ->ₐ[R] R where
  定义体: a.fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (A := A)
  map_add' := fst_add
  commutes' := fst_inl A

Depends on / 依赖: a.fst
-/
def fstHom : Unitization R A ->ₐ[R] R where
  toFun a := a.fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (A := A)
  map_add' := fst_add
  commutes' := fst_inl A

end Algebra

section coe

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `Unitization R A`
realized as a non-unital algebra homomorphism. -/
@[simps toFun]
/--
Definition of `inrNonUnitalAlgHom` / `inrNonUnitalAlgHom` 的定义

English:
definition inrNonUnitalAlgHom
  signature: (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  body: (↑)
  map_smul' := inr_smul R
  map_zero' := inr_zero R
  map_add' := inr_add R
  map_mul' := inr_mul R

中文:
定义 inrNonUnitalAlgHom
  签名: (R A : 类型) [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  定义体: (↑)
  map_smul' := inr_smul R
  map_zero' := inr_zero R
  map_add' := inr_add R
  map_mul' := inr_mul R
-/
def inrNonUnitalAlgHom (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A] :
    A ->ₙₐ[R] Unitization R A where
  toFun := (↑)
  map_smul' := inr_smul R
  map_zero' := inr_zero R
  map_add' := inr_add R
  map_mul' := inr_mul R

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `Unitization R A`
realized as a non-unital star algebra homomorphism. -/
@[simps! apply]
/--
Definition of `inrNonUnitalStarAlgHom` / `inrNonUnitalStarAlgHom` 的定义

English:
definition inrNonUnitalStarAlgHom
  signature: (R A : Type*) [CommSemiring R] [StarAddMonoid R]
  body: inrNonUnitalAlgHom R A
  map_star' := inr_star

中文:
定义 inrNonUnitalStarAlgHom
  签名: (R A : 类型) [CommSemiring R] [StarAddMonoid R]
  定义体: inrNonUnitalAlgHom R A
  map_star' := inr_star

Depends on / 依赖: inrNonUnitalAlgHom
-/
def inrNonUnitalStarAlgHom (R A : Type*) [CommSemiring R] [StarAddMonoid R]
    [NonUnitalSemiring A] [Star A] [Module R A] :
    A ->⋆ₙₐ[R] Unitization R A where
  toNonUnitalAlgHom := inrNonUnitalAlgHom R A
  map_star' := inr_star

/-- The star algebra equivalence obtained by restricting `Unitization.inrNonUnitalStarAlgHom`
to its range. -/
@[simps!]
/--
Definition of `inrRangeEquiv` / `inrRangeEquiv` 的定义

English:
definition inrRangeEquiv
  signature: (R A : Type*) [CommSemiring R] [StarAddMonoid R] [NonUnitalSemiring A]
  body: StarAlgEquiv.ofLeftInverse' (g := fun a => a.snd) (snd_inr R ·)

中文:
定义 inrRangeEquiv
  签名: (R A : 类型) [CommSemiring R] [StarAddMonoid R] [NonUnitalSemiring A]
  定义体: StarAlgEquiv.ofLeftInverse' (g := fun a => a.snd) (snd_inr R ·)

Depends on / 依赖: StarAlgEquiv, StarAlgEquiv.ofLeftInverse, a.snd, ofLeftInverse, snd_inr
-/
def inrRangeEquiv (R A : Type*) [CommSemiring R] [StarAddMonoid R] [NonUnitalSemiring A]
    [Star A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range (inrNonUnitalStarAlgHom R A) :=
  StarAlgEquiv.ofLeftInverse' (g := fun a => a.snd) (snd_inr R ·)

end coe

section AlgHom

variable {S R A : Type*} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type*} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type*} [Semiring C] [Algebra R C]

/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  statement: {F : Type*}
  proof: by
  refine DFunLike.ext φ ψ (fun x => ?_)
  induction x
  simp only [map_add, ← algebraMap_eq_inl, h, h']

中文:
定理 algHom_ext
  结论: {F : 类型}
  证明: by
  refine DFunLike.ext φ ψ (fun x => ?_)
  induction x
  simp only [map_add, ← algebraMap_eq_inl, h, h']

Depends on / 依赖: DFunLike, DFunLike.ext, algebraMap_eq_inl, map_add
-/
theorem algHom_ext {F : Type*}
    [FunLike F (Unitization R A) B] [AlgHomClass F S (Unitization R A) B] {φ ψ : F}
    (h : forall a : A, φ a = ψ a)
    (h' : forall r, φ (algebraMap R (Unitization R A) r) = ψ (algebraMap R (Unitization R A) r)) :
    φ = ψ := by
  refine DFunLike.ext φ ψ (fun x => ?_)
  induction x
  simp only [map_add, ← algebraMap_eq_inl, h, h']

/--
lemma `algHom_ext''` / 引理 `algHom_ext''`

English:
lemma algHom_ext''
  statement: {F : Type*}
  proof: algHom_ext h (fun r => by simp only [AlgHomClass.commutes])

中文:
引理 algHom_ext''
  结论: {F : 类型}
  证明: algHom_ext h (fun r => by simp only [AlgHomClass.commutes])

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, algHom_ext, commutes
-/
lemma algHom_ext'' {F : Type*}
    [FunLike F (Unitization R A) C] [AlgHomClass F R (Unitization R A) C] {φ ψ : F}
    (h : forall a : A, φ a = ψ a) : φ = ψ :=
  algHom_ext h (fun r => by simp only [AlgHomClass.commutes])

/-- See note [partially-applied ext lemmas] -/
@[ext 1100]
/--
theorem `algHom_ext'` / 定理 `algHom_ext'`

English:
theorem algHom_ext'
  statement: {φ ψ : Unitization R A ->ₐ[R] C}
  proof: algHom_ext'' (NonUnitalAlgHom.congr_fun h)

中文:
定理 algHom_ext'
  结论: {φ ψ : Unitization R A ->ₐ[R] C}
  证明: algHom_ext'' (NonUnitalAlgHom.congr_fun h)

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.congr_fun, algHom_ext, congr_fun
-/
theorem algHom_ext' {φ ψ : Unitization R A ->ₐ[R] C}
    (h :
      φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A) =
        ψ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)) :
    φ = ψ :=
  algHom_ext'' (NonUnitalAlgHom.congr_fun h)

/-- A non-unital algebra homomorphism from `A` into a unital `R`-algebra `C` lifts to a unital
algebra homomorphism from the unitization into `C`. This is extended to an `Equiv` in
`Unitization.lift` and that should be used instead. This declaration only exists for performance
reasons. -/
@[simps]
/--
Definition of `_root_.NonUnitalAlgHom.toAlgHom` / `_root_.NonUnitalAlgHom.toAlgHom` 的定义

English:
definition _root_.NonUnitalAlgHom.toAlgHom
  signature: (φ : A ->ₙₐ[R] C)
  body: fun x => algebraMap R C x.fst + φ x.snd
  map_one' := by simp only [fst_one, map_one, snd_one, φ.map_zero, add_zero]
  map_mul' := fun x y => by
    induction x with
    | inl_add_inr x_r x_a =>
      induction y with
      | inl_add_inr =>
        simp only [fst_mul, fst_add, fst_inl, fst_inr, snd_

中文:
定义 _root_.NonUnitalAlgHom.toAlgHom
  签名: (φ : A ->ₙₐ[R] C)
  定义体: fun x => algebraMap R C x.fst + φ x.snd
  map_one' := by simp only [fst_one, map_one, snd_one, φ.map_zero, add_zero]
  map_mul' := fun x y => by
    induction x with
    | inl_add_inr x_r x_a =>
      induction y with
      | inl_add_inr =>
        simp only [fst_mul, fst_add, fst_inl, fst_inr, snd_

Depends on / 依赖: algebraMap, x.fst, x.snd
-/
def _root_.NonUnitalAlgHom.toAlgHom (φ : A ->ₙₐ[R] C) : Unitization R A ->ₐ[R] C where
  toFun := fun x => algebraMap R C x.fst + φ x.snd
  map_one' := by simp only [fst_one, map_one, snd_one, φ.map_zero, add_zero]
  map_mul' := fun x y => by
    induction x with
    | inl_add_inr x_r x_a =>
      induction y with
      | inl_add_inr =>
        simp only [fst_mul, fst_add, fst_inl, fst_inr, snd_mul, snd_add, snd_inl, snd_inr, add_zero,
          map_mul, zero_add, map_add, map_smul φ]
        rw [add_mul]; rw [mul_add]; rw [mul_add]
        rw [← Algebra.commutes _ (φ x_a)]
        simp only [Algebra.algebraMap_eq_smul_one, smul_one_mul, add_assoc]
  map_zero' := by simp only [fst_zero, map_zero, snd_zero, φ.map_zero, add_zero]
  map_add' := fun x y => by
    induction x with
    | inl_add_inr =>
      induction y with
      | inl_add_inr =>
        simp only [fst_add, fst_inl, fst_inr, add_zero, map_add, snd_add, snd_inl, snd_inr,
          zero_add, φ.map_add]
        rw [add_add_add_comm]
  commutes' := fun r => by
    simp only [algebraMap_eq_inl, fst_inl, snd_inl, φ.map_zero, add_zero]


set_option backward.isDefEq.respectTransparency false in
/-- Non-unital algebra homomorphisms from `A` into a unital `R`-algebra `C` lift uniquely to
`Unitization R A →ₐ[R] C`. This is the universal property of the unitization. -/
@[simps! apply symm_apply]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (A ->ₙₐ[R] C) ≃ (Unitization R A ->ₐ[R] C) where
  body: NonUnitalAlgHom.toAlgHom
  invFun φ := φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)
  left_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]
  right_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]

中文:
定义 lift
  签名: : (A ->ₙₐ[R] C) ≃ (Unitization R A ->ₐ[R] C) where
  定义体: NonUnitalAlgHom.toAlgHom
  invFun φ := φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)
  left_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]
  right_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.toAlgHom, toAlgHom
-/
def lift : (A ->ₙₐ[R] C) ≃ (Unitization R A ->ₐ[R] C) where
  toFun := NonUnitalAlgHom.toAlgHom
  invFun φ := φ.toNonUnitalAlgHom.comp (inrNonUnitalAlgHom R A)
  left_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]
  right_inv φ := by ext; simp [NonUnitalAlgHomClass.toNonUnitalAlgHom]

/--
theorem `lift_symm_apply_apply` / 定理 `lift_symm_apply_apply`

English:
theorem lift_symm_apply_apply
  given: (φ : Unitization R A ->ₐ[R] C) (a : A)
  proof: rfl

@[simp]

中文:
定理 lift_symm_apply_apply
  条件: (φ : Unitization R A ->ₐ[R] C) (a : A)
  证明: rfl

@[simp]
-/
theorem lift_symm_apply_apply (φ : Unitization R A ->ₐ[R] C) (a : A) :
    Unitization.lift.symm φ a = φ a :=
  rfl

@[simp]
/--
lemma `_root_.NonUnitalAlgHom.toAlgHom_zero` / 引理 `_root_.NonUnitalAlgHom.toAlgHom_zero`

English:
lemma _root_.NonUnitalAlgHom.toAlgHom_zero
  proof: by
  ext
  simp

中文:
引理 _root_.NonUnitalAlgHom.toAlgHom_zero
  证明: by
  ext
  simp
-/
lemma _root_.NonUnitalAlgHom.toAlgHom_zero :
    ⇑(0 : A ->ₙₐ[R] R).toAlgHom = (fun x => x.fst) := by
  ext
  simp

end AlgHom

section StarAlgHom

variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [Semiring C] [Algebra R C] [StarRing C]

/-- See note [partially-applied ext lemmas] -/
@[ext]
/--
theorem `starAlgHom_ext` / 定理 `starAlgHom_ext`

English:
theorem starAlgHom_ext
  statement: {φ ψ : Unitization R A ->⋆ₐ[R] C}
  proof: Unitization.algHom_ext'' DFunLike.congr_fun h

中文:
定理 starAlgHom_ext
  结论: {φ ψ : Unitization R A ->⋆ₐ[R] C}
  证明: Unitization.algHom_ext'' DFunLike.congr_fun h

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Unitization, Unitization.algHom_ext, algHom_ext, congr_fun
-/
theorem starAlgHom_ext {φ ψ : Unitization R A ->⋆ₐ[R] C}
    (h : (φ : Unitization R A ->⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A) =
      (ψ : Unitization R A ->⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A)) :
    φ = ψ :=
Unitization.algHom_ext'' DFunLike.congr_fun h

variable [StarModule R C]

/-- Non-unital star algebra homomorphisms from `A` into a unital star `R`-algebra `C` lift uniquely
to `Unitization R A →⋆ₐ[R] C`. This is the universal property of the unitization. -/
@[simps! apply symm_apply]
/--
Definition of `starLift` / `starLift` 的定义

English:
definition starLift
  signature: : (A ->⋆ₙₐ[R] C) ≃ (Unitization R A ->⋆ₐ[R] C)
  body: { toFun := fun φ =>
  { toAlgHom := Unitization.lift φ.toNonUnitalAlgHom
    map_star' := fun x => by
      simp [map_star] }
  invFun φ := φ.toNonUnitalStarAlgHom.comp (inrNonUnitalStarAlgHom R A),
  left_inv _ := by ext; simp,
  right_inv _ := by ext; simp }

中文:
定义 starLift
  签名: : (A ->⋆ₙₐ[R] C) ≃ (Unitization R A ->⋆ₐ[R] C)
  定义体: { toFun := fun φ =>
  { toAlgHom := Unitization.lift φ.toNonUnitalAlgHom
    map_star' := fun x => by
      simp [map_star] }
  invFun φ := φ.toNonUnitalStarAlgHom.comp (inrNonUnitalStarAlgHom R A),
  left_inv _ := by ext; simp,
  right_inv _ := by ext; simp }

Depends on / 依赖: Unitization, Unitization.lift, inrNonUnitalStarAlgHom, invFun, left_inv, map_star, right_inv, toAlgHom, toNonUnitalAlgHom, toNonUnitalStarAlgHom, toNonUnitalStarAlgHom.comp
-/
def starLift : (A ->⋆ₙₐ[R] C) ≃ (Unitization R A ->⋆ₐ[R] C) :=
{ toFun := fun φ =>
  { toAlgHom := Unitization.lift φ.toNonUnitalAlgHom
    map_star' := fun x => by
      simp [map_star] }
  invFun φ := φ.toNonUnitalStarAlgHom.comp (inrNonUnitalStarAlgHom R A),
  left_inv _ := by ext; simp,
  right_inv _ := by ext; simp }

/--
theorem `starLift_symm_apply_apply` / 定理 `starLift_symm_apply_apply`

English:
theorem starLift_symm_apply_apply
  given: (φ : Unitization R A ->⋆ₐ[R] C) (a : A)
  proof: rfl

中文:
定理 starLift_symm_apply_apply
  条件: (φ : Unitization R A ->⋆ₐ[R] C) (a : A)
  证明: rfl
-/
@[simp] theorem starLift_symm_apply_apply (φ : Unitization R A ->⋆ₐ[R] C) (a : A) :
    Unitization.starLift.symm φ a = φ a :=
  rfl

end StarAlgHom

section StarMap

variable {R A B C : Type*} [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalSemiring B] [StarRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
variable [NonUnitalSemiring C] [StarRing C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]
variable [StarModule R B] [StarModule R C]

/-- The functorial map on morphisms between the category of non-unital C⋆-algebras with non-unital
star homomorphisms and unital C⋆-algebras with unital star homomorphisms.

This sends `φ : A →⋆ₙₐ[R] B` to a map `Unitization R A →⋆ₐ[R] Unitization R B` given by the formula
`(r, a) ↦ (r, φ a)` (or perhaps more precisely,
`algebraMap R _ r + ↑a ↦ algebraMap R _ r + ↑(φ a)`). -/
@[simps! apply]
/--
Definition of `starMap` / `starMap` 的定义

English:
definition starMap
  signature: (φ : A ->⋆ₙₐ[R] B)
  body: Unitization.starLift (Unitization.inrNonUnitalStarAlgHom R B).comp φ

@[simp high]

中文:
定义 starMap
  签名: (φ : A ->⋆ₙₐ[R] B)
  定义体: Unitization.starLift (Unitization.inrNonUnitalStarAlgHom R B).comp φ

@[simp high]

Depends on / 依赖: Unitization, Unitization.inrNonUnitalStarAlgHom, Unitization.starLift, inrNonUnitalStarAlgHom, starLift
-/
def starMap (φ : A ->⋆ₙₐ[R] B) : Unitization R A ->⋆ₐ[R] Unitization R B :=
Unitization.starLift (Unitization.inrNonUnitalStarAlgHom R B).comp φ

@[simp high]
/--
lemma `starMap_inr` / 引理 `starMap_inr`

English:
lemma starMap_inr
  given: (φ : A ->⋆ₙₐ[R] B) (a : A)
  proof: by
  simp

@[simp high]

中文:
引理 starMap_inr
  条件: (φ : A ->⋆ₙₐ[R] B) (a : A)
  证明: by
  simp

@[simp high]
-/
lemma starMap_inr (φ : A ->⋆ₙₐ[R] B) (a : A) :
    starMap φ (inr a) = inr (φ a) := by
  simp

@[simp high]
/--
lemma `starMap_inl` / 引理 `starMap_inl`

English:
lemma starMap_inl
  given: (φ : A ->⋆ₙₐ[R] B) (r : R)
  proof: by
  simp

中文:
引理 starMap_inl
  条件: (φ : A ->⋆ₙₐ[R] B) (r : R)
  证明: by
  simp
-/
lemma starMap_inl (φ : A ->⋆ₙₐ[R] B) (r : R) :
    starMap φ (inl r) = algebraMap R (Unitization R B) r := by
  simp

/--
lemma `starMap_injective` / 引理 `starMap_injective`

English:
lemma starMap_injective
  given: {φ : A ->⋆ₙₐ[R] B} (hφ : Function.Injective φ)
  proof: by
  intro x y h
  ext
  · simpa using! congr($(h).fst)
· exact hφ by simpa [algebraMap_eq_inl] using! congr($(h).snd)

中文:
引理 starMap_injective
  条件: {φ : A ->⋆ₙₐ[R] B} (hφ : Function.Injective φ)
  证明: by
  intro x y h
  ext
  · simpa using! congr($(h).fst)
· exact hφ by simpa [algebraMap_eq_inl] using! congr($(h).snd)

Depends on / 依赖: algebraMap_eq_inl
-/
lemma starMap_injective {φ : A ->⋆ₙₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (starMap φ) := by
  intro x y h
  ext
  · simpa using! congr($(h).fst)
· exact hφ by simpa [algebraMap_eq_inl] using! congr($(h).snd)

/--
lemma `starMap_surjective` / 引理 `starMap_surjective`

English:
lemma starMap_surjective
  given: {φ : A ->⋆ₙₐ[R] B} (hφ : Function.Surjective φ)
  proof: by
  intro x
  induction x using Unitization.ind with
  | inl_add_inr r b =>
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨mk (r, a), by rfl⟩

中文:
引理 starMap_surjective
  条件: {φ : A ->⋆ₙₐ[R] B} (hφ : Function.Surjective φ)
  证明: by
  intro x
  induction x using Unitization.ind with
  | inl_add_inr r b =>
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨mk (r, a), by rfl⟩

Depends on / 依赖: Unitization, Unitization.ind, inl_add_inr
-/
lemma starMap_surjective {φ : A ->⋆ₙₐ[R] B} (hφ : Function.Surjective φ) :
    Function.Surjective (starMap φ) := by
  intro x
  induction x using Unitization.ind with
  | inl_add_inr r b =>
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨mk (r, a), by rfl⟩

/--
lemma `starMap_comp` / 引理 `starMap_comp`

English:
lemma starMap_comp
  given: {φ : A ->⋆ₙₐ[R] B} {ψ : B ->⋆ₙₐ[R] C}
  proof: by
  ext; all_goals simp

中文:
引理 starMap_comp
  条件: {φ : A ->⋆ₙₐ[R] B} {ψ : B ->⋆ₙₐ[R] C}
  证明: by
  ext; all_goals simp

Depends on / 依赖: all_goals
-/
lemma starMap_comp {φ : A ->⋆ₙₐ[R] B} {ψ : B ->⋆ₙₐ[R] C} :
    starMap (ψ.comp φ) = (starMap ψ).comp (starMap φ) := by
  ext; all_goals simp

/-- `starMap` is functorial:
`starMap (NonUnitalStarAlgHom.id R B) = StarAlgHom.id R (Unitization R B)`. -/
@[simp]
/--
lemma `starMap_id` / 引理 `starMap_id`

English:
lemma starMap_id
  statement: starMap (NonUnitalStarAlgHom.id R B) = StarAlgHom.id R (Unitization R B)
  proof: by
  ext; all_goals simp

中文:
引理 starMap_id
  结论: starMap (NonUnitalStarAlgHom.id R B) = StarAlgHom.id R (Unitization R B)
  证明: by
  ext; all_goals simp

Depends on / 依赖: all_goals
-/
lemma starMap_id : starMap (NonUnitalStarAlgHom.id R B) = StarAlgHom.id R (Unitization R B) := by
  ext; all_goals simp

end StarMap

section StarNormal

variable {R A : Type*} [Semiring R]
variable [StarAddMonoid R] [Star A] {a : A}


@[simp]
/--
lemma `isSelfAdjoint_inr` / 引理 `isSelfAdjoint_inr`

English:
lemma isSelfAdjoint_inr
  statement: IsSelfAdjoint (a : Unitization R A) ↔ IsSelfAdjoint a
  proof: by
  simp only [isSelfAdjoint_iff, ← inr_star, inr_injective.eq_iff]

alias ⟨_root_.IsSelfAdjoint.of_inr, _⟩ := isSelfAdjoint_inr

中文:
引理 isSelfAdjoint_inr
  结论: IsSelfAdjoint (a : Unitization R A) ↔ IsSelfAdjoint a
  证明: by
  simp only [isSelfAdjoint_iff, ← inr_star, inr_injective.eq_iff]

alias ⟨_root_.IsSelfAdjoint.of_inr, _⟩ := isSelfAdjoint_inr

Depends on / 依赖: eq_iff, inr_injective, inr_injective.eq_iff, inr_star, isSelfAdjoint_iff
-/
lemma isSelfAdjoint_inr : IsSelfAdjoint (a : Unitization R A) ↔ IsSelfAdjoint a := by
  simp only [isSelfAdjoint_iff, ← inr_star, inr_injective.eq_iff]

alias ⟨_root_.IsSelfAdjoint.of_inr, _⟩ := isSelfAdjoint_inr

variable (R) in
/--
lemma `_root_.IsSelfAdjoint.inr` / 引理 `_root_.IsSelfAdjoint.inr`

English:
lemma _root_.IsSelfAdjoint.inr
  given: (ha : IsSelfAdjoint a)
  statement: IsSelfAdjoint (a : Unitization R A)
  proof: isSelfAdjoint_inr.mpr ha

中文:
引理 _root_.IsSelfAdjoint.inr
  条件: (ha : IsSelfAdjoint a)
  结论: IsSelfAdjoint (a : Unitization R A)
  证明: isSelfAdjoint_inr.mpr ha

Depends on / 依赖: isSelfAdjoint_inr, isSelfAdjoint_inr.mpr
-/
lemma _root_.IsSelfAdjoint.inr (ha : IsSelfAdjoint a) : IsSelfAdjoint (a : Unitization R A) :=
  isSelfAdjoint_inr.mpr ha

variable [AddCommMonoid A] [Mul A] [SMulWithZero R A]

@[simp]
/--
lemma `isStarNormal_inr` / 引理 `isStarNormal_inr`

English:
lemma isStarNormal_inr
  statement: IsStarNormal (a : Unitization R A) ↔ IsStarNormal a
  proof: by
  simp only [isStarNormal_iff, commute_iff_eq, ← inr_star, ← inr_mul, inr_injective.eq_iff]

alias ⟨_root_.IsStarNormal.of_inr, _⟩ := isStarNormal_inr

中文:
引理 isStarNormal_inr
  结论: IsStarNormal (a : Unitization R A) ↔ IsStarNormal a
  证明: by
  simp only [isStarNormal_iff, commute_iff_eq, ← inr_star, ← inr_mul, inr_injective.eq_iff]

alias ⟨_root_.IsStarNormal.of_inr, _⟩ := isStarNormal_inr

Depends on / 依赖: commute_iff_eq, eq_iff, inr_injective, inr_injective.eq_iff, inr_mul, inr_star, isStarNormal_iff
-/
lemma isStarNormal_inr : IsStarNormal (a : Unitization R A) ↔ IsStarNormal a := by
  simp only [isStarNormal_iff, commute_iff_eq, ← inr_star, ← inr_mul, inr_injective.eq_iff]

alias ⟨_root_.IsStarNormal.of_inr, _⟩ := isStarNormal_inr

variable (R a) in
/--
Instance `instIsStarNormal` / 实例 `instIsStarNormal`

English:
instance instIsStarNormal
  signature: (a : A) [IsStarNormal a]
  body: isStarNormal_inr.mpr ‹_›

中文:
实例 instIsStarNormal
  签名: (a : A) [IsStarNormal a]
  定义体: isStarNormal_inr.mpr ‹_›

Depends on / 依赖: isStarNormal_inr, isStarNormal_inr.mpr
-/
instance instIsStarNormal (a : A) [IsStarNormal a] :
    IsStarNormal (a : Unitization R A) :=
  isStarNormal_inr.mpr ‹_›

end StarNormal

@[simp]
/--
lemma `isIdempotentElem_inr_iff` / 引理 `isIdempotentElem_inr_iff`

English:
lemma isIdempotentElem_inr_iff
  statement: (R : Type*) {A : Type*} [MulZeroClass R]
  proof: by
  simp only [IsIdempotentElem, ← inr_mul, inr_injective.eq_iff]

alias ⟨_, IsIdempotentElem.inr⟩ := isIdempotentElem_inr_iff

@[grind =]

中文:
引理 isIdempotentElem_inr_iff
  结论: (R : 类型) {A : 类型} [MulZeroClass R]
  证明: by
  simp only [IsIdempotentElem, ← inr_mul, inr_injective.eq_iff]

alias ⟨_, IsIdempotentElem.inr⟩ := isIdempotentElem_inr_iff

@[grind =]

Depends on / 依赖: IsIdempotentElem, eq_iff, inr_injective, inr_injective.eq_iff, inr_mul
-/
lemma isIdempotentElem_inr_iff (R : Type*) {A : Type*} [MulZeroClass R]
    [AddZeroClass A] [Mul A] [SMulWithZero R A] {a : A} :
    IsIdempotentElem (a : Unitization R A) ↔ IsIdempotentElem a := by
  simp only [IsIdempotentElem, ← inr_mul, inr_injective.eq_iff]

alias ⟨_, IsIdempotentElem.inr⟩ := isIdempotentElem_inr_iff

@[grind =]
/--
lemma `isStarProjection_inr_iff` / 引理 `isStarProjection_inr_iff`

English:
lemma isStarProjection_inr_iff
  statement: {R A : Type*} [Semiring R] [StarRing R] [NonUnitalSemiring A]
  proof: by
  simp [isStarProjection_iff]

protected alias ⟨_root_.IsStarProjection.of_inr, _root_.IsStarProjection.inr⟩ :=
  isStarProjection_inr_iff

中文:
引理 isStarProjection_inr_iff
  结论: {R A : 类型} [Semiring R] [StarRing R] [NonUnitalSemiring A]
  证明: by
  simp [isStarProjection_iff]

protected alias ⟨_root_.IsStarProjection.of_inr, _root_.IsStarProjection.inr⟩ :=
  isStarProjection_inr_iff

Depends on / 依赖: isStarProjection_iff
-/
lemma isStarProjection_inr_iff {R A : Type*} [Semiring R] [StarRing R] [NonUnitalSemiring A]
    [StarRing A] [Module R A] {p : A} :
    IsStarProjection (p : Unitization R A) ↔ IsStarProjection p := by
  simp [isStarProjection_iff]

protected alias ⟨_root_.IsStarProjection.of_inr, _root_.IsStarProjection.inr⟩ :=
  isStarProjection_inr_iff

end Unitization
