/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser, Antoine Chambert-Loir, María-Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Trivial Square-Zero Extension

Given a ring `R` together with an `(R, R)`-bimodule `M`, the trivial square-zero extension of `M`
over `R` is defined to be the `R`-algebra `R ⊕ M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + m₁ r₂`.

It is a square-zero extension because `M^2 = 0`.

Note that expressing this requires bimodules; we write these in general for a
not-necessarily-commutative `R` as:
```lean
variable {R M : Type*} [Semiring R] [AddCommMonoid M]
variable [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
```
If we instead work with a commutative `R'` acting symmetrically on `M`, we write
```lean
variable {R' M : Type*} [CommSemiring R'] [AddCommMonoid M]
variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
```
noting that in this context `IsCentralScalar R' M` implies `SMulCommClass R' R'ᵐᵒᵖ M`.

Many of the later results in this file are only stated for the commutative `R'` for simplicity.

## Main definitions

* `TrivSqZeroExt.inl`, `TrivSqZeroExt.inr`: the canonical inclusions into
  `TrivSqZeroExt R M`.
* `TrivSqZeroExt.fst`, `TrivSqZeroExt.snd`: the canonical projections from
  `TrivSqZeroExt R M`.
* `triv_sq_zero_ext.algebra`: the associated `R`-algebra structure.
* `TrivSqZeroExt.lift`: the universal property of the trivial square-zero extension; algebra
  morphisms `TrivSqZeroExt R M →ₐ[S] A` are uniquely defined by an algebra morphism `f : R →ₐ[S] A`
  on `R` and a linear map `g : M →ₗ[S] A` on `M` such that:
  * `g x * g y = 0`: the elements of `M` continue to square to zero.
  * `g (r •> x) = f r * g x` and `g (x <• r) = g x * f r`: left and right actions are preserved by
    `g`.
* `TrivSqZeroExt.lift`: the universal property of the trivial square-zero extension; algebra
  morphisms `TrivSqZeroExt R M →ₐ[R] A` are uniquely defined by linear maps `M →ₗ[R] A` for
  which the product of any two elements in the range is zero.

-/

@[expose] public section

universe u v w

/--
Definition of `TrivSqZeroExt` / `TrivSqZeroExt` 的定义

English:
definition TrivSqZeroExt
  signature: (R : Type u) (M : Type v)
  body: R × M

local notation "tsze" => TrivSqZeroExt

中文:
定义 TrivSqZeroExt
  签名: (R : 类型u) (M : 类型v)
  定义体: R × M

local notation "tsze" => TrivSqZeroExt
-/
def TrivSqZeroExt (R : Type u) (M : Type v) :=
  R × M

local notation "tsze" => TrivSqZeroExt

open scoped RightActions

namespace TrivSqZeroExt

open MulOpposite

section Basic

variable {R : Type u} {M : Type v}

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: [Zero M] (r : R)
  body: (r, 0)

中文:
定义 inl
  签名: [Zero M] (r : R)
  定义体: (r, 0)
-/
def inl [Zero M] (r : R) : tsze R M :=
  (r, 0)

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: [Zero R] (m : M)
  body: (0, m)

中文:
定义 inr
  签名: [Zero R] (m : M)
  定义体: (0, m)

Depends on / 依赖: f.retract, isClosedImmersion_of_comp_eq_id, retract
-/
def inr [Zero R] (m : M) : tsze R M :=
  (0, m)

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: (x : tsze R M)
  body: x.1

中文:
定义 fst
  签名: (x : tsze R M)
  定义体: x.1

Depends on / 依赖: IsOver, Scheme, Subsingleton, X.Over, f.IsOver
-/
def fst (x : tsze R M) : R :=
  x.1

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: (x : tsze R M)
  body: x.2

@[simp]

中文:
定义 snd
  签名: (x : tsze R M)
  定义体: x.2

@[simp]
-/
def snd (x : tsze R M) : M :=
  x.2

@[simp]
/--
theorem `fst_mk` / 定理 `fst_mk`

English:
theorem fst_mk
  given: (r : R) (m : M)
  statement: fst (r, m) = r
  proof: rfl

@[simp]

中文:
定理 fst_mk
  条件: (r : R) (m : M)
  结论: fst (r, m) = r
  证明: rfl

@[simp]
-/
theorem fst_mk (r : R) (m : M) : fst (r, m) = r :=
  rfl

@[simp]
/--
theorem `snd_mk` / 定理 `snd_mk`

English:
theorem snd_mk
  given: (r : R) (m : M)
  statement: snd (r, m) = m
  proof: rfl

@[ext]

中文:
定理 snd_mk
  条件: (r : R) (m : M)
  结论: snd (r, m) = m
  证明: rfl

@[ext]
-/
theorem snd_mk (r : R) (m : M) : snd (r, m) = m :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd)
  statement: x = y
  proof: Prod.ext h1 h2

中文:
定理 ext
  条件: {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd)
  结论: x = y
  证明: Prod.ext h1 h2

Depends on / 依赖: Prod.ext
-/
theorem ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext h1 h2

section

variable (M)

@[simp]
/--
theorem `fst_inl` / 定理 `fst_inl`

English:
theorem fst_inl
  given: [Zero M] (r : R)
  statement: (inl r : tsze R M).fst = r
  proof: rfl

@[simp]

中文:
定理 fst_inl
  条件: [Zero M] (r : R)
  结论: (inl r : tsze R M).fst = r
  证明: rfl

@[simp]
-/
theorem fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst = r :=
  rfl

@[simp]
/--
theorem `snd_inl` / 定理 `snd_inl`

English:
theorem snd_inl
  given: [Zero M] (r : R)
  statement: (inl r : tsze R M).snd = 0
  proof: rfl

@[simp]

中文:
定理 snd_inl
  条件: [Zero M] (r : R)
  结论: (inl r : tsze R M).snd = 0
  证明: rfl

@[simp]
-/
theorem snd_inl [Zero M] (r : R) : (inl r : tsze R M).snd = 0 :=
  rfl

@[simp]
/--
theorem `fst_comp_inl` / 定理 `fst_comp_inl`

English:
theorem fst_comp_inl
  given: [Zero M]
  statement: fst ∘ (inl : R -> tsze R M) = id
  proof: rfl

@[simp]

中文:
定理 fst_comp_inl
  条件: [Zero M]
  结论: fst ∘ (inl : R -> tsze R M) = id
  证明: rfl

@[simp]
-/
theorem fst_comp_inl [Zero M] : fst ∘ (inl : R -> tsze R M) = id :=
  rfl

@[simp]
/--
theorem `snd_comp_inl` / 定理 `snd_comp_inl`

English:
theorem snd_comp_inl
  given: [Zero M]
  statement: snd ∘ (inl : R -> tsze R M) = 0
  proof: rfl

中文:
定理 snd_comp_inl
  条件: [Zero M]
  结论: snd ∘ (inl : R -> tsze R M) = 0
  证明: rfl
-/
theorem snd_comp_inl [Zero M] : snd ∘ (inl : R -> tsze R M) = 0 :=
  rfl

end

section

variable (R)

@[simp]
/--
theorem `fst_inr` / 定理 `fst_inr`

English:
theorem fst_inr
  given: [Zero R] (m : M)
  statement: (inr m : tsze R M).fst = 0
  proof: rfl

@[simp]

中文:
定理 fst_inr
  条件: [Zero R] (m : M)
  结论: (inr m : tsze R M).fst = 0
  证明: rfl

@[simp]

Depends on / 依赖: HasAffineProperty, HasAffineProperty.isLocal_affineProperty, isLocal_affineProperty
-/
theorem fst_inr [Zero R] (m : M) : (inr m : tsze R M).fst = 0 :=
  rfl

@[simp]
/--
theorem `snd_inr` / 定理 `snd_inr`

English:
theorem snd_inr
  given: [Zero R] (m : M)
  statement: (inr m : tsze R M).snd = m
  proof: rfl

@[simp]

中文:
定理 snd_inr
  条件: [Zero R] (m : M)
  结论: (inr m : tsze R M).snd = m
  证明: rfl

@[simp]

Depends on / 依赖: HasAffineProperty, HasAffineProperty.of_isZariskiLocalAtTarget, of_isZariskiLocalAtTarget
-/
theorem snd_inr [Zero R] (m : M) : (inr m : tsze R M).snd = m :=
  rfl

@[simp]
/--
theorem `fst_comp_inr` / 定理 `fst_comp_inr`

English:
theorem fst_comp_inr
  given: [Zero R]
  statement: fst ∘ (inr : M -> tsze R M) = 0
  proof: rfl

@[simp]

中文:
定理 fst_comp_inr
  条件: [Zero R]
  结论: fst ∘ (inr : M -> tsze R M) = 0
  证明: rfl

@[simp]

Depends on / 依赖: IsOpenImmersion, IsZariskiLocalAtSource, IsZariskiLocalAtSource.comp, IsZariskiLocalAtSource.mk, IsZariskiLocalAtSource.of_iSup_eq_top, P.of_postcomp, Scheme, X.Opens, comp_diagonal, diagonal, of_iSup_eq_top, of_postcomp, pullback, pullback.comp_diagonal, pullback.diagonal, pullback.map
-/
theorem fst_comp_inr [Zero R] : fst ∘ (inr : M -> tsze R M) = 0 :=
  rfl

@[simp]
/--
theorem `snd_comp_inr` / 定理 `snd_comp_inr`

English:
theorem snd_comp_inr
  given: [Zero R]
  statement: snd ∘ (inr : M -> tsze R M) = id
  proof: rfl

中文:
定理 snd_comp_inr
  条件: [Zero R]
  结论: snd ∘ (inr : M -> tsze R M) = id
  证明: rfl
-/
theorem snd_comp_inr [Zero R] : snd ∘ (inr : M -> tsze R M) = id :=
  rfl

end

/--
theorem `fst_surjective` / 定理 `fst_surjective`

English:
theorem fst_surjective
  given: [Nonempty M]
  statement: Function.Surjective (fst : tsze R M -> R)
  proof: Prod.fst_surjective

中文:
定理 fst_surjective
  条件: [Nonempty M]
  结论: Function.Surjective (fst : tsze R M -> R)
  证明: Prod.fst_surjective

Depends on / 依赖: Prod.fst_surjective, fst_surjective
-/
theorem fst_surjective [Nonempty M] : Function.Surjective (fst : tsze R M -> R) :=
  Prod.fst_surjective

/--
theorem `snd_surjective` / 定理 `snd_surjective`

English:
theorem snd_surjective
  given: [Nonempty R]
  statement: Function.Surjective (snd : tsze R M -> M)
  proof: Prod.snd_surjective

中文:
定理 snd_surjective
  条件: [Nonempty R]
  结论: Function.Surjective (snd : tsze R M -> M)
  证明: Prod.snd_surjective

Depends on / 依赖: Prod.snd_surjective, snd_surjective
-/
theorem snd_surjective [Nonempty R] : Function.Surjective (snd : tsze R M -> M) :=
  Prod.snd_surjective

/--
theorem `inl_injective` / 定理 `inl_injective`

English:
theorem inl_injective
  given: [Zero M]
  statement: Function.Injective (inl : R -> tsze R M)
  proof: Function.LeftInverse.injective fst_inl _

中文:
定理 inl_injective
  条件: [Zero M]
  结论: Function.Injective (inl : R -> tsze R M)
  证明: Function.LeftInverse.injective fst_inl _

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, fst_inl, injective
-/
theorem inl_injective [Zero M] : Function.Injective (inl : R -> tsze R M) :=
Function.LeftInverse.injective fst_inl _

/--
theorem `inr_injective` / 定理 `inr_injective`

English:
theorem inr_injective
  given: [Zero R]
  statement: Function.Injective (inr : M -> tsze R M)
  proof: Function.LeftInverse.injective snd_inr _

中文:
定理 inr_injective
  条件: [Zero R]
  结论: Function.Injective (inr : M -> tsze R M)
  证明: Function.LeftInverse.injective snd_inr _

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, snd_inr
-/
theorem inr_injective [Zero R] : Function.Injective (inr : M -> tsze R M) :=
Function.LeftInverse.injective snd_inr _

end Basic

/-! ### Structures inherited from `Prod`

Additive operators and scalar multiplication operate elementwise. -/


section Additive

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: [Inhabited R] [Inhabited M]
  body: inferInstanceAs Inhabited (R × M)

中文:
实例 inhabited
  签名: [Inhabited R] [Inhabited M]
  定义体: inferInstanceAs Inhabited (R × M)

Depends on / 依赖: Inhabited
-/
instance inhabited [Inhabited R] [Inhabited M] : Inhabited (tsze R M) :=
inferInstanceAs Inhabited (R × M)

/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: [Zero R] [Zero M]
  body: inferInstanceAs Zero (R × M)

中文:
实例 zero
  签名: [Zero R] [Zero M]
  定义体: inferInstanceAs Zero (R × M)
-/
instance zero [Zero R] [Zero M] : Zero (tsze R M) :=
inferInstanceAs Zero (R × M)

/--
Instance `add` / 实例 `add`

English:
instance add
  signature: [Add R] [Add M]
  body: inferInstanceAs Add (R × M)

中文:
实例 add
  签名: [Add R] [Add M]
  定义体: inferInstanceAs Add (R × M)
-/
instance add [Add R] [Add M] : Add (tsze R M) :=
inferInstanceAs Add (R × M)

/--
Instance `sub` / 实例 `sub`

English:
instance sub
  signature: [Sub R] [Sub M]
  body: inferInstanceAs Sub (R × M)

中文:
实例 sub
  签名: [Sub R] [Sub M]
  定义体: inferInstanceAs Sub (R × M)
-/
instance sub [Sub R] [Sub M] : Sub (tsze R M) :=
inferInstanceAs Sub (R × M)

/--
Instance `neg` / 实例 `neg`

English:
instance neg
  signature: [Neg R] [Neg M]
  body: inferInstanceAs Neg (R × M)

中文:
实例 neg
  签名: [Neg R] [Neg M]
  定义体: inferInstanceAs Neg (R × M)
-/
instance neg [Neg R] [Neg M] : Neg (tsze R M) :=
inferInstanceAs Neg (R × M)

/--
Instance `addSemigroup` / 实例 `addSemigroup`

English:
instance addSemigroup
  signature: [AddSemigroup R] [AddSemigroup M]
  body: inferInstanceAs AddSemigroup (R × M)

中文:
实例 addSemigroup
  签名: [AddSemigroup R] [AddSemigroup M]
  定义体: inferInstanceAs AddSemigroup (R × M)

Depends on / 依赖: AddSemigroup
-/
instance addSemigroup [AddSemigroup R] [AddSemigroup M] : AddSemigroup (tsze R M) :=
inferInstanceAs AddSemigroup (R × M)

/--
Instance `addZeroClass` / 实例 `addZeroClass`

English:
instance addZeroClass
  signature: [AddZeroClass R] [AddZeroClass M]
  body: inferInstanceAs AddZeroClass (R × M)

中文:
实例 addZeroClass
  签名: [AddZeroClass R] [AddZeroClass M]
  定义体: inferInstanceAs AddZeroClass (R × M)

Depends on / 依赖: AddZeroClass
-/
instance addZeroClass [AddZeroClass R] [AddZeroClass M] : AddZeroClass (tsze R M) :=
inferInstanceAs AddZeroClass (R × M)

/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [SMul S R] [SMul S M]
  body: inferInstanceAs SMul S (R × M)

中文:
实例 smul
  签名: [SMul S R] [SMul S M]
  定义体: inferInstanceAs SMul S (R × M)
-/
instance smul [SMul S R] [SMul S M] : SMul S (tsze R M) :=
inferInstanceAs SMul S (R × M)

/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: [AddMonoid R] [AddMonoid M]
  body: letI := smul (S := Nat) (R := R) (M := M); (· • ·)
__ : AddMonoid (tsze R M) := inferInstanceAs AddMonoid (R × M)

中文:
实例 addMonoid
  签名: [AddMonoid R] [AddMonoid M]
  定义体: letI := smul (S := Nat) (R := R) (M := M); (· • ·)
__ : AddMonoid (tsze R M) := inferInstanceAs AddMonoid (R × M)
-/
instance addMonoid [AddMonoid R] [AddMonoid M] : AddMonoid (tsze R M) where
  nsmul := letI := smul (S := Nat) (R := R) (M := M); (· • ·)
__ : AddMonoid (tsze R M) := inferInstanceAs AddMonoid (R × M)

/--
Instance `addGroup` / 实例 `addGroup`

English:
instance addGroup
  signature: [AddGroup R] [AddGroup M]
  body: letI := smul (S := Int) (R := R) (M := M); (· • ·)
__ : AddGroup (tsze R M) := inferInstanceAs AddGroup (R × M)

中文:
实例 addGroup
  签名: [AddGroup R] [AddGroup M]
  定义体: letI := smul (S := Int) (R := R) (M := M); (· • ·)
__ : AddGroup (tsze R M) := inferInstanceAs AddGroup (R × M)
-/
instance addGroup [AddGroup R] [AddGroup M] : AddGroup (tsze R M) where
  zsmul := letI := smul (S := Int) (R := R) (M := M); (· • ·)
__ : AddGroup (tsze R M) := inferInstanceAs AddGroup (R × M)

/--
Instance `addCommSemigroup` / 实例 `addCommSemigroup`

English:
instance addCommSemigroup
  signature: [AddCommSemigroup R] [AddCommSemigroup M]
  body: inferInstanceAs AddCommSemigroup (R × M)

中文:
实例 addCommSemigroup
  签名: [AddCommSemigroup R] [AddCommSemigroup M]
  定义体: inferInstanceAs AddCommSemigroup (R × M)

Depends on / 依赖: AddCommSemigroup
-/
instance addCommSemigroup [AddCommSemigroup R] [AddCommSemigroup M] : AddCommSemigroup (tsze R M) :=
inferInstanceAs AddCommSemigroup (R × M)

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: [AddCommMonoid R] [AddCommMonoid M]
  body: inferInstanceAs AddCommMonoid (R × M)

中文:
实例 addCommMonoid
  签名: [AddCommMonoid R] [AddCommMonoid M]
  定义体: inferInstanceAs AddCommMonoid (R × M)

Depends on / 依赖: AddCommMonoid
-/
instance addCommMonoid [AddCommMonoid R] [AddCommMonoid M] : AddCommMonoid (tsze R M) :=
inferInstanceAs AddCommMonoid (R × M)

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: [AddCommGroup R] [AddCommGroup M]
  body: inferInstanceAs AddCommGroup (R × M)

中文:
实例 addCommGroup
  签名: [AddCommGroup R] [AddCommGroup M]
  定义体: inferInstanceAs AddCommGroup (R × M)

Depends on / 依赖: AddCommGroup
-/
instance addCommGroup [AddCommGroup R] [AddCommGroup M] : AddCommGroup (tsze R M) :=
inferInstanceAs AddCommGroup (R × M)

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul T R] [SMul T M] [SMul S R] [SMul S M] [SMul T S]
  body: inferInstanceAs IsScalarTower T S (R × M)

中文:
实例 isScalarTower
  签名: [SMul T R] [SMul T M] [SMul S R] [SMul S M] [SMul T S]
  定义体: inferInstanceAs IsScalarTower T S (R × M)

Depends on / 依赖: IsScalarTower
-/
instance isScalarTower [SMul T R] [SMul T M] [SMul S R] [SMul S M] [SMul T S]
    [IsScalarTower T S R] [IsScalarTower T S M] : IsScalarTower T S (tsze R M) :=
inferInstanceAs IsScalarTower T S (R × M)

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: [SMul T R] [SMul T M] [SMul S R] [SMul S M]
  body: inferInstanceAs SMulCommClass T S (R × M)

中文:
实例 smulCommClass
  签名: [SMul T R] [SMul T M] [SMul S R] [SMul S M]
  定义体: inferInstanceAs SMulCommClass T S (R × M)

Depends on / 依赖: SMulCommClass
-/
instance smulCommClass [SMul T R] [SMul T M] [SMul S R] [SMul S M]
    [SMulCommClass T S R] [SMulCommClass T S M] : SMulCommClass T S (tsze R M) :=
inferInstanceAs SMulCommClass T S (R × M)

/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [SMul S R] [SMul S M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsCentralScalar S R]
  body: inferInstanceAs IsCentralScalar S (R × M)

中文:
实例 isCentralScalar
  签名: [SMul S R] [SMul S M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsCentralScalar S R]
  定义体: inferInstanceAs IsCentralScalar S (R × M)

Depends on / 依赖: IsCentralScalar
-/
instance isCentralScalar [SMul S R] [SMul S M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsCentralScalar S R]
    [IsCentralScalar S M] : IsCentralScalar S (tsze R M) :=
inferInstanceAs IsCentralScalar S (R × M)

/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: [Monoid S] [MulAction S R] [MulAction S M]
  body: inferInstanceAs MulAction S (R × M)

中文:
实例 mulAction
  签名: [Monoid S] [MulAction S R] [MulAction S M]
  定义体: inferInstanceAs MulAction S (R × M)

Depends on / 依赖: MulAction
-/
instance mulAction [Monoid S] [MulAction S R] [MulAction S M] : MulAction S (tsze R M) :=
inferInstanceAs MulAction S (R × M)

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: [Monoid S] [AddMonoid R] [AddMonoid M]
  body: inferInstanceAs DistribMulAction S (R × M)

中文:
实例 distribMulAction
  签名: [Monoid S] [AddMonoid R] [AddMonoid M]
  定义体: inferInstanceAs DistribMulAction S (R × M)

Depends on / 依赖: DistribMulAction
-/
instance distribMulAction [Monoid S] [AddMonoid R] [AddMonoid M]
    [DistribMulAction S R] [DistribMulAction S M] : DistribMulAction S (tsze R M) :=
inferInstanceAs DistribMulAction S (R × M)

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [Module S R] [Module S M]
  body: inferInstanceAs Module S (R × M)

中文:
实例 module
  签名: [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [Module S R] [Module S M]
  定义体: inferInstanceAs Module S (R × M)

Depends on / 依赖: Module
-/
instance module [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [Module S R] [Module S M] :
    Module S (tsze R M) :=
inferInstanceAs Module S (R × M)

/--
Instance `instNontrivial_of_left` / 实例 `instNontrivial_of_left`

English:
instance instNontrivial_of_left
  signature: {R M : Type*} [Nontrivial R] [Nonempty M]
  body: inferInstanceAs Nontrivial (R × M)

中文:
实例 instNontrivial_of_left
  签名: {R M : 类型} [Nontrivial R] [Nonempty M]
  定义体: inferInstanceAs Nontrivial (R × M)

Depends on / 依赖: Nontrivial
-/
instance instNontrivial_of_left {R M : Type*} [Nontrivial R] [Nonempty M] :
    Nontrivial (tsze R M) :=
inferInstanceAs Nontrivial (R × M)

/--
Instance `instNontrivial_of_right` / 实例 `instNontrivial_of_right`

English:
instance instNontrivial_of_right
  signature: {R M : Type*} [Nonempty R] [Nontrivial M]
  body: inferInstanceAs Nontrivial (R × M)

@[simp]

中文:
实例 instNontrivial_of_right
  签名: {R M : 类型} [Nonempty R] [Nontrivial M]
  定义体: inferInstanceAs Nontrivial (R × M)

@[simp]

Depends on / 依赖: Nontrivial
-/
instance instNontrivial_of_right {R M : Type*} [Nonempty R] [Nontrivial M] :
    Nontrivial (tsze R M) :=
inferInstanceAs Nontrivial (R × M)

@[simp]
/--
theorem `fst_zero` / 定理 `fst_zero`

English:
theorem fst_zero
  given: [Zero R] [Zero M]
  statement: (0 : tsze R M).fst = 0
  proof: rfl

@[simp]

中文:
定理 fst_zero
  条件: [Zero R] [Zero M]
  结论: (0 : tsze R M).fst = 0
  证明: rfl

@[simp]

Depends on / 依赖: IsOpenImmersion
-/
theorem fst_zero [Zero R] [Zero M] : (0 : tsze R M).fst = 0 :=
  rfl

@[simp]
/--
theorem `snd_zero` / 定理 `snd_zero`

English:
theorem snd_zero
  given: [Zero R] [Zero M]
  statement: (0 : tsze R M).snd = 0
  proof: rfl

@[simp]

中文:
定理 snd_zero
  条件: [Zero R] [Zero M]
  结论: (0 : tsze R M).snd = 0
  证明: rfl

@[simp]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
theorem snd_zero [Zero R] [Zero M] : (0 : tsze R M).snd = 0 :=
  rfl

@[simp]
/--
theorem `fst_add` / 定理 `fst_add`

English:
theorem fst_add
  given: [Add R] [Add M] (x₁ x₂ : tsze R M)
  statement: (x₁ + x₂).fst = x₁.fst + x₂.fst
  proof: rfl

@[simp]

中文:
定理 fst_add
  条件: [Add R] [Add M] (x₁ x₂ : tsze R M)
  结论: (x₁ + x₂).fst = x₁.fst + x₂.fst
  证明: rfl

@[simp]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
theorem fst_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).fst = x₁.fst + x₂.fst :=
  rfl

@[simp]
/--
theorem `snd_add` / 定理 `snd_add`

English:
theorem snd_add
  given: [Add R] [Add M] (x₁ x₂ : tsze R M)
  statement: (x₁ + x₂).snd = x₁.snd + x₂.snd
  proof: rfl

@[simp]

中文:
定理 snd_add
  条件: [Add R] [Add M] (x₁ x₂ : tsze R M)
  结论: (x₁ + x₂).snd = x₁.snd + x₂.snd
  证明: rfl

@[simp]

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, restrict
-/
theorem snd_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).snd = x₁.snd + x₂.snd :=
  rfl

@[simp]
/--
theorem `fst_neg` / 定理 `fst_neg`

English:
theorem fst_neg
  given: [Neg R] [Neg M] (x : tsze R M)
  statement: (-x).fst = -x.fst
  proof: rfl

@[simp]

中文:
定理 fst_neg
  条件: [Neg R] [Neg M] (x : tsze R M)
  结论: (-x).fst = -x.fst
  证明: rfl

@[simp]

Depends on / 依赖: Scheme, Scheme.Hom.resLE, infer_instance
-/
theorem fst_neg [Neg R] [Neg M] (x : tsze R M) : (-x).fst = -x.fst :=
  rfl

@[simp]
/--
theorem `snd_neg` / 定理 `snd_neg`

English:
theorem snd_neg
  given: [Neg R] [Neg M] (x : tsze R M)
  statement: (-x).snd = -x.snd
  proof: rfl

@[simp]

中文:
定理 snd_neg
  条件: [Neg R] [Neg M] (x : tsze R M)
  结论: (-x).snd = -x.snd
  证明: rfl

@[simp]
-/
theorem snd_neg [Neg R] [Neg M] (x : tsze R M) : (-x).snd = -x.snd :=
  rfl

@[simp]
/--
theorem `fst_sub` / 定理 `fst_sub`

English:
theorem fst_sub
  given: [Sub R] [Sub M] (x₁ x₂ : tsze R M)
  statement: (x₁ - x₂).fst = x₁.fst - x₂.fst
  proof: rfl

@[simp]

中文:
定理 fst_sub
  条件: [Sub R] [Sub M] (x₁ x₂ : tsze R M)
  结论: (x₁ - x₂).fst = x₁.fst - x₂.fst
  证明: rfl

@[simp]
-/
theorem fst_sub [Sub R] [Sub M] (x₁ x₂ : tsze R M) : (x₁ - x₂).fst = x₁.fst - x₂.fst :=
  rfl

@[simp]
/--
theorem `snd_sub` / 定理 `snd_sub`

English:
theorem snd_sub
  given: [Sub R] [Sub M] (x₁ x₂ : tsze R M)
  statement: (x₁ - x₂).snd = x₁.snd - x₂.snd
  proof: rfl

@[simp]

中文:
定理 snd_sub
  条件: [Sub R] [Sub M] (x₁ x₂ : tsze R M)
  结论: (x₁ - x₂).snd = x₁.snd - x₂.snd
  证明: rfl

@[simp]
-/
theorem snd_sub [Sub R] [Sub M] (x₁ x₂ : tsze R M) : (x₁ - x₂).snd = x₁.snd - x₂.snd :=
  rfl

@[simp]
/--
theorem `fst_smul` / 定理 `fst_smul`

English:
theorem fst_smul
  given: [SMul S R] [SMul S M] (s : S) (x : tsze R M)
  statement: (s • x).fst = s • x.fst
  proof: rfl

@[simp]

中文:
定理 fst_smul
  条件: [SMul S R] [SMul S M] (s : S) (x : tsze R M)
  结论: (s • x).fst = s • x.fst
  证明: rfl

@[simp]

Depends on / 依赖: Smooth
-/
theorem fst_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).fst = s • x.fst :=
  rfl

@[simp]
/--
theorem `snd_smul` / 定理 `snd_smul`

English:
theorem snd_smul
  given: [SMul S R] [SMul S M] (s : S) (x : tsze R M)
  statement: (s • x).snd = s • x.snd
  proof: rfl

中文:
定理 snd_smul
  条件: [SMul S R] [SMul S M] (s : S) (x : tsze R M)
  结论: (s • x).snd = s • x.snd
  证明: rfl

Depends on / 依赖: FormallyUnramified
-/
theorem snd_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).snd = s • x.snd :=
  rfl

/--
theorem `fst_sum` / 定理 `fst_sum`

English:
theorem fst_sum
  given: {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> tsze R M)
  proof: Prod.fst_sum

中文:
定理 fst_sum
  条件: {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> tsze R M)
  证明: Prod.fst_sum

Depends on / 依赖: Prod.fst_sum, fst_sum
-/
theorem fst_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> tsze R M) :
    (∑ i in s, f i).fst = ∑ i in s, (f i).fst :=
  Prod.fst_sum

/--
theorem `snd_sum` / 定理 `snd_sum`

English:
theorem snd_sum
  given: {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> tsze R M)
  proof: Prod.snd_sum

中文:
定理 snd_sum
  条件: {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> tsze R M)
  证明: Prod.snd_sum

Depends on / 依赖: Prod.snd_sum, snd_sum
-/
theorem snd_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> tsze R M) :
    (∑ i in s, f i).snd = ∑ i in s, (f i).snd :=
  Prod.snd_sum

section

variable (M)

@[simp]
/--
theorem `inl_zero` / 定理 `inl_zero`

English:
theorem inl_zero
  given: [Zero R] [Zero M]
  statement: (inl 0 : tsze R M) = 0
  proof: rfl

@[simp]

中文:
定理 inl_zero
  条件: [Zero R] [Zero M]
  结论: (inl 0 : tsze R M) = 0
  证明: rfl

@[simp]
-/
theorem inl_zero [Zero R] [Zero M] : (inl 0 : tsze R M) = 0 :=
  rfl

@[simp]
/--
theorem `inl_add` / 定理 `inl_add`

English:
theorem inl_add
  given: [Add R] [AddZeroClass M] (r₁ r₂ : R)
  proof: ext rfl (add_zero 0).symm

@[simp]

中文:
定理 inl_add
  条件: [Add R] [AddZeroClass M] (r₁ r₂ : R)
  证明: ext rfl (add_zero 0).symm

@[simp]

Depends on / 依赖: add_zero
-/
theorem inl_add [Add R] [AddZeroClass M] (r₁ r₂ : R) :
    (inl (r₁ + r₂) : tsze R M) = inl r₁ + inl r₂ :=
  ext rfl (add_zero 0).symm

@[simp]
/--
theorem `inl_neg` / 定理 `inl_neg`

English:
theorem inl_neg
  given: [Neg R] [NegZeroClass M] (r : R)
  statement: (inl (-r) : tsze R M) = -inl r
  proof: ext rfl neg_zero.symm

@[simp]

中文:
定理 inl_neg
  条件: [Neg R] [NegZeroClass M] (r : R)
  结论: (inl (-r) : tsze R M) = -inl r
  证明: ext rfl neg_zero.symm

@[simp]

Depends on / 依赖: neg_zero, neg_zero.symm
-/
theorem inl_neg [Neg R] [NegZeroClass M] (r : R) : (inl (-r) : tsze R M) = -inl r :=
  ext rfl neg_zero.symm

@[simp]
/--
theorem `inl_sub` / 定理 `inl_sub`

English:
theorem inl_sub
  given: [Sub R] [SubNegZeroMonoid M] (r₁ r₂ : R)
  proof: ext rfl (sub_zero _).symm

@[simp]

中文:
定理 inl_sub
  条件: [Sub R] [SubNegZeroMonoid M] (r₁ r₂ : R)
  证明: ext rfl (sub_zero _).symm

@[simp]

Depends on / 依赖: Y.prop, sub_zero
-/
theorem inl_sub [Sub R] [SubNegZeroMonoid M] (r₁ r₂ : R) :
    (inl (r₁ - r₂) : tsze R M) = inl r₁ - inl r₂ :=
  ext rfl (sub_zero _).symm

@[simp]
/--
theorem `inl_smul` / 定理 `inl_smul`

English:
theorem inl_smul
  given: [Monoid S] [AddMonoid M] [SMul S R] [DistribMulAction S M] (s : S) (r : R)
  proof: ext rfl (smul_zero s).symm

中文:
定理 inl_smul
  条件: [Monoid S] [AddMonoid M] [SMul S R] [DistribMulAction S M] (s : S) (r : R)
  证明: ext rfl (smul_zero s).symm

Depends on / 依赖: CategoryTheory, CategoryTheory.Over.w, Etale.of_comp, Y.hom, f.left, infer_instance, of_comp, smul_zero
-/
theorem inl_smul [Monoid S] [AddMonoid M] [SMul S R] [DistribMulAction S M] (s : S) (r : R) :
    (inl (s • r) : tsze R M) = s • inl r :=
  ext rfl (smul_zero s).symm

/--
theorem `inl_sum` / 定理 `inl_sum`

English:
theorem inl_sum
  given: {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> R)
  proof: map_sum (LinearMap.inl Nat _ _) _ _

中文:
定理 inl_sum
  条件: {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> R)
  证明: map_sum (LinearMap.inl Nat _ _) _ _

Depends on / 依赖: LinearMap, LinearMap.inl, map_sum
-/
theorem inl_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> R) :
    (inl (∑ i in s, f i) : tsze R M) = ∑ i in s, inl (f i) :=
  map_sum (LinearMap.inl Nat _ _) _ _

end

section

variable (R)

@[simp]
/--
theorem `inr_zero` / 定理 `inr_zero`

English:
theorem inr_zero
  given: [Zero R] [Zero M]
  statement: (inr 0 : tsze R M) = 0
  proof: rfl

@[simp]

中文:
定理 inr_zero
  条件: [Zero R] [Zero M]
  结论: (inr 0 : tsze R M) = 0
  证明: rfl

@[simp]
-/
theorem inr_zero [Zero R] [Zero M] : (inr 0 : tsze R M) = 0 :=
  rfl

@[simp]
/--
theorem `inr_add` / 定理 `inr_add`

English:
theorem inr_add
  given: [AddZeroClass R] [Add M] (m₁ m₂ : M)
  proof: ext (add_zero 0).symm rfl

@[simp]

中文:
定理 inr_add
  条件: [AddZeroClass R] [Add M] (m₁ m₂ : M)
  证明: ext (add_zero 0).symm rfl

@[simp]

Depends on / 依赖: add_zero
-/
theorem inr_add [AddZeroClass R] [Add M] (m₁ m₂ : M) :
    (inr (m₁ + m₂) : tsze R M) = inr m₁ + inr m₂ :=
  ext (add_zero 0).symm rfl

@[simp]
/--
theorem `inr_neg` / 定理 `inr_neg`

English:
theorem inr_neg
  given: [NegZeroClass R] [Neg M] (m : M)
  statement: (inr (-m) : tsze R M) = -inr m
  proof: ext neg_zero.symm rfl

@[simp]

中文:
定理 inr_neg
  条件: [NegZeroClass R] [Neg M] (m : M)
  结论: (inr (-m) : tsze R M) = -inr m
  证明: ext neg_zero.symm rfl

@[simp]

Depends on / 依赖: neg_zero, neg_zero.symm
-/
theorem inr_neg [NegZeroClass R] [Neg M] (m : M) : (inr (-m) : tsze R M) = -inr m :=
  ext neg_zero.symm rfl

@[simp]
/--
theorem `inr_sub` / 定理 `inr_sub`

English:
theorem inr_sub
  given: [SubNegZeroMonoid R] [Sub M] (m₁ m₂ : M)
  proof: ext (sub_zero _).symm rfl

@[simp]

中文:
定理 inr_sub
  条件: [SubNegZeroMonoid R] [Sub M] (m₁ m₂ : M)
  证明: ext (sub_zero _).symm rfl

@[simp]

Depends on / 依赖: sub_zero
-/
theorem inr_sub [SubNegZeroMonoid R] [Sub M] (m₁ m₂ : M) :
    (inr (m₁ - m₂) : tsze R M) = inr m₁ - inr m₂ :=
  ext (sub_zero _).symm rfl

@[simp]
/--
theorem `inr_smul` / 定理 `inr_smul`

English:
theorem inr_smul
  given: [Zero R] [SMulZeroClass S R] [SMul S M] (r : S) (m : M)
  proof: ext (smul_zero _).symm rfl

中文:
定理 inr_smul
  条件: [Zero R] [SMulZeroClass S R] [SMul S M] (r : S) (m : M)
  证明: ext (smul_zero _).symm rfl

Depends on / 依赖: smul_zero
-/
theorem inr_smul [Zero R] [SMulZeroClass S R] [SMul S M] (r : S) (m : M) :
    (inr (r • m) : tsze R M) = r • inr m :=
  ext (smul_zero _).symm rfl

/--
theorem `inr_sum` / 定理 `inr_sum`

English:
theorem inr_sum
  given: {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> M)
  proof: map_sum (LinearMap.inr Nat _ _) _ _

中文:
定理 inr_sum
  条件: {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> M)
  证明: map_sum (LinearMap.inr Nat _ _) _ _

Depends on / 依赖: LinearMap, LinearMap.inr, map_sum
-/
theorem inr_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> M) :
    (inr (∑ i in s, f i) : tsze R M) = ∑ i in s, inr (f i) :=
  map_sum (LinearMap.inr Nat _ _) _ _

end

/--
theorem `inl_fst_add_inr_snd_eq` / 定理 `inl_fst_add_inr_snd_eq`

English:
theorem inl_fst_add_inr_snd_eq
  given: [AddZeroClass R] [AddZeroClass M] (x : tsze R M)
  proof: ext (add_zero x.1) (zero_add x.2)

中文:
定理 inl_fst_add_inr_snd_eq
  条件: [AddZeroClass R] [AddZeroClass M] (x : tsze R M)
  证明: ext (add_zero x.1) (zero_add x.2)

Depends on / 依赖: add_zero, zero_add
-/
theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass M] (x : tsze R M) :
    inl x.fst + inr x.snd = x :=
  ext (add_zero x.1) (zero_add x.2)

/-- To show a property hold on all `TrivSqZeroExt R M` it suffices to show it holds
on terms of the form `inl r + inr m`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  statement: {R M} [AddZeroClass R] [AddZeroClass M] {P : TrivSqZeroExt R M -> Prop}
  proof: inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.1 x.2

中文:
定理 ind
  结论: {R M} [AddZeroClass R] [AddZeroClass M] {P : TrivSqZeroExt R M -> 命题}
  证明: inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.1 x.2

Depends on / 依赖: Y.prop, inl_add_inr, inl_fst_add_inr_snd_eq
-/
theorem ind {R M} [AddZeroClass R] [AddZeroClass M] {P : TrivSqZeroExt R M -> Prop}
    (inl_add_inr : forall r m, P (inl r + inr m)) (x) : P x :=
  inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.1 x.2

/--
theorem `linearMap_ext` / 定理 `linearMap_ext`

English:
theorem linearMap_ext
  statement: {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [AddCommMonoid N]
  proof: LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

中文:
定理 linearMap_ext
  结论: {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [AddCommMonoid N]
  证明: LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

Depends on / 依赖: LinearMap, LinearMap.ext, LinearMap.prod_ext, prod_ext
-/
theorem linearMap_ext {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [AddCommMonoid N]
    [Module S R] [Module S M] [Module S N] ⦃f g : tsze R M ->ₗ[S] N⦄
    (hl : forall r, f (inl r) = g (inl r)) (hr : forall m, f (inr m) = g (inr m)) : f = g :=
  LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

variable (R M)

/-- The canonical `R`-linear inclusion `M → TrivSqZeroExt R M`. -/
@[simps apply]
/--
Definition of `inrHom` / `inrHom` 的定义

English:
definition inrHom
  signature: [Semiring R] [AddCommMonoid M] [Module R M]
  body: { LinearMap.inr R R M with toFun := inr }

中文:
定义 inrHom
  签名: [Semiring R] [AddCommMonoid M] [Module R M]
  定义体: { LinearMap.inr R R M with toFun := inr }

Depends on / 依赖: LinearMap, LinearMap.inr
-/
def inrHom [Semiring R] [AddCommMonoid M] [Module R M] : M ->ₗ[R] tsze R M :=
  { LinearMap.inr R R M with toFun := inr }

/-- The canonical `R`-linear projection `TrivSqZeroExt R M → M`. -/
@[simps apply]
/--
Definition of `sndHom` / `sndHom` 的定义

English:
definition sndHom
  signature: [Semiring R] [AddCommMonoid M] [Module R M]
  body: { LinearMap.snd _ _ _ with toFun := snd }

中文:
定义 sndHom
  签名: [Semiring R] [AddCommMonoid M] [Module R M]
  定义体: { LinearMap.snd _ _ _ with toFun := snd }

Depends on / 依赖: LinearMap, LinearMap.snd
-/
def sndHom [Semiring R] [AddCommMonoid M] [Module R M] : tsze R M ->ₗ[R] M :=
  { LinearMap.snd _ _ _ with toFun := snd }

end Additive

/-! ### Multiplicative structure -/


section Mul

variable {R : Type u} {M : Type v}

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: [One R] [Zero M]
  body: ⟨(1, 0)⟩

中文:
实例 one
  签名: [One R] [Zero M]
  定义体: ⟨(1, 0)⟩
-/
instance one [One R] [Zero M] : One (tsze R M) :=
  ⟨(1, 0)⟩

/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M]
  body: ⟨fun x y => (x.1 * y.1, x.1 •> y.2 + x.2 <• y.1)⟩

@[simp]

中文:
实例 mul
  签名: [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M]
  定义体: ⟨fun x y => (x.1 * y.1, x.1 •> y.2 + x.2 <• y.1)⟩

@[simp]
-/
instance mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] : Mul (tsze R M) :=
  ⟨fun x y => (x.1 * y.1, x.1 •> y.2 + x.2 <• y.1)⟩

@[simp]
/--
theorem `fst_one` / 定理 `fst_one`

English:
theorem fst_one
  given: [One R] [Zero M]
  statement: (1 : tsze R M).fst = 1
  proof: rfl

@[simp]

中文:
定理 fst_one
  条件: [One R] [Zero M]
  结论: (1 : tsze R M).fst = 1
  证明: rfl

@[simp]
-/
theorem fst_one [One R] [Zero M] : (1 : tsze R M).fst = 1 :=
  rfl

@[simp]
/--
theorem `snd_one` / 定理 `snd_one`

English:
theorem snd_one
  given: [One R] [Zero M]
  statement: (1 : tsze R M).snd = 0
  proof: rfl

@[simp]

中文:
定理 snd_one
  条件: [One R] [Zero M]
  结论: (1 : tsze R M).snd = 0
  证明: rfl

@[simp]
-/
theorem snd_one [One R] [Zero M] : (1 : tsze R M).snd = 0 :=
  rfl

@[simp]
/--
theorem `fst_mul` / 定理 `fst_mul`

English:
theorem fst_mul
  given: [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M)
  proof: rfl

@[simp]

中文:
定理 fst_mul
  条件: [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M)
  证明: rfl

@[simp]
-/
theorem fst_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst :=
  rfl

@[simp]
/--
theorem `snd_mul` / 定理 `snd_mul`

English:
theorem snd_mul
  given: [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M)
  proof: rfl

中文:
定理 snd_mul
  条件: [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M)
  证明: rfl

Depends on / 依赖: IsFinite, of_isIso
-/
theorem snd_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).snd = x₁.fst •> x₂.snd + x₁.snd <• x₂.fst :=
  rfl

section

variable (M)

@[simp]
/--
theorem `inl_one` / 定理 `inl_one`

English:
theorem inl_one
  given: [One R] [Zero M]
  statement: (inl 1 : tsze R M) = 1
  proof: rfl

@[simp]

中文:
定理 inl_one
  条件: [One R] [Zero M]
  结论: (inl 1 : tsze R M) = 1
  证明: rfl

@[simp]

Depends on / 依赖: IsFinite, IsStableUnderComposition, IsStableUnderComposition.comp_mem, comp_mem
-/
theorem inl_one [One R] [Zero M] : (inl 1 : tsze R M) = 1 :=
  rfl

@[simp]
/--
theorem `inl_mul` / 定理 `inl_mul`

English:
theorem inl_mul
  statement: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  proof: ext rfl show (0 : M) = r₁ •> (0 : M) + (0 : M) <• r₂ by rw [smul_zero, zero_add, smul_zero]

中文:
定理 inl_mul
  结论: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  证明: ext rfl show (0 : M) = r₁ •> (0 : M) + (0 : M) <• r₂ by rw [smul_zero, zero_add, smul_zero]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst, smul_zero, zero_add
-/
theorem inl_mul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r₁ r₂ : R) : (inl (r₁ * r₂) : tsze R M) = inl r₁ * inl r₂ :=
ext rfl show (0 : M) = r₁ •> (0 : M) + (0 : M) <• r₂ by rw [smul_zero, zero_add, smul_zero]

/--
theorem `inl_mul_inl` / 定理 `inl_mul_inl`

English:
theorem inl_mul_inl
  statement: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  proof: (inl_mul M r₁ r₂).symm

中文:
定理 inl_mul_inl
  结论: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  证明: (inl_mul M r₁ r₂).symm

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, inl_mul, pullback_snd
-/
theorem inl_mul_inl [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r₁ r₂ : R) : (inl r₁ * inl r₂ : tsze R M) = inl (r₁ * r₂) :=
  (inl_mul M r₁ r₂).symm

end

section

variable (R)

@[simp]
/--
theorem `inr_mul_inr` / 定理 `inr_mul_inr`

English:
theorem inr_mul_inr
  given: [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (m₁ m₂ : M)
  proof: ext (mul_zero _)
    show (0 : R) •> m₂ + m₁ <• (0 : R) = 0 by rw [zero_smul, zero_add, op_zero, zero_smul]

中文:
定理 inr_mul_inr
  条件: [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (m₁ m₂ : M)
  证明: ext (mul_zero _)
    show (0 : R) •> m₂ + m₁ <• (0 : R) = 0 by rw [zero_smul, zero_add, op_zero, zero_smul]

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, mul_zero, op_zero, restrict, zero_add, zero_smul
-/
theorem inr_mul_inr [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (m₁ m₂ : M) :
    (inr m₁ * inr m₂ : tsze R M) = 0 :=
ext (mul_zero _)
    show (0 : R) •> m₂ + m₁ <• (0 : R) = 0 by rw [zero_smul, zero_add, op_zero, zero_smul]

end

/--
theorem `inl_mul_inr` / 定理 `inl_mul_inr`

English:
theorem inl_mul_inr
  statement: [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]
  proof: ext (mul_zero r)
    show r • m + (0 : Rᵐᵒᵖ) • (0 : M) = r • m by rw [smul_zero, add_zero]

中文:
定理 inl_mul_inr
  结论: [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]
  证明: ext (mul_zero r)
    show r • m + (0 : Rᵐᵒᵖ) • (0 : M) = r • m by rw [smul_zero, add_zero]

Depends on / 依赖: add_zero, mul_zero, smul_zero
-/
theorem inl_mul_inr [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] (r : R) (m : M) : (inl r * inr m : tsze R M) = inr (r • m) :=
ext (mul_zero r)
    show r • m + (0 : Rᵐᵒᵖ) • (0 : M) = r • m by rw [smul_zero, add_zero]

/--
theorem `inr_mul_inl` / 定理 `inr_mul_inl`

English:
theorem inr_mul_inl
  statement: [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]
  proof: ext (zero_mul r)
    show (0 : R) •> (0 : M) + m <• r = m <• r by rw [smul_zero, zero_add]

中文:
定理 inr_mul_inl
  结论: [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]
  证明: ext (zero_mul r)
    show (0 : R) •> (0 : M) + m <• r = m <• r by rw [smul_zero, zero_add]

Depends on / 依赖: smul_zero, zero_add, zero_mul
-/
theorem inr_mul_inl [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] (r : R) (m : M) : (inr m * inl r : tsze R M) = inr (m <• r) :=
ext (zero_mul r)
    show (0 : R) •> (0 : M) + m <• r = m <• r by rw [smul_zero, zero_add]

/--
theorem `inl_mul_eq_smul` / 定理 `inl_mul_eq_smul`

English:
theorem inl_mul_eq_smul
  statement: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  proof: ext rfl (by dsimp; rw [smul_zero, add_zero])

中文:
定理 inl_mul_eq_smul
  结论: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  证明: ext rfl (by dsimp; rw [smul_zero, add_zero])

Depends on / 依赖: IsFinite, IsIntegralHom, add_zero, smul_zero
-/
theorem inl_mul_eq_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r : R) (x : tsze R M) :
    inl r * x = r •> x :=
  ext rfl (by dsimp; rw [smul_zero, add_zero])

/--
theorem `mul_inl_eq_op_smul` / 定理 `mul_inl_eq_op_smul`

English:
theorem mul_inl_eq_op_smul
  statement: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  proof: ext rfl (by dsimp; rw [smul_zero, zero_add])

中文:
定理 mul_inl_eq_op_smul
  结论: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  证明: ext rfl (by dsimp; rw [smul_zero, zero_add])

Depends on / 依赖: IsFinite, LocallyOfFiniteType, smul_zero, zero_add
-/
theorem mul_inl_eq_op_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (r : R) :
    x * inl r = x <• r :=
  ext rfl (by dsimp; rw [smul_zero, zero_add])

/--
Instance `mulOneClass` / 实例 `mulOneClass`

English:
instance mulOneClass
  signature: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  body: fun x =>
ext (one_mul x.1)
      show (1 : R) •> x.2 + (0 : M) <• x.1 = x.2 by rw [one_smul, smul_zero, add_zero]
  mul_one := fun x =>
ext (mul_one x.1)
      show x.1 • (0 : M) + x.2 <• (1 : R) = x.2 by rw [smul_zero, zero_add, op_one, one_smul]

中文:
实例 mulOneClass
  签名: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  定义体: fun x =>
ext (one_mul x.1)
      show (1 : R) •> x.2 + (0 : M) <• x.1 = x.2 by rw [one_smul, smul_zero, add_zero]
  mul_one := fun x =>
ext (mul_one x.1)
      show x.1 • (0 : M) + x.2 <• (1 : R) = x.2 by rw [smul_zero, zero_add, op_one, one_smul]
-/
instance mulOneClass [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] :
    MulOneClass (tsze R M) where
  one_mul := fun x =>
ext (one_mul x.1)
      show (1 : R) •> x.2 + (0 : M) <• x.1 = x.2 by rw [one_smul, smul_zero, add_zero]
  mul_one := fun x =>
ext (mul_one x.1)
      show x.1 • (0 : M) + x.2 <• (1 : R) = x.2 by rw [smul_zero, zero_add, op_one, one_smul]

/--
Instance `addMonoidWithOne` / 实例 `addMonoidWithOne`

English:
instance addMonoidWithOne
  signature: [AddMonoidWithOne R] [AddMonoid M]
  body: fun n => inl n
  natCast_zero := by simp [Nat.cast]
  natCast_succ := fun _ => by ext <;> simp [Nat.cast]

@[simp]

中文:
实例 addMonoidWithOne
  签名: [AddMonoidWithOne R] [AddMonoid M]
  定义体: fun n => inl n
  natCast_zero := by simp [Nat.cast]
  natCast_succ := fun _ => by ext <;> simp [Nat.cast]

@[simp]
-/
instance addMonoidWithOne [AddMonoidWithOne R] [AddMonoid M] : AddMonoidWithOne (tsze R M) where
  natCast := fun n => inl n
  natCast_zero := by simp [Nat.cast]
  natCast_succ := fun _ => by ext <;> simp [Nat.cast]

@[simp]
/--
theorem `fst_natCast` / 定理 `fst_natCast`

English:
theorem fst_natCast
  given: [AddMonoidWithOne R] [AddMonoid M] (n : Nat)
  statement: (n : tsze R M).fst = n
  proof: rfl

@[simp]

中文:
定理 fst_natCast
  条件: [AddMonoidWithOne R] [AddMonoid M] (n : 自然数)
  结论: (n : tsze R M).fst = n
  证明: rfl

@[simp]

Depends on / 依赖: IsClosedImmersion, IsFinite
-/
theorem fst_natCast [AddMonoidWithOne R] [AddMonoid M] (n : Nat) : (n : tsze R M).fst = n :=
  rfl

@[simp]
/--
theorem `snd_natCast` / 定理 `snd_natCast`

English:
theorem snd_natCast
  given: [AddMonoidWithOne R] [AddMonoid M] (n : Nat)
  statement: (n : tsze R M).snd = 0
  proof: rfl

@[simp]

中文:
定理 snd_natCast
  条件: [AddMonoidWithOne R] [AddMonoid M] (n : 自然数)
  结论: (n : tsze R M).snd = 0
  证明: rfl

@[simp]
-/
theorem snd_natCast [AddMonoidWithOne R] [AddMonoid M] (n : Nat) : (n : tsze R M).snd = 0 :=
  rfl

@[simp]
/--
theorem `inl_natCast` / 定理 `inl_natCast`

English:
theorem inl_natCast
  given: [AddMonoidWithOne R] [AddMonoid M] (n : Nat)
  statement: (inl n : tsze R M) = n
  proof: rfl

中文:
定理 inl_natCast
  条件: [AddMonoidWithOne R] [AddMonoid M] (n : 自然数)
  结论: (inl n : tsze R M) = n
  证明: rfl
-/
theorem inl_natCast [AddMonoidWithOne R] [AddMonoid M] (n : Nat) : (inl n : tsze R M) = n :=
  rfl

/--
Instance `addGroupWithOne` / 实例 `addGroupWithOne`

English:
instance addGroupWithOne
  signature: [AddGroupWithOne R] [AddGroup M]
  body: fun z => inl z
  intCast_ofNat := fun _n => ext (Int.cast_natCast _) rfl
  intCast_negSucc := fun _n => ext (Int.cast_negSucc _) neg_zero.symm

@[simp]

中文:
实例 addGroupWithOne
  签名: [AddGroupWithOne R] [AddGroup M]
  定义体: fun z => inl z
  intCast_ofNat := fun _n => ext (Int.cast_natCast _) rfl
  intCast_negSucc := fun _n => ext (Int.cast_negSucc _) neg_zero.symm

@[simp]
-/
instance addGroupWithOne [AddGroupWithOne R] [AddGroup M] : AddGroupWithOne (tsze R M) where
  intCast := fun z => inl z
  intCast_ofNat := fun _n => ext (Int.cast_natCast _) rfl
  intCast_negSucc := fun _n => ext (Int.cast_negSucc _) neg_zero.symm

@[simp]
/--
theorem `fst_intCast` / 定理 `fst_intCast`

English:
theorem fst_intCast
  given: [AddGroupWithOne R] [AddGroup M] (z : Int)
  statement: (z : tsze R M).fst = z
  proof: rfl

@[simp]

中文:
定理 fst_intCast
  条件: [AddGroupWithOne R] [AddGroup M] (z : 整数)
  结论: (z : tsze R M).fst = z
  证明: rfl

@[simp]

Depends on / 依赖: HasAffineProperty, HasAffineProperty.coprodDesc_affineAnd, RingHom, RingHom.finite_algebraMap.mpr, RingHom.finite_respectsIso, algebraize, coprodDesc_affineAnd, finite_algebraMap, finite_respectsIso, intros
-/
theorem fst_intCast [AddGroupWithOne R] [AddGroup M] (z : Int) : (z : tsze R M).fst = z :=
  rfl

@[simp]
/--
theorem `snd_intCast` / 定理 `snd_intCast`

English:
theorem snd_intCast
  given: [AddGroupWithOne R] [AddGroup M] (z : Int)
  statement: (z : tsze R M).snd = 0
  proof: rfl

@[simp]

中文:
定理 snd_intCast
  条件: [AddGroupWithOne R] [AddGroup M] (z : 整数)
  结论: (z : tsze R M).snd = 0
  证明: rfl

@[simp]
-/
theorem snd_intCast [AddGroupWithOne R] [AddGroup M] (z : Int) : (z : tsze R M).snd = 0 :=
  rfl

@[simp]
/--
theorem `inl_intCast` / 定理 `inl_intCast`

English:
theorem inl_intCast
  given: [AddGroupWithOne R] [AddGroup M] (z : Int)
  statement: (inl z : tsze R M) = z
  proof: rfl

中文:
定理 inl_intCast
  条件: [AddGroupWithOne R] [AddGroup M] (z : 整数)
  结论: (inl z : tsze R M) = z
  证明: rfl
-/
theorem inl_intCast [AddGroupWithOne R] [AddGroup M] (z : Int) : (inl z : tsze R M) = z :=
  rfl

/--
Instance `nonAssocSemiring` / 实例 `nonAssocSemiring`

English:
instance nonAssocSemiring
  signature: [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
  body: fun x =>
ext (zero_mul x.1)
      show (0 : R) •> x.2 + (0 : M) <• x.1 = 0 by rw [zero_smul, zero_add, smul_zero]
  mul_zero := fun x =>
ext (mul_zero x.1)
      show x.1 • (0 : M) + (0 : Rᵐᵒᵖ) • x.2 = 0 by rw [smul_zero, zero_add, zero_smul]
  left_distrib := fun x₁ x₂ x₃ =>
ext (mul_add x₁.1 x₂.1 

中文:
实例 nonAssocSemiring
  签名: [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
  定义体: fun x =>
ext (zero_mul x.1)
      show (0 : R) •> x.2 + (0 : M) <• x.1 = 0 by rw [zero_smul, zero_add, smul_zero]
  mul_zero := fun x =>
ext (mul_zero x.1)
      show x.1 • (0 : M) + (0 : Rᵐᵒᵖ) • x.2 = 0 by rw [smul_zero, zero_add, zero_smul]
  left_distrib := fun x₁ x₂ x₃ =>
ext (mul_add x₁.1 x₂.1 
-/
instance nonAssocSemiring [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] :
    NonAssocSemiring (tsze R M) where
  zero_mul := fun x =>
ext (zero_mul x.1)
      show (0 : R) •> x.2 + (0 : M) <• x.1 = 0 by rw [zero_smul, zero_add, smul_zero]
  mul_zero := fun x =>
ext (mul_zero x.1)
      show x.1 • (0 : M) + (0 : Rᵐᵒᵖ) • x.2 = 0 by rw [smul_zero, zero_add, zero_smul]
  left_distrib := fun x₁ x₂ x₃ =>
ext (mul_add x₁.1 x₂.1 x₃.1)
      show
        x₁.1 •> (x₂.2 + x₃.2) + x₁.2 <• (x₂.1 + x₃.1) =
          x₁.1 •> x₂.2 + x₁.2 <• x₂.1 + (x₁.1 •> x₃.2 + x₁.2 <• x₃.1)
        by simp_rw [smul_add, MulOpposite.op_add, add_smul, add_add_add_comm]
  right_distrib := fun x₁ x₂ x₃ =>
ext (add_mul x₁.1 x₂.1 x₃.1)
      show
        (x₁.1 + x₂.1) •> x₃.2 + (x₁.2 + x₂.2) <• x₃.1 =
          x₁.1 •> x₃.2 + x₁.2 <• x₃.1 + (x₂.1 •> x₃.2 + x₂.2 <• x₃.1)
        by simp_rw [add_smul, smul_add, add_add_add_comm]

/--
Instance `nonAssocRing` / 实例 `nonAssocRing`

English:
instance nonAssocRing
  signature: [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]

中文:
实例 nonAssocRing
  签名: [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
-/
instance nonAssocRing [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] :
    NonAssocRing (tsze R M) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] :
  body: ⟨fun x n =>
    ⟨x.fst ^ n, ((List.range n).map fun i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum⟩⟩

@[simp]

中文:
实例 [Monoid
  签名: R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] :
  定义体: ⟨fun x n =>
    ⟨x.fst ^ n, ((List.range n).map fun i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum⟩⟩

@[simp]

Depends on / 依赖: List.range, n.pred, x.fst, x.snd
-/
instance [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] :
    Pow (tsze R M) Nat :=
  ⟨fun x n =>
    ⟨x.fst ^ n, ((List.range n).map fun i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum⟩⟩

@[simp]
/--
theorem `fst_pow` / 定理 `fst_pow`

English:
theorem fst_pow
  statement: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  proof: rfl

中文:
定理 fst_pow
  结论: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  证明: rfl
-/
theorem fst_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (n : Nat) : fst (x ^ n) = x.fst ^ n :=
  rfl

/--
theorem `snd_pow_eq_sum` / 定理 `snd_pow_eq_sum`

English:
theorem snd_pow_eq_sum
  statement: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  proof: rfl

中文:
定理 snd_pow_eq_sum
  结论: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  证明: rfl

Depends on / 依赖: IsOpenImmersion, locallyOfFinitePresentation_of_isOpenImmersion
-/
theorem snd_pow_eq_sum [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (n : Nat) :
    snd (x ^ n) = ((List.range n).map fun i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum :=
  rfl

/--
theorem `snd_pow_of_smul_comm` / 定理 `snd_pow_of_smul_comm`

English:
theorem snd_pow_of_smul_comm
  statement: [Monoid R] [AddMonoid M] [DistribMulAction R M]
  proof: by
  simp_rw [snd_pow_eq_sum, ← smul_comm (_ : R) (_ : Rᵐᵒᵖ), aux, smul_smul, ← pow_add]
  match n with
  | 0 => rw [Nat.pred_zero, pow_zero, List.range_zero, zero_smul, List.map_nil, List.sum_nil]
  | (Nat.succ n) =>
    simp_rw [Nat.pred_succ]
    exact (List.sum_eq_card_nsmul _ (x.fst ^ n • x.snd

中文:
定理 snd_pow_of_smul_comm
  结论: [Monoid R] [AddMonoid M] [DistribMulAction R M]
  证明: by
  simp_rw [snd_pow_eq_sum, ← smul_comm (_ : R) (_ : Rᵐᵒᵖ), aux, smul_smul, ← pow_add]
  match n with
  | 0 => rw [Nat.pred_zero, pow_zero, List.range_zero, zero_smul, List.map_nil, List.sum_nil]
  | (Nat.succ n) =>
    simp_rw [Nat.pred_succ]
    exact (List.sum_eq_card_nsmul _ (x.fst ^ n • x.snd

Depends on / 依赖: List.length_map, List.length_range, List.map_nil, List.range_zero, List.sum_eq_card_nsmul, List.sum_nil, Nat.pred_succ, Nat.pred_zero, Nat.succ, length_map, length_range, map_nil, pow_add, pow_zero, pred_succ, pred_zero, range_zero, simp_rw, smul_comm, smul_smul
-/
theorem snd_pow_of_smul_comm [Monoid R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : Nat)
    (h : x.snd <• x.fst = x.fst •> x.snd) : snd (x ^ n) = n • x.fst ^ n.pred •> x.snd := by
  simp_rw [snd_pow_eq_sum, ← smul_comm (_ : R) (_ : Rᵐᵒᵖ), aux, smul_smul, ← pow_add]
  match n with
  | 0 => rw [Nat.pred_zero, pow_zero, List.range_zero, zero_smul, List.map_nil, List.sum_nil]
  | (Nat.succ n) =>
    simp_rw [Nat.pred_succ]
    exact (List.sum_eq_card_nsmul _ (x.fst ^ n • x.snd) (by grind)).trans
      (by rw [List.length_map, List.length_range])
where
  aux : forall n : Nat, x.snd <• x.fst ^ n = x.fst ^ n •> x.snd := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]; rw [op_mul]; rw [mul_smul]; rw [mul_smul]; rw [← h]; rw [smul_comm (_ : R) (op x.fst) x.snd]; rw [ih]

/--
theorem `snd_pow_of_smul_comm'` / 定理 `snd_pow_of_smul_comm'`

English:
theorem snd_pow_of_smul_comm'
  statement: [Monoid R] [AddMonoid M] [DistribMulAction R M]
  proof: by
  rw [snd_pow_of_smul_comm _ _ h]; rw [snd_pow_of_smul_comm.aux _ h]

@[simp]

中文:
定理 snd_pow_of_smul_comm'
  结论: [Monoid R] [AddMonoid M] [DistribMulAction R M]
  证明: by
  rw [snd_pow_of_smul_comm _ _ h]; rw [snd_pow_of_smul_comm.aux _ h]

@[simp]

Depends on / 依赖: snd_pow_of_smul_comm, snd_pow_of_smul_comm.aux
-/
theorem snd_pow_of_smul_comm' [Monoid R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : Nat)
    (h : x.snd <• x.fst = x.fst •> x.snd) : snd (x ^ n) = n • (x.snd <• x.fst ^ n.pred) := by
  rw [snd_pow_of_smul_comm _ _ h]; rw [snd_pow_of_smul_comm.aux _ h]

@[simp]
/--
theorem `snd_pow` / 定理 `snd_pow`

English:
theorem snd_pow
  statement: [CommMonoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  proof: snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _)

@[simp]

中文:
定理 snd_pow
  结论: [CommMonoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  证明: snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _)

@[simp]

Depends on / 依赖: op_smul_eq_smul, snd_pow_of_smul_comm
-/
theorem snd_pow [CommMonoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [IsCentralScalar R M] (x : tsze R M) (n : Nat) : snd (x ^ n) = n • x.fst ^ n.pred • x.snd :=
  snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _)

@[simp]
/--
theorem `inl_pow` / 定理 `inl_pow`

English:
theorem inl_pow
  statement: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (r : R)
  proof: ext rfl by simp [snd_pow_eq_sum, List.map_const']

中文:
定理 inl_pow
  结论: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (r : R)
  证明: ext rfl by simp [snd_pow_eq_sum, List.map_const']

Depends on / 依赖: List.map_const, map_const, snd_pow_eq_sum
-/
theorem inl_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (r : R)
    (n : Nat) : (inl r ^ n : tsze R M) = inl (r ^ n) :=
ext rfl by simp [snd_pow_eq_sum, List.map_const']

/--
Instance `monoid` / 实例 `monoid`

English:
instance monoid
  signature: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  body: fun x y z =>
ext (mul_assoc x.1 y.1 z.1)
      show
        (x.1 * y.1) •> z.2 + (x.1 •> y.2 + x.2 <• y.1) <• z.1 =
          x.1 •> (y.1 •> z.2 + y.2 <• z.1) + x.2 <• (y.1 * z.1)
        by simp_rw [smul_add, ← mul_smul, add_assoc, smul_comm, op_mul]
  npow := fun n x => x ^ n
  npow_zero := fun x 

中文:
实例 monoid
  签名: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  定义体: fun x y z =>
ext (mul_assoc x.1 y.1 z.1)
      show
        (x.1 * y.1) •> z.2 + (x.1 •> y.2 + x.2 <• y.1) <• z.1 =
          x.1 •> (y.1 •> z.2 + y.2 <• z.1) + x.2 <• (y.1 * z.1)
        by simp_rw [smul_add, ← mul_smul, add_assoc, smul_comm, op_mul]
  npow := fun n x => x ^ n
  npow_zero := fun x 
-/
instance monoid [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] : Monoid (tsze R M) where
  mul_assoc := fun x y z =>
ext (mul_assoc x.1 y.1 z.1)
      show
        (x.1 * y.1) •> z.2 + (x.1 •> y.2 + x.2 <• y.1) <• z.1 =
          x.1 •> (y.1 •> z.2 + y.2 <• z.1) + x.2 <• (y.1 * z.1)
        by simp_rw [smul_add, ← mul_smul, add_assoc, smul_comm, op_mul]
  npow := fun n x => x ^ n
  npow_zero := fun x => ext (pow_zero x.fst) (by simp [snd_pow_eq_sum])
  npow_succ := fun n x =>
    ext (pow_succ _ _)
      (by
        simp_rw [snd_mul, snd_pow_eq_sum, Nat.pred_succ]
        cases n
        · simp [List.range_succ]
        rw [List.sum_range_succ']
        simp only [pow_zero, op_one, Nat.sub_zero, one_smul, Nat.succ_sub_succ_eq_sub, fst_pow,
          Nat.pred_succ, List.smul_sum, List.map_map, Function.comp_def]
        simp_rw [← smul_comm (_ : R) (_ : Rᵐᵒᵖ), smul_smul, pow_succ]
        rfl)

/--
theorem `fst_list_prod` / 定理 `fst_list_prod`

English:
theorem fst_list_prod
  statement: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  proof: map_list_prod ({ toFun := fst, map_one' := fst_one, map_mul' := fst_mul } : tsze R M ->* R) _

中文:
定理 fst_list_prod
  结论: [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  证明: map_list_prod ({ toFun := fst, map_one' := fst_one, map_mul' := fst_mul } : tsze R M ->* R) _

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, fst_mul, fst_one, map_list_prod, map_mul, map_one, pullback_fst
-/
theorem fst_list_prod [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) : l.prod.fst = (l.map fst).prod :=
  map_list_prod ({ toFun := fst, map_one' := fst_one, map_mul' := fst_mul } : tsze R M ->* R) _

/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: [Semiring R] [AddCommMonoid M]

中文:
实例 semiring
  签名: [Semiring R] [AddCommMonoid M]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
instance semiring [Semiring R] [AddCommMonoid M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] : Semiring (tsze R M) where

/--
theorem `snd_list_prod` / 定理 `snd_list_prod`

English:
theorem snd_list_prod
  statement: [Monoid R] [AddCommMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  proof: by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.zipIdx_cons']
    simp_rw [List.map_cons, List.map_map, Function.comp_def, Prod.map_snd, Prod.map_fst, id,
      List.take_zero, List.take_succ_cons, List.prod_nil, List.prod_cons, snd_mul, one_smul,
      List.drop, mul_smul, Li

中文:
定理 snd_list_prod
  结论: [Monoid R] [AddCommMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
  证明: by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.zipIdx_cons']
    simp_rw [List.map_cons, List.map_map, Function.comp_def, Prod.map_snd, Prod.map_fst, id,
      List.take_zero, List.take_succ_cons, List.prod_nil, List.prod_cons, snd_mul, one_smul,
      List.drop, mul_smul, Li

Depends on / 依赖: Function, Function.comp_def, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, List.drop, List.map_cons, List.map_map, List.prod_cons, List.prod_nil, List.smul_sum, List.sum_cons, List.take_succ_cons, List.take_zero, List.zipIdx_cons, Prod.map_fst, Prod.map_snd, add_comm, comp_def, fst_list_prod, map_cons
-/
theorem snd_list_prod [Monoid R] [AddCommMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) :
    l.prod.snd =
      (l.zipIdx.map fun x : tsze R M × Nat =>
          ((l.map fst).take x.2).prod •> x.fst.snd <• ((l.map fst).drop x.2.succ).prod).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.zipIdx_cons']
    simp_rw [List.map_cons, List.map_map, Function.comp_def, Prod.map_snd, Prod.map_fst, id,
      List.take_zero, List.take_succ_cons, List.prod_nil, List.prod_cons, snd_mul, one_smul,
      List.drop, mul_smul, List.sum_cons, fst_list_prod, ih, List.smul_sum, List.map_map,
      ← smul_comm (_ : R) (_ : Rᵐᵒᵖ)]
    exact add_comm _ _

/--
Instance `ring` / 实例 `ring`

English:
instance ring
  signature: [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

中文:
实例 ring
  签名: [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

Depends on / 依赖: Scheme, Scheme.Hom.resLE, infer_instance
-/
instance ring [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] :
    Ring (tsze R M) where

/--
Instance `commMonoid` / 实例 `commMonoid`

English:
instance commMonoid
  signature: [CommMonoid R] [AddCommMonoid M] [DistribMulAction R M]
  body: { TrivSqZeroExt.monoid with
    mul_comm := fun x₁ x₂ =>
ext (mul_comm x₁.1 x₂.1)
        show x₁.1 •> x₂.2 + x₁.2 <• x₂.1 = x₂.1 •> x₁.2 + x₂.2 <• x₁.1 by
          rw [op_smul_eq_smul]; rw [op_smul_eq_smul]; rw [add_comm] }

中文:
实例 commMonoid
  签名: [CommMonoid R] [AddCommMonoid M] [DistribMulAction R M]
  定义体: { TrivSqZeroExt.monoid with
    mul_comm := fun x₁ x₂ =>
ext (mul_comm x₁.1 x₂.1)
        show x₁.1 •> x₂.2 + x₁.2 <• x₂.1 = x₂.1 •> x₁.2 + x₂.2 <• x₁.1 by
          rw [op_smul_eq_smul]; rw [op_smul_eq_smul]; rw [add_comm] }

Depends on / 依赖: FiniteType, HasRingHomProperty, HasRingHomProperty.eq_affineLocally, LocallyOfFinitePresentation, LocallyOfFiniteType, RingHom, RingHom.FiniteType.of_finitePresentation, TrivSqZeroExt, TrivSqZeroExt.monoid, add_comm, affineLocally_le, eq_affineLocally, monoid, mul_comm, of_finitePresentation, op_smul_eq_smul
-/
instance commMonoid [CommMonoid R] [AddCommMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [IsCentralScalar R M] : CommMonoid (tsze R M) :=
  { TrivSqZeroExt.monoid with
    mul_comm := fun x₁ x₂ =>
ext (mul_comm x₁.1 x₂.1)
        show x₁.1 •> x₂.2 + x₁.2 <• x₂.1 = x₂.1 •> x₁.2 + x₂.2 <• x₁.1 by
          rw [op_smul_eq_smul]; rw [op_smul_eq_smul]; rw [add_comm] }

/--
Instance `commSemiring` / 实例 `commSemiring`

English:
instance commSemiring
  signature: [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]

中文:
实例 commSemiring
  签名: [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
-/
instance commSemiring [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] : CommSemiring (tsze R M) where

/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

中文:
实例 commRing
  签名: [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
-/
instance commRing [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    CommRing (tsze R M) where

variable (R M)

/-- The canonical inclusion of rings `R → TrivSqZeroExt R M`. -/
@[simps apply]
/--
Definition of `inlHom` / `inlHom` 的定义

English:
definition inlHom
  signature: [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
  body: inl
  map_one' := inl_one M
  map_mul' := inl_mul M
  map_zero' := inl_zero M
  map_add' := inl_add M

中文:
定义 inlHom
  签名: [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
  定义体: inl
  map_one' := inl_one M
  map_mul' := inl_mul M
  map_zero' := inl_zero M
  map_add' := inl_add M
-/
def inlHom [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] : R ->+* tsze R M where
  toFun := inl
  map_one' := inl_one M
  map_mul' := inl_mul M
  map_zero' := inl_zero M
  map_add' := inl_add M

end Mul

section Inv
variable {R : Type u} {M : Type v}
variable [Neg M] [Inv R] [SMul Rᵐᵒᵖ M] [SMul R M]

/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: : Inv (tsze R M)
  body: ⟨fun b => (b.1⁻¹, -(b.1⁻¹ •> b.2 <• b.1⁻¹))⟩

中文:
实例 instInv
  签名: : Inv (tsze R M)
  定义体: ⟨fun b => (b.1⁻¹, -(b.1⁻¹ •> b.2 <• b.1⁻¹))⟩
-/
instance instInv : Inv (tsze R M) :=
  ⟨fun b => (b.1⁻¹, -(b.1⁻¹ •> b.2 <• b.1⁻¹))⟩

/--
theorem `fst_inv` / 定理 `fst_inv`

English:
theorem fst_inv
  given: (x : tsze R M)
  statement: fst x⁻¹ = (fst x)⁻¹
  proof: rfl

中文:
定理 fst_inv
  条件: (x : tsze R M)
  结论: fst x⁻¹ = (fst x)⁻¹
  证明: rfl

Depends on / 依赖: IsOpenImmersion, locallyOfFiniteType_of_isOpenImmersion
-/
@[simp] theorem fst_inv (x : tsze R M) : fst x⁻¹ = (fst x)⁻¹ :=
  rfl

/--
theorem `snd_inv` / 定理 `snd_inv`

English:
theorem snd_inv
  given: (x : tsze R M)
  statement: snd x⁻¹ = -((fst x)⁻¹ •> snd x <• (fst x)⁻¹)
  proof: rfl

中文:
定理 snd_inv
  条件: (x : tsze R M)
  结论: snd x⁻¹ = -((fst x)⁻¹ •> snd x <• (fst x)⁻¹)
  证明: rfl
-/
@[simp] theorem snd_inv (x : tsze R M) : snd x⁻¹ = -((fst x)⁻¹ •> snd x <• (fst x)⁻¹) :=
  rfl

end Inv

/-! This section is heavily inspired by analogous results about matrices. -/
section Invertible
variable {R : Type u} {M : Type v}
variable [AddCommGroup M] [Semiring R] [Module Rᵐᵒᵖ M] [Module R M]

/--
Definition of `invertibleFstOfInvertible` / `invertibleFstOfInvertible` 的定义

English:
abbreviation invertibleFstOfInvertible
  signature: (x : tsze R M) [Invertible x]
  body: (⅟x).fst
  invOf_mul_self := by rw [← fst_mul, invOf_mul_self, fst_one]
  mul_invOf_self := by rw [← fst_mul, mul_invOf_self, fst_one]

中文:
缩写 invertibleFstOfInvertible
  签名: (x : tsze R M) [Invertible x]
  定义体: (⅟x).fst
  invOf_mul_self := by rw [← fst_mul, invOf_mul_self, fst_one]
  mul_invOf_self := by rw [← fst_mul, mul_invOf_self, fst_one]
-/
abbrev invertibleFstOfInvertible (x : tsze R M) [Invertible x] : Invertible x.fst where
  invOf := (⅟x).fst
  invOf_mul_self := by rw [← fst_mul, invOf_mul_self, fst_one]
  mul_invOf_self := by rw [← fst_mul, mul_invOf_self, fst_one]

/--
theorem `fst_invOf` / 定理 `fst_invOf`

English:
theorem fst_invOf
  given: (x : tsze R M) [Invertible x] [Invertible x.fst]
  statement: (⅟x).fst = ⅟(x.fst)
  proof: by
  let := invertibleFstOfInvertible x
  convert! (rfl : _ = ⅟x.fst)

中文:
定理 fst_invOf
  条件: (x : tsze R M) [Invertible x] [Invertible x.fst]
  结论: (⅟x).fst = ⅟(x.fst)
  证明: by
  let := invertibleFstOfInvertible x
  convert! (rfl : _ = ⅟x.fst)

Depends on / 依赖: convert, invertibleFstOfInvertible, x.fst
-/
theorem fst_invOf (x : tsze R M) [Invertible x] [Invertible x.fst] : (⅟x).fst = ⅟(x.fst) := by
  let := invertibleFstOfInvertible x
  convert! (rfl : _ = ⅟x.fst)

/--
theorem `mul_left_eq_one` / 定理 `mul_left_eq_one`

English:
theorem mul_left_eq_one
  given: (r : R) (x : tsze R M) (h : r * x.fst = 1)
  proof: by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, op_smul_op_smul, h, op_one, one_smul,
      add_neg_cancel]

中文:
定理 mul_left_eq_one
  条件: (r : R) (x : tsze R M) (h : r * x.fst = 1)
  证明: by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, op_smul_op_smul, h, op_one, one_smul,
      add_neg_cancel]

Depends on / 依赖: add_neg_cancel, add_zero, one_smul, op_one, op_smul_op_smul, smul_neg, zero_add
-/
theorem mul_left_eq_one (r : R) (x : tsze R M) (h : r * x.fst = 1) :
    (inl r + inr (-((r •> x.snd) <• r))) * x = 1 := by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, op_smul_op_smul, h, op_one, one_smul,
      add_neg_cancel]

/--
theorem `mul_right_eq_one` / 定理 `mul_right_eq_one`

English:
theorem mul_right_eq_one
  given: (x : tsze R M) (r : R) (h : x.fst * r = 1)
  proof: by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, smul_smul, h, one_smul, neg_add_cancel]

中文:
定理 mul_right_eq_one
  条件: (x : tsze R M) (r : R) (h : x.fst * r = 1)
  证明: by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, smul_smul, h, one_smul, neg_add_cancel]

Depends on / 依赖: add_zero, neg_add_cancel, one_smul, smul_neg, smul_smul, zero_add
-/
theorem mul_right_eq_one (x : tsze R M) (r : R) (h : x.fst * r = 1) :
    x * (inl r + inr (-(r •> (x.snd <• r)))) = 1 := by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, smul_smul, h, one_smul, neg_add_cancel]

variable [SMulCommClass R Rᵐᵒᵖ M]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `invertibleOfInvertibleFst` / `invertibleOfInvertibleFst` 的定义

English:
abbreviation invertibleOfInvertibleFst
  signature: (x : tsze R M) [Invertible x.fst]
  body: (⅟x.fst, -(⅟x.fst •> x.snd <• ⅟x.fst))
  invOf_mul_self := by
    convert! mul_left_eq_one _ _ (invOf_mul_self x.fst)
    ext <;> simp
  mul_invOf_self := by
    convert! mul_right_eq_one _ _ (mul_invOf_self x.fst)
    ext <;> simp [smul_comm]

中文:
缩写 invertibleOfInvertibleFst
  签名: (x : tsze R M) [Invertible x.fst]
  定义体: (⅟x.fst, -(⅟x.fst •> x.snd <• ⅟x.fst))
  invOf_mul_self := by
    convert! mul_left_eq_one _ _ (invOf_mul_self x.fst)
    ext <;> simp
  mul_invOf_self := by
    convert! mul_right_eq_one _ _ (mul_invOf_self x.fst)
    ext <;> simp [smul_comm]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst, x.fst, x.snd
-/
abbrev invertibleOfInvertibleFst (x : tsze R M) [Invertible x.fst] : Invertible x where
  invOf := (⅟x.fst, -(⅟x.fst •> x.snd <• ⅟x.fst))
  invOf_mul_self := by
    convert! mul_left_eq_one _ _ (invOf_mul_self x.fst)
    ext <;> simp
  mul_invOf_self := by
    convert! mul_right_eq_one _ _ (mul_invOf_self x.fst)
    ext <;> simp [smul_comm]

/--
theorem `snd_invOf` / 定理 `snd_invOf`

English:
theorem snd_invOf
  given: (x : tsze R M) [Invertible x] [Invertible x.fst]
  proof: by
  let := invertibleOfInvertibleFst x
  convert! congr_arg (TrivSqZeroExt.snd (R := R) (M := M)) (_ : _ = ⅟x)
  convert! rfl

中文:
定理 snd_invOf
  条件: (x : tsze R M) [Invertible x] [Invertible x.fst]
  证明: by
  let := invertibleOfInvertibleFst x
  convert! congr_arg (TrivSqZeroExt.snd (R := R) (M := M)) (_ : _ = ⅟x)
  convert! rfl

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, TrivSqZeroExt, TrivSqZeroExt.snd, congr_arg, convert, invertibleOfInvertibleFst, pullback_snd
-/
theorem snd_invOf (x : tsze R M) [Invertible x] [Invertible x.fst] :
    (⅟x).snd = -(⅟x.fst •> x.snd <• ⅟x.fst) := by
  let := invertibleOfInvertibleFst x
  convert! congr_arg (TrivSqZeroExt.snd (R := R) (M := M)) (_ : _ = ⅟x)
  convert! rfl

/-- Together `TrivSqZeroExt.detInvertibleOfInvertible` and `TrivSqZeroExt.invertibleOfDetInvertible`
form an equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
/--
Definition of `invertibleEquivInvertibleFst` / `invertibleEquivInvertibleFst` 的定义

English:
definition invertibleEquivInvertibleFst
  signature: (x : tsze R M)
  body: invertibleFstOfInvertible x
  invFun _ := invertibleOfInvertibleFst x
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 invertibleEquivInvertibleFst
  签名: (x : tsze R M)
  定义体: invertibleFstOfInvertible x
  invFun _ := invertibleOfInvertibleFst x
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, invertibleFstOfInvertible, restrict
-/
def invertibleEquivInvertibleFst (x : tsze R M) : Invertible x ≃ Invertible x.fst where
  toFun _ := invertibleFstOfInvertible x
  invFun _ := invertibleOfInvertibleFst x
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/--
theorem `isUnit_iff_isUnit_fst` / 定理 `isUnit_iff_isUnit_fst`

English:
theorem isUnit_iff_isUnit_fst
  given: {x : tsze R M}
  statement: IsUnit x ↔ IsUnit x.fst
  proof: by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivInvertibleFst x).nonempty_congr]

@[simp]

中文:
定理 isUnit_iff_isUnit_fst
  条件: {x : tsze R M}
  结论: IsUnit x ↔ IsUnit x.fst
  证明: by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivInvertibleFst x).nonempty_congr]

@[simp]

Depends on / 依赖: Scheme, Scheme.Hom.resLE, infer_instance, invertibleEquivInvertibleFst, nonempty_congr, nonempty_invertible_iff_isUnit
-/
theorem isUnit_iff_isUnit_fst {x : tsze R M} : IsUnit x ↔ IsUnit x.fst := by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivInvertibleFst x).nonempty_congr]

@[simp]
/--
theorem `isUnit_inl_iff` / 定理 `isUnit_inl_iff`

English:
theorem isUnit_inl_iff
  given: {r : R}
  statement: IsUnit (inl r : tsze R M) ↔ IsUnit r
  proof: by
  rw [isUnit_iff_isUnit_fst]; rw [fst_inl]

@[simp]

中文:
定理 isUnit_inl_iff
  条件: {r : R}
  结论: IsUnit (inl r : tsze R M) ↔ IsUnit r
  证明: by
  rw [isUnit_iff_isUnit_fst]; rw [fst_inl]

@[simp]

Depends on / 依赖: fst_inl, isUnit_iff_isUnit_fst
-/
theorem isUnit_inl_iff {r : R} : IsUnit (inl r : tsze R M) ↔ IsUnit r := by
  rw [isUnit_iff_isUnit_fst]; rw [fst_inl]

@[simp]
/--
theorem `isUnit_inr_iff` / 定理 `isUnit_inr_iff`

English:
theorem isUnit_inr_iff
  given: {m : M}
  statement: IsUnit (inr m : tsze R M) ↔ Subsingleton R
  proof: by
  simp_rw [isUnit_iff_isUnit_fst, fst_inr, isUnit_zero_iff, subsingleton_iff_zero_eq_one]

中文:
定理 isUnit_inr_iff
  条件: {m : M}
  结论: IsUnit (inr m : tsze R M) ↔ Subsingleton R
  证明: by
  simp_rw [isUnit_iff_isUnit_fst, fst_inr, isUnit_zero_iff, subsingleton_iff_zero_eq_one]

Depends on / 依赖: JacobsonSpace, PrimeSpectrum, fst_inr, isUnit_iff_isUnit_fst, isUnit_zero_iff, simp_rw, subsingleton_iff_zero_eq_one
-/
theorem isUnit_inr_iff {m : M} : IsUnit (inr m : tsze R M) ↔ Subsingleton R := by
  simp_rw [isUnit_iff_isUnit_fst, fst_inr, isUnit_zero_iff, subsingleton_iff_zero_eq_one]

end Invertible

section DivisionSemiring
variable {R : Type u} {M : Type v}
variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

/--
theorem `inv_inl` / 定理 `inv_inl`

English:
theorem inv_inl
  given: (r : R)
  proof: by
  ext
  · rw [fst_inv, fst_inl, fst_inl]
  · rw [snd_inv, fst_inl, snd_inl, snd_inl, smul_zero, smul_zero, neg_zero]

@[simp]

中文:
定理 inv_inl
  条件: (r : R)
  证明: by
  ext
  · rw [fst_inv, fst_inl, fst_inl]
  · rw [snd_inv, fst_inl, snd_inl, snd_inl, smul_zero, smul_zero, neg_zero]

@[simp]

Depends on / 依赖: JacobsonSpace, PrimeSpectrum
-/
protected theorem inv_inl (r : R) :
    (inl r)⁻¹ = (inl (r⁻¹ : R) : tsze R M) := by
  ext
  · rw [fst_inv, fst_inl, fst_inl]
  · rw [snd_inv, fst_inl, snd_inl, snd_inl, smul_zero, smul_zero, neg_zero]

@[simp]
/--
theorem `inv_inr` / 定理 `inv_inr`

English:
theorem inv_inr
  given: (m : M)
  statement: (inr m)⁻¹ = (0 : tsze R M)
  proof: by
  ext
  · rw [fst_inv, fst_inr, fst_zero, inv_zero]
  · rw [snd_inv, snd_inr, fst_inr, inv_zero, op_zero, zero_smul, snd_zero, neg_zero]

@[simp]

中文:
定理 inv_inr
  条件: (m : M)
  结论: (inr m)⁻¹ = (0 : tsze R M)
  证明: by
  ext
  · rw [fst_inv, fst_inr, fst_zero, inv_zero]
  · rw [snd_inv, snd_inr, fst_inr, inv_zero, op_zero, zero_smul, snd_zero, neg_zero]

@[simp]

Depends on / 依赖: fst_inr, fst_inv, fst_zero, inv_zero, neg_zero, op_zero, snd_inr, snd_inv, snd_zero, zero_smul
-/
theorem inv_inr (m : M) : (inr m)⁻¹ = (0 : tsze R M) := by
  ext
  · rw [fst_inv, fst_inr, fst_zero, inv_zero]
  · rw [snd_inv, snd_inr, fst_inr, inv_zero, op_zero, zero_smul, snd_zero, neg_zero]

@[simp]
/--
theorem `inv_zero` / 定理 `inv_zero`

English:
theorem inv_zero
  statement: (0 : tsze R M)⁻¹ = (0 : tsze R M)
  proof: by
  rw [← inl_zero]; rw [TrivSqZeroExt.inv_inl]; rw [inv_zero]

@[simp]

中文:
定理 inv_zero
  结论: (0 : tsze R M)⁻¹ = (0 : tsze R M)
  证明: by
  rw [← inl_zero]; rw [TrivSqZeroExt.inv_inl]; rw [inv_zero]

@[simp]
-/
protected theorem inv_zero : (0 : tsze R M)⁻¹ = (0 : tsze R M) := by
  rw [← inl_zero]; rw [TrivSqZeroExt.inv_inl]; rw [inv_zero]

@[simp]
/--
theorem `inv_one` / 定理 `inv_one`

English:
theorem inv_one
  statement: (1 : tsze R M)⁻¹ = (1 : tsze R M)
  proof: by
  rw [← inl_one]; rw [TrivSqZeroExt.inv_inl]; rw [inv_one]

中文:
定理 inv_one
  结论: (1 : tsze R M)⁻¹ = (1 : tsze R M)
  证明: by
  rw [← inl_one]; rw [TrivSqZeroExt.inv_inl]; rw [inv_one]
-/
protected theorem inv_one : (1 : tsze R M)⁻¹ = (1 : tsze R M) := by
  rw [← inl_one]; rw [TrivSqZeroExt.inv_inl]; rw [inv_one]

/--
theorem `inv_mul_cancel` / 定理 `inv_mul_cancel`

English:
theorem inv_mul_cancel
  given: {x : tsze R M} (hx : fst x != 0)
  statement: x⁻¹ * x = 1
  proof: by
  convert mul_left_eq_one _ _ (_root_.inv_mul_cancel₀ hx)
  ext <;> simp

中文:
定理 inv_mul_cancel
  条件: {x : tsze R M} (hx : fst x != 0)
  结论: x⁻¹ * x = 1
  证明: by
  convert mul_left_eq_one _ _ (_root_.inv_mul_cancel₀ hx)
  ext <;> simp

Depends on / 依赖: IsOpenImmersion
-/
protected theorem inv_mul_cancel {x : tsze R M} (hx : fst x != 0) : x⁻¹ * x = 1 := by
  convert mul_left_eq_one _ _ (_root_.inv_mul_cancel₀ hx)
  ext <;> simp

variable [SMulCommClass R Rᵐᵒᵖ M]

/--
theorem `invOf_eq_inv` / 定理 `invOf_eq_inv`

English:
theorem invOf_eq_inv
  given: (x : tsze R M) [Invertible x]
  statement: ⅟x = x⁻¹
  proof: by
  let := invertibleFstOfInvertible x
  ext <;> simp [fst_invOf, snd_invOf]

中文:
定理 invOf_eq_inv
  条件: (x : tsze R M) [Invertible x]
  结论: ⅟x = x⁻¹
  证明: by
  let := invertibleFstOfInvertible x
  ext <;> simp [fst_invOf, snd_invOf]
-/
@[simp] theorem invOf_eq_inv (x : tsze R M) [Invertible x] : ⅟x = x⁻¹ := by
  let := invertibleFstOfInvertible x
  ext <;> simp [fst_invOf, snd_invOf]

/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: {x : tsze R M} (hx : fst x != 0)
  statement: x * x⁻¹ = 1
  proof: by
  have : Invertible x.fst := Units.invertible (.mk0 _ hx)
  have := invertibleOfInvertibleFst x
  rw [← invOf_eq_inv]; rw [mul_invOf_self]

中文:
定理 mul_inv_cancel
  条件: {x : tsze R M} (hx : fst x != 0)
  结论: x * x⁻¹ = 1
  证明: by
  have : Invertible x.fst := Units.invertible (.mk0 _ hx)
  have := invertibleOfInvertibleFst x
  rw [← invOf_eq_inv]; rw [mul_invOf_self]
-/
protected theorem mul_inv_cancel {x : tsze R M} (hx : fst x != 0) : x * x⁻¹ = 1 := by
  have : Invertible x.fst := Units.invertible (.mk0 _ hx)
  have := invertibleOfInvertibleFst x
  rw [← invOf_eq_inv]; rw [mul_invOf_self]

/--
theorem `mul_inv_rev` / 定理 `mul_inv_rev`

English:
theorem mul_inv_rev
  given: (a b : tsze R M)
  proof: by
  ext
  · rw [fst_inv, fst_mul, fst_mul, mul_inv_rev, fst_inv, fst_inv]
  · simp only [snd_inv, snd_mul, fst_mul, fst_inv]
    simp only [smul_neg, smul_add]
    simp_rw [mul_inv_rev, smul_comm (_ : R), op_smul_op_smul, smul_smul, add_comm, neg_add]
    obtain ha0 | ha := eq_or_ne (fst a) 0
    ·

中文:
定理 mul_inv_rev
  条件: (a b : tsze R M)
  证明: by
  ext
  · rw [fst_inv, fst_mul, fst_mul, mul_inv_rev, fst_inv, fst_inv]
  · simp only [snd_inv, snd_mul, fst_mul, fst_inv]
    simp only [smul_neg, smul_add]
    simp_rw [mul_inv_rev, smul_comm (_ : R), op_smul_op_smul, smul_smul, add_comm, neg_add]
    obtain ha0 | ha := eq_or_ne (fst a) 0
    ·
-/
protected theorem mul_inv_rev (a b : tsze R M) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  ext
  · rw [fst_inv, fst_mul, fst_mul, mul_inv_rev, fst_inv, fst_inv]
  · simp only [snd_inv, snd_mul, fst_mul, fst_inv]
    simp only [smul_neg, smul_add]
    simp_rw [mul_inv_rev, smul_comm (_ : R), op_smul_op_smul, smul_smul, add_comm, neg_add]
    obtain ha0 | ha := eq_or_ne (fst a) 0
    · simp [ha0]
    obtain hb0 | hb := eq_or_ne (fst b) 0
    · simp [hb0]
    rw [inv_mul_cancel_right₀ ha]; rw [mul_inv_cancel_left₀ hb]

/--
theorem `inv_inv` / 定理 `inv_inv`

English:
theorem inv_inv
  given: {x : tsze R M} (hx : fst x != 0)
  statement: x⁻¹⁻¹ = x
  proof: -- adapted from `Matrix.nonsing_inv_nonsing_inv`
  calc
    x⁻¹⁻¹ = 1 * x⁻¹⁻¹ := by rw [one_mul]
    _ = x * x⁻¹ * x⁻¹⁻¹ := by rw [TrivSqZeroExt.mul_inv_cancel hx]
    _ = x := by
      rw [mul_assoc]; rw [TrivSqZeroExt.mul_inv_cancel]; rw [mul_one]
      rw [fst_inv]
      apply inv_ne_zero hx

@[s

中文:
定理 inv_inv
  条件: {x : tsze R M} (hx : fst x != 0)
  结论: x⁻¹⁻¹ = x
  证明: -- adapted from `Matrix.nonsing_inv_nonsing_inv`
  calc
    x⁻¹⁻¹ = 1 * x⁻¹⁻¹ := by rw [one_mul]
    _ = x * x⁻¹ * x⁻¹⁻¹ := by rw [TrivSqZeroExt.mul_inv_cancel hx]
    _ = x := by
      rw [mul_assoc]; rw [TrivSqZeroExt.mul_inv_cancel]; rw [mul_one]
      rw [fst_inv]
      apply inv_ne_zero hx

@[s
-/
protected theorem inv_inv {x : tsze R M} (hx : fst x != 0) : x⁻¹⁻¹ = x :=
  -- adapted from `Matrix.nonsing_inv_nonsing_inv`
  calc
    x⁻¹⁻¹ = 1 * x⁻¹⁻¹ := by rw [one_mul]
    _ = x * x⁻¹ * x⁻¹⁻¹ := by rw [TrivSqZeroExt.mul_inv_cancel hx]
    _ = x := by
      rw [mul_assoc]; rw [TrivSqZeroExt.mul_inv_cancel]; rw [mul_one]
      rw [fst_inv]
      apply inv_ne_zero hx

@[simp]
/--
theorem `isUnit_inv_iff` / 定理 `isUnit_inv_iff`

English:
theorem isUnit_inv_iff
  given: {x : tsze R M}
  statement: IsUnit x⁻¹ ↔ IsUnit x
  proof: by
  simp_rw [isUnit_iff_isUnit_fst, fst_inv, isUnit_iff_ne_zero, ne_eq, inv_eq_zero]

中文:
定理 isUnit_inv_iff
  条件: {x : tsze R M}
  结论: IsUnit x⁻¹ ↔ IsUnit x
  证明: by
  simp_rw [isUnit_iff_isUnit_fst, fst_inv, isUnit_iff_ne_zero, ne_eq, inv_eq_zero]

Depends on / 依赖: fst_inv, inv_eq_zero, isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, ne_eq, simp_rw
-/
theorem isUnit_inv_iff {x : tsze R M} : IsUnit x⁻¹ ↔ IsUnit x := by
  simp_rw [isUnit_iff_isUnit_fst, fst_inv, isUnit_iff_ne_zero, ne_eq, inv_eq_zero]

end DivisionSemiring

section DivisionRing
variable {R : Type u} {M : Type v}
variable [DivisionRing R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

/--
theorem `inv_neg` / 定理 `inv_neg`

English:
theorem inv_neg
  given: {x : tsze R M}
  statement: (-x)⁻¹ = -(x⁻¹)
  proof: by
  ext <;> simp [inv_neg]

中文:
定理 inv_neg
  条件: {x : tsze R M}
  结论: (-x)⁻¹ = -(x⁻¹)
  证明: by
  ext <;> simp [inv_neg]
-/
protected theorem inv_neg {x : tsze R M} : (-x)⁻¹ = -(x⁻¹) := by
  ext <;> simp [inv_neg]

end DivisionRing

section Algebra

variable (S : Type*) (R R' : Type u) (M : Type v)
variable [CommSemiring S] [Semiring R] [CommSemiring R'] [AddCommMonoid M]
variable [Algebra S R] [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
variable [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]
variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]

/--
Instance `algebra'` / 实例 `algebra'`

English:
instance algebra'
  signature: : Algebra S (tsze R M) where
  body: (TrivSqZeroExt.inlHom R M).comp (algebraMap S R)
  commutes' := fun s x =>
ext (Algebra.commutes _ _)
      show algebraMap S R s •> x.snd + (0 : M) <• x.fst
          = x.fst •> (0 : M) + x.snd <• algebraMap S R s by
        rw [smul_zero]; rw [smul_zero]; rw [add_zero]; rw [zero_add]
        rw [A

中文:
实例 algebra'
  签名: : Algebra S (tsze R M) where
  定义体: (TrivSqZeroExt.inlHom R M).comp (algebraMap S R)
  commutes' := fun s x =>
ext (Algebra.commutes _ _)
      show algebraMap S R s •> x.snd + (0 : M) <• x.fst
          = x.fst •> (0 : M) + x.snd <• algebraMap S R s by
        rw [smul_zero]; rw [smul_zero]; rw [add_zero]; rw [zero_add]
        rw [A

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, TrivSqZeroExt, TrivSqZeroExt.inlHom, algebraMap, inlHom, pullback_fst
-/
instance algebra' : Algebra S (tsze R M) where
  algebraMap := (TrivSqZeroExt.inlHom R M).comp (algebraMap S R)
  commutes' := fun s x =>
ext (Algebra.commutes _ _)
      show algebraMap S R s •> x.snd + (0 : M) <• x.fst
          = x.fst •> (0 : M) + x.snd <• algebraMap S R s by
        rw [smul_zero]; rw [smul_zero]; rw [add_zero]; rw [zero_add]
        rw [Algebra.algebraMap_eq_smul_one]; rw [MulOpposite.op_smul]; rw [op_one]; rw [smul_assoc]; rw [one_smul]; rw [smul_assoc]; rw [one_smul]
  smul_def' := fun s x =>
ext (Algebra.smul_def _ _)
      show s • x.snd = algebraMap S R s •> x.snd + (0 : M) <• x.fst by
        rw [smul_zero]; rw [add_zero]; rw [algebraMap_smul]

-- shortcut instance for the common case
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R' (tsze R' M)
  body: TrivSqZeroExt.algebra' _ _ _

中文:
实例 :
  签名: Algebra R' (tsze R' M)
  定义体: TrivSqZeroExt.algebra' _ _ _

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, TrivSqZeroExt, TrivSqZeroExt.algebra, algebra, pullback_snd
-/
instance : Algebra R' (tsze R' M) :=
  TrivSqZeroExt.algebra' _ _ _

/--
theorem `algebraMap_eq_inl` / 定理 `algebraMap_eq_inl`

English:
theorem algebraMap_eq_inl
  statement: ⇑(algebraMap R' (tsze R' M)) = inl
  proof: rfl

中文:
定理 algebraMap_eq_inl
  结论: ⇑(algebraMap R' (tsze R' M)) = inl
  证明: rfl

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, restrict
-/
theorem algebraMap_eq_inl : ⇑(algebraMap R' (tsze R' M)) = inl :=
  rfl

/--
theorem `algebraMap_eq_inlHom` / 定理 `algebraMap_eq_inlHom`

English:
theorem algebraMap_eq_inlHom
  statement: algebraMap R' (tsze R' M) = inlHom R' M
  proof: rfl

中文:
定理 algebraMap_eq_inlHom
  结论: algebraMap R' (tsze R' M) = inlHom R' M
  证明: rfl

Depends on / 依赖: Scheme, Scheme.Hom.resLE, infer_instance
-/
theorem algebraMap_eq_inlHom : algebraMap R' (tsze R' M) = inlHom R' M :=
  rfl

/--
theorem `algebraMap_eq_inl'` / 定理 `algebraMap_eq_inl'`

English:
theorem algebraMap_eq_inl'
  given: (s : S)
  statement: algebraMap S (tsze R M) s = inl (algebraMap S R s)
  proof: rfl

中文:
定理 algebraMap_eq_inl'
  条件: (s : S)
  结论: algebraMap S (tsze R M) s = inl (algebraMap S R s)
  证明: rfl
-/
theorem algebraMap_eq_inl' (s : S) : algebraMap S (tsze R M) s = inl (algebraMap S R s) :=
  rfl

/-- The canonical `S`-algebra projection `TrivSqZeroExt R M → R`. -/
@[simps]
/--
Definition of `fstHom` / `fstHom` 的定义

English:
definition fstHom
  signature: : tsze R M ->ₐ[S] R where
  body: fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (M := M)
  map_add' := fst_add
  commutes' _r := fst_inl M _

中文:
定义 fstHom
  签名: : tsze R M ->ₐ[S] R where
  定义体: fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (M := M)
  map_add' := fst_add
  commutes' _r := fst_inl M _
-/
def fstHom : tsze R M ->ₐ[S] R where
  toFun := fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (M := M)
  map_add' := fst_add
  commutes' _r := fst_inl M _

/--
Definition of `algebraBase` / `algebraBase` 的定义

English:
abbreviation algebraBase
  signature: : Algebra (tsze R' M) R' where
  body: (fstHom R' R' M).toRingHom
  smul x r := x.fst * r
  commutes' _ _ := mul_comm ..
  smul_def' _ _ := rfl

中文:
缩写 algebraBase
  签名: : Algebra (tsze R' M) R' where
  定义体: (fstHom R' R' M).toRingHom
  smul x r := x.fst * r
  commutes' _ _ := mul_comm ..
  smul_def' _ _ := rfl

Depends on / 依赖: fstHom, toRingHom
-/
abbrev algebraBase : Algebra (tsze R' M) R' where
  algebraMap := (fstHom R' R' M).toRingHom
  smul x r := x.fst * r
  commutes' _ _ := mul_comm ..
  smul_def' _ _ := rfl

attribute [local instance] algebraBase in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R' (tsze R' M) R'
  body: mul_assoc ..

中文:
实例 :
  签名: IsScalarTower R' (tsze R' M) R'
  定义体: mul_assoc ..

Depends on / 依赖: IsZariskiLocalAtSource, IsZariskiLocalAtSource.sigmaDesc, mul_assoc, sigmaDesc
-/
instance : IsScalarTower R' (tsze R' M) R' where
  smul_assoc _ _ _ := mul_assoc ..

/-- The canonical `S`-algebra inclusion `R → TrivSqZeroExt R M`. -/
@[simps]
/--
Definition of `inlAlgHom` / `inlAlgHom` 的定义

English:
definition inlAlgHom
  signature: : R ->ₐ[S] tsze R M where
  body: inl
  map_one' := inl_one _
  map_mul' := inl_mul _
  map_zero' := inl_zero (M := M)
  map_add' := inl_add _
  commutes' _r := (algebraMap_eq_inl' _ _ _ _).symm

中文:
定义 inlAlgHom
  签名: : R ->ₐ[S] tsze R M where
  定义体: inl
  map_one' := inl_one _
  map_mul' := inl_mul _
  map_zero' := inl_zero (M := M)
  map_add' := inl_add _
  commutes' _r := (algebraMap_eq_inl' _ _ _ _).symm

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.Spec_iff, IsIntegral, IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff_of_openCover, MorphismProperty, MorphismProperty.cancel_right_of_respectsIso, Spec.map_preimage, Spec_iff, Subsingleton, X.affineCover, X.affineCover.f, Y.isoSpec.hom, affineCover, cancel_right_of_respectsIso, iff_of_openCover, isField_of_isIntegral_of_subsingleton, isoSpec, map_preimage, of_isField
-/
def inlAlgHom : R ->ₐ[S] tsze R M where
  toFun := inl
  map_one' := inl_one _
  map_mul' := inl_mul _
  map_zero' := inl_zero (M := M)
  map_add' := inl_add _
  commutes' _r := (algebraMap_eq_inl' _ _ _ _).symm

variable {R R' S M}

/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  given: {A} [Semiring A] [Algebra R' A] ⦃f g
  statement: tsze R' M ->ₐ[R'] A⦄
  proof: AlgHom.toLinearMap_injective
    linearMap_ext (fun _r => (f.commutes _).trans (g.commutes _).symm) h

@[ext]

中文:
定理 algHom_ext
  条件: {A} [Semiring A] [Algebra R' A] ⦃f g
  结论: tsze R' M ->ₐ[R'] A⦄
  证明: AlgHom.toLinearMap_injective
    linearMap_ext (fun _r => (f.commutes _).trans (g.commutes _).symm) h

@[ext]

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, commutes, f.commutes, g.commutes, linearMap_ext, toLinearMap_injective
-/
theorem algHom_ext {A} [Semiring A] [Algebra R' A] ⦃f g : tsze R' M ->ₐ[R'] A⦄
    (h : forall m, f (inr m) = g (inr m)) : f = g :=
AlgHom.toLinearMap_injective
    linearMap_ext (fun _r => (f.commutes _).trans (g.commutes _).symm) h

@[ext]
/--
theorem `algHom_ext'` / 定理 `algHom_ext'`

English:
theorem algHom_ext'
  given: {A} [Semiring A] [Algebra S A] ⦃f g
  statement: tsze R M ->ₐ[S] A⦄
  proof: AlgHom.toLinearMap_injective
    linearMap_ext (AlgHom.congr_fun hinl) (LinearMap.congr_fun hinr)

中文:
定理 algHom_ext'
  条件: {A} [Semiring A] [Algebra S A] ⦃f g
  结论: tsze R M ->ₐ[S] A⦄
  证明: AlgHom.toLinearMap_injective
    linearMap_ext (AlgHom.congr_fun hinl) (LinearMap.congr_fun hinr)

Depends on / 依赖: AlgHom, AlgHom.congr_fun, AlgHom.toLinearMap_injective, LinearMap, LinearMap.congr_fun, congr_fun, linearMap_ext, toLinearMap_injective
-/
theorem algHom_ext' {A} [Semiring A] [Algebra S A] ⦃f g : tsze R M ->ₐ[S] A⦄
    (hinl : f.comp (inlAlgHom S R M) = g.comp (inlAlgHom S R M))
    (hinr : f.toLinearMap.comp (inrHom R M |>.restrictScalars S) =
      g.toLinearMap.comp (inrHom R M |>.restrictScalars S)) : f = g :=
AlgHom.toLinearMap_injective
    linearMap_ext (AlgHom.congr_fun hinl) (LinearMap.congr_fun hinr)

variable {A : Type*} [Semiring A] [Algebra S A] [Algebra R' A]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  body: AlgHom.ofLinearMap
    ((f.comp <| fstHom S R M).toLinearMap + g ∘ₗ (sndHom R M |>.restrictScalars S))
    (show f 1 + g (0 : M) = 1 by rw [map_zero, map_one, add_zero])
    (TrivSqZeroExt.ind fun r₁ m₁ =>
      TrivSqZeroExt.ind fun r₂ m₂ => by
        dsimp
        simp only [add_zero, zero_add, a

中文:
定义 lift
  签名: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  定义体: AlgHom.ofLinearMap
    ((f.comp <| fstHom S R M).toLinearMap + g ∘ₗ (sndHom R M |>.restrictScalars S))
    (show f 1 + g (0 : M) = 1 by rw [map_zero, map_one, add_zero])
    (TrivSqZeroExt.ind fun r₁ m₁ =>
      TrivSqZeroExt.ind fun r₂ m₂ => by
        dsimp
        simp only [add_zero, zero_add, a

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, TrivSqZeroExt, TrivSqZeroExt.ind, add_assoc, add_comm, add_mul, add_zero, f.comp, fstHom, map_add, map_mul, map_one, map_zero, mul_add, ofLinearMap, restrictScalars, sndHom, toLinearMap, zero_add
-/
def lift (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
    (hg : forall x y, g x * g y = 0)
    (hfg : forall r x, g (r •> x) = f r * g x)
    (hgf : forall r x, g (x <• r) = g x * f r) : tsze R M ->ₐ[S] A :=
  AlgHom.ofLinearMap
    ((f.comp <| fstHom S R M).toLinearMap + g ∘ₗ (sndHom R M |>.restrictScalars S))
    (show f 1 + g (0 : M) = 1 by rw [map_zero, map_one, add_zero])
    (TrivSqZeroExt.ind fun r₁ m₁ =>
      TrivSqZeroExt.ind fun r₂ m₂ => by
        dsimp
        simp only [add_zero, zero_add, add_mul, mul_add, hg]
        rw [← map_mul]; rw [map_add]; rw [add_comm (g _)]; rw [add_assoc]; rw [hfg]; rw [hgf])

/--
theorem `lift_def` / 定理 `lift_def`

English:
theorem lift_def
  statement: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  proof: rfl

@[simp]

中文:
定理 lift_def
  结论: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  证明: rfl

@[simp]
-/
theorem lift_def (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
    (hg : forall x y, g x * g y = 0)
    (hfg : forall r x, g (r • x) = f r * g x)
    (hgf : forall r x, g (op r • x) = g x * f r) (x : tsze R M) :
    lift f g hg hfg hgf x = f x.fst + g x.snd :=
  rfl

@[simp]
/--
theorem `lift_apply_inl` / 定理 `lift_apply_inl`

English:
theorem lift_apply_inl
  statement: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  proof: show f r + g 0 = f r by rw [map_zero, add_zero]

@[simp]

中文:
定理 lift_apply_inl
  结论: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  证明: show f r + g 0 = f r by rw [map_zero, add_zero]

@[simp]

Depends on / 依赖: add_zero, map_zero
-/
theorem lift_apply_inl (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
    (hg : forall x y, g x * g y = 0)
    (hfg : forall r x, g (r •> x) = f r * g x)
    (hgf : forall r x, g (x <• r) = g x * f r)
    (r : R) :
    lift f g hg hfg hgf (inl r) = f r :=
  show f r + g 0 = f r by rw [map_zero, add_zero]

@[simp]
/--
theorem `lift_apply_inr` / 定理 `lift_apply_inr`

English:
theorem lift_apply_inr
  statement: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  proof: show f 0 + g m = g m by rw [map_zero, zero_add]

@[simp]

中文:
定理 lift_apply_inr
  结论: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  证明: show f 0 + g m = g m by rw [map_zero, zero_add]

@[simp]

Depends on / 依赖: map_zero, zero_add
-/
theorem lift_apply_inr (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
    (hg : forall x y, g x * g y = 0)
    (hfg : forall r x, g (r •> x) = f r * g x)
    (hgf : forall r x, g (x <• r) = g x * f r)
    (m : M) :
    lift f g hg hfg hgf (inr m) = g m :=
  show f 0 + g m = g m by rw [map_zero, zero_add]

@[simp]
/--
theorem `lift_comp_inlHom` / 定理 `lift_comp_inlHom`

English:
theorem lift_comp_inlHom
  statement: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  proof: AlgHom.ext lift_apply_inl f g hg hfg hgf

@[simp]

中文:
定理 lift_comp_inlHom
  结论: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  证明: AlgHom.ext lift_apply_inl f g hg hfg hgf

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ext, lift_apply_inl
-/
theorem lift_comp_inlHom (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
    (hg : forall x y, g x * g y = 0)
    (hfg : forall r x, g (r •> x) = f r * g x)
    (hgf : forall r x, g (x <• r) = g x * f r) :
    (lift f g hg hfg hgf).comp (inlAlgHom S R M) = f :=
AlgHom.ext lift_apply_inl f g hg hfg hgf

@[simp]
/--
theorem `lift_comp_inrHom` / 定理 `lift_comp_inrHom`

English:
theorem lift_comp_inrHom
  statement: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  proof: LinearMap.ext lift_apply_inr f g hg hfg hgf

中文:
定理 lift_comp_inrHom
  结论: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  证明: LinearMap.ext lift_apply_inr f g hg hfg hgf

Depends on / 依赖: LinearMap, LinearMap.ext, lift_apply_inr
-/
theorem lift_comp_inrHom (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
    (hg : forall x y, g x * g y = 0)
    (hfg : forall r x, g (r •> x) = f r * g x)
    (hgf : forall r x, g (x <• r) = g x * f r) :
    (lift f g hg hfg hgf).toLinearMap.comp (inrHom R M |>.restrictScalars S) = g :=
LinearMap.ext lift_apply_inr f g hg hfg hgf

/-- When applied to `inr` and `inl` themselves, `lift` is the identity. -/
@[simp]
/--
theorem `lift_inlAlgHom_inrHom` / 定理 `lift_inlAlgHom_inrHom`

English:
theorem lift_inlAlgHom_inrHom
  proof: algHom_ext' (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)


@[simp]

中文:
定理 lift_inlAlgHom_inrHom
  证明: algHom_ext' (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)


@[simp]

Depends on / 依赖: algHom_ext, lift_comp_inlHom, lift_comp_inrHom
-/
theorem lift_inlAlgHom_inrHom :
    lift (inlAlgHom _ _ _) (inrHom R M |>.restrictScalars S)
      (inr_mul_inr R) (fun _ _ => (inl_mul_inr _ _).symm) (fun _ _ => (inr_mul_inl _ _).symm) =
    AlgHom.id S (tsze R M) :=
  algHom_ext' (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)


@[simp]
/--
theorem `range_inlAlgHom_sup_adjoin_range_inr` / 定理 `range_inlAlgHom_sup_adjoin_range_inr`

English:
theorem range_inlAlgHom_sup_adjoin_range_inr
  proof: by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.inl_fst_add_inr_snd_eq]
  refine add_mem ?_ ?_
· exact le_sup_left (α := Subalgebra S _) Set.mem_range_self x.fst
· exact le_sup_right (α := Subalgebra S _) Algebra.subset_adjoin Set.mem_range_self x.snd

@[simp]

中文:
定理 range_inlAlgHom_sup_adjoin_range_inr
  证明: by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.inl_fst_add_inr_snd_eq]
  refine add_mem ?_ ?_
· exact le_sup_left (α := Subalgebra S _) Set.mem_range_self x.fst
· exact le_sup_right (α := Subalgebra S _) Algebra.subset_adjoin Set.mem_range_self x.snd

@[simp]

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Set.mem_range_self, Subalgebra, add_mem, inl_fst_add_inr_snd_eq, le_sup_left, le_sup_right, mem_range_self, subset_adjoin, top_unique, x.fst, x.inl_fst_add_inr_snd_eq, x.snd
-/
theorem range_inlAlgHom_sup_adjoin_range_inr :
    (inlAlgHom S R M).range ⊔ Algebra.adjoin S (Set.range inr) = (⊤ : Subalgebra S (tsze R M)) := by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.inl_fst_add_inr_snd_eq]
  refine add_mem ?_ ?_
· exact le_sup_left (α := Subalgebra S _) Set.mem_range_self x.fst
· exact le_sup_right (α := Subalgebra S _) Algebra.subset_adjoin Set.mem_range_self x.snd

@[simp]
/--
theorem `range_liftAux` / 定理 `range_liftAux`

English:
theorem range_liftAux
  statement: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  proof: by
  simp_rw [← Algebra.map_top, ← range_inlAlgHom_sup_adjoin_range_inr, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, lift_comp_inlHom, ← Set.range_comp, Function.comp_def,
    lift_apply_inr, Algebra.map_top]

中文:
定理 range_liftAux
  结论: (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
  证明: by
  simp_rw [← Algebra.map_top, ← range_inlAlgHom_sup_adjoin_range_inr, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, lift_comp_inlHom, ← Set.range_comp, Function.comp_def,
    lift_apply_inr, Algebra.map_top]

Depends on / 依赖: AlgHom, AlgHom.map_adjoin, AlgHom.range_comp, Algebra, Algebra.map_sup, Algebra.map_top, Function, Function.comp_def, Set.range_comp, comp_def, lift_apply_inr, lift_comp_inlHom, map_adjoin, map_sup, map_top, range_comp, range_inlAlgHom_sup_adjoin_range_inr, simp_rw
-/
theorem range_liftAux (f : R ->ₐ[S] A) (g : M ->ₗ[S] A)
    (hg : forall x y, g x * g y = 0)
    (hfg : forall r x, g (r •> x) = f r * g x)
    (hgf : forall r x, g (x <• r) = g x * f r) :
    (lift f g hg hfg hgf).range = f.range ⊔ Algebra.adjoin S (Set.range g) := by
  simp_rw [← Algebra.map_top, ← range_inlAlgHom_sup_adjoin_range_inr, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, lift_comp_inlHom, ← Set.range_comp, Function.comp_def,
    lift_apply_inr, Algebra.map_top]

/-- A universal property of the trivial square-zero extension, providing a unique
`TrivSqZeroExt R M →ₐ[R] A` for every pair of maps `f : R →ₐ[S] A` and `g : M →ₗ[S] A`,
where the range of `g` has no non-zero products, and scaling the input to `g` on the left or right
amounts to a corresponding multiplication by `f` in the output.

This isomorphism is named to match the very similar `Complex.lift`. -/
@[simps! apply symm_apply_coe]
/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: :
  body: lift fg.val.1 fg.val.2 fg.prop.1 fg.prop.2.1 fg.prop.2.2
  invFun F :=
    ⟨(F.comp (inlAlgHom _ _ _), F.toLinearMap ∘ₗ (inrHom _ _ |>.restrictScalars _)),
      (fun _x _y =>
(map_mul F _ _).symm.trans (F.congr_arg <| inr_mul_inr _ _ _).trans (map_zero F)),
      (fun _r _x => (F.congr_arg (inl_mul

中文:
定义 liftEquiv
  签名: :
  定义体: lift fg.val.1 fg.val.2 fg.prop.1 fg.prop.2.1 fg.prop.2.2
  invFun F :=
    ⟨(F.comp (inlAlgHom _ _ _), F.toLinearMap ∘ₗ (inrHom _ _ |>.restrictScalars _)),
      (fun _x _y =>
(map_mul F _ _).symm.trans (F.congr_arg <| inr_mul_inr _ _ _).trans (map_zero F)),
      (fun _r _x => (F.congr_arg (inl_mul

Depends on / 依赖: fg.prop, fg.val
-/
def liftEquiv :
    {fg : (R ->ₐ[S] A) × (M ->ₗ[S] A) //
      (forall x y, fg.2 x * fg.2 y = 0) ∧
      (forall r x, fg.2 (r •> x) = fg.1 r * fg.2 x) ∧
      (forall r x, fg.2 (x <• r) = fg.2 x * fg.1 r)} ≃ (tsze R M ->ₐ[S] A) where
  toFun fg := lift fg.val.1 fg.val.2 fg.prop.1 fg.prop.2.1 fg.prop.2.2
  invFun F :=
    ⟨(F.comp (inlAlgHom _ _ _), F.toLinearMap ∘ₗ (inrHom _ _ |>.restrictScalars _)),
      (fun _x _y =>
(map_mul F _ _).symm.trans (F.congr_arg <| inr_mul_inr _ _ _).trans (map_zero F)),
      (fun _r _x => (F.congr_arg (inl_mul_inr _ _).symm).trans (map_mul F _ _)),
      (fun _r _x => (F.congr_arg (inr_mul_inl _ _).symm).trans (map_mul F _ _))⟩
left_inv _f := Subtype.ext Prod.ext (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)
  right_inv _F := algHom_ext' (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)

/-- A simplified version of `TrivSqZeroExt.liftEquiv` for the commutative case. -/
@[simps! apply symm_apply_coe]
/--
Definition of `liftEquivOfComm` / `liftEquivOfComm` 的定义

English:
definition liftEquivOfComm
  signature: :
  body: by
  refine Equiv.trans ?_ liftEquiv
  exact {
    toFun := fun f => ⟨(Algebra.ofId _ _, f.val), f.prop,
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply],
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply, Algebra.commutes]⟩
    invFun := fun fg => ⟨fg.val.2, fg.prop.1⟩ }

中文:
定义 liftEquivOfComm
  签名: :
  定义体: by
  refine Equiv.trans ?_ liftEquiv
  exact {
    toFun := fun f => ⟨(Algebra.ofId _ _, f.val), f.prop,
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply],
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply, Algebra.commutes]⟩
    invFun := fun fg => ⟨fg.val.2, fg.prop.1⟩ }

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.ofId, Algebra.ofId_apply, Algebra.smul_def, Equiv.trans, commutes, f.prop, f.val, fg.prop, fg.val, invFun, liftEquiv, ofId_apply, smul_def
-/
def liftEquivOfComm :
    { f : M ->ₗ[R'] A // forall x y, f x * f y = 0 } ≃ (tsze R' M ->ₐ[R'] A) := by
  refine Equiv.trans ?_ liftEquiv
  exact {
    toFun := fun f => ⟨(Algebra.ofId _ _, f.val), f.prop,
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply],
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply, Algebra.commutes]⟩
    invFun := fun fg => ⟨fg.val.2, fg.prop.1⟩ }

section map

variable {N P : Type*} [AddCommMonoid N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [AddCommMonoid P] [Module R' P] [Module R'ᵐᵒᵖ P] [IsCentralScalar R' P]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₗ[R'] N)
  body: liftEquivOfComm ⟨inrHom R' N ∘ₗ f, fun _ _ => inr_mul_inr _ _ _⟩

@[simp]

中文:
定义 map
  签名: (f : M ->ₗ[R'] N)
  定义体: liftEquivOfComm ⟨inrHom R' N ∘ₗ f, fun _ _ => inr_mul_inr _ _ _⟩

@[simp]

Depends on / 依赖: inrHom, inr_mul_inr, liftEquivOfComm
-/
def map (f : M ->ₗ[R'] N) : TrivSqZeroExt R' M ->ₐ[R'] TrivSqZeroExt R' N :=
  liftEquivOfComm ⟨inrHom R' N ∘ₗ f, fun _ _ => inr_mul_inr _ _ _⟩

@[simp]
/--
theorem `map_inl` / 定理 `map_inl`

English:
theorem map_inl
  given: (f : M ->ₗ[R'] N) (r : R')
  statement: map f (inl r) = inl r
  proof: by
  rw [map]; rw [liftEquivOfComm_apply]; rw [lift_apply_inl]; rw [Algebra.ofId_apply]; rw [algebraMap_eq_inl]

@[simp]

中文:
定理 map_inl
  条件: (f : M ->ₗ[R'] N) (r : R')
  结论: map f (inl r) = inl r
  证明: by
  rw [map]; rw [liftEquivOfComm_apply]; rw [lift_apply_inl]; rw [Algebra.ofId_apply]; rw [algebraMap_eq_inl]

@[simp]

Depends on / 依赖: Algebra, Algebra.ofId_apply, algebraMap_eq_inl, liftEquivOfComm_apply, lift_apply_inl, ofId_apply
-/
theorem map_inl (f : M ->ₗ[R'] N) (r : R') : map f (inl r) = inl r := by
  rw [map]; rw [liftEquivOfComm_apply]; rw [lift_apply_inl]; rw [Algebra.ofId_apply]; rw [algebraMap_eq_inl]

@[simp]
/--
theorem `map_inr` / 定理 `map_inr`

English:
theorem map_inr
  given: (f : M ->ₗ[R'] N) (x : M)
  statement: map f (inr x) = inr (f x)
  proof: by
  rw [map]; rw [liftEquivOfComm_apply]; rw [lift_apply_inr]; rw [LinearMap.comp_apply]; rw [inrHom_apply]

@[simp]

中文:
定理 map_inr
  条件: (f : M ->ₗ[R'] N) (x : M)
  结论: map f (inr x) = inr (f x)
  证明: by
  rw [map]; rw [liftEquivOfComm_apply]; rw [lift_apply_inr]; rw [LinearMap.comp_apply]; rw [inrHom_apply]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, comp_apply, inrHom_apply, liftEquivOfComm_apply, lift_apply_inr
-/
theorem map_inr (f : M ->ₗ[R'] N) (x : M) : map f (inr x) = inr (f x) := by
  rw [map]; rw [liftEquivOfComm_apply]; rw [lift_apply_inr]; rw [LinearMap.comp_apply]; rw [inrHom_apply]

@[simp]
/--
theorem `fst_map` / 定理 `fst_map`

English:
theorem fst_map
  given: (f : M ->ₗ[R'] N) (x : TrivSqZeroExt R' M)
  statement: fst (map f x) = fst x
  proof: by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]

中文:
定理 fst_map
  条件: (f : M ->ₗ[R'] N) (x : TrivSqZeroExt R' M)
  结论: fst (map f x) = fst x
  证明: by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]

Depends on / 依赖: Algebra, Algebra.ofId_apply, algebraMap_eq_inl, lift_def, ofId_apply
-/
theorem fst_map (f : M ->ₗ[R'] N) (x : TrivSqZeroExt R' M) : fst (map f x) = fst x := by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]
/--
theorem `snd_map` / 定理 `snd_map`

English:
theorem snd_map
  given: (f : M ->ₗ[R'] N) (x : TrivSqZeroExt R' M)
  statement: snd (map f x) = f (snd x)
  proof: by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]

中文:
定理 snd_map
  条件: (f : M ->ₗ[R'] N) (x : TrivSqZeroExt R' M)
  结论: snd (map f x) = f (snd x)
  证明: by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]

Depends on / 依赖: Algebra, Algebra.ofId_apply, algebraMap_eq_inl, lift_def, ofId_apply
-/
theorem snd_map (f : M ->ₗ[R'] N) (x : TrivSqZeroExt R' M) : snd (map f x) = f (snd x) := by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]
/--
theorem `map_comp_inlAlgHom` / 定理 `map_comp_inlAlgHom`

English:
theorem map_comp_inlAlgHom
  given: (f : M ->ₗ[R'] N)
  proof: AlgHom.ext map_inl _

@[simp]

中文:
定理 map_comp_inlAlgHom
  条件: (f : M ->ₗ[R'] N)
  证明: AlgHom.ext map_inl _

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ext, map_inl
-/
theorem map_comp_inlAlgHom (f : M ->ₗ[R'] N) :
    (map f).comp (inlAlgHom R' R' M) = inlAlgHom R' R' N :=
AlgHom.ext map_inl _

@[simp]
/--
theorem `map_comp_inrHom` / 定理 `map_comp_inrHom`

English:
theorem map_comp_inrHom
  given: (f : M ->ₗ[R'] N)
  proof: LinearMap.ext map_inr _

@[simp]

中文:
定理 map_comp_inrHom
  条件: (f : M ->ₗ[R'] N)
  证明: LinearMap.ext map_inr _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, map_inr
-/
theorem map_comp_inrHom (f : M ->ₗ[R'] N) :
    (map f).toLinearMap ∘ₗ inrHom R' M = inrHom R' N ∘ₗ f :=
LinearMap.ext map_inr _

@[simp]
/--
theorem `fstHom_comp_map` / 定理 `fstHom_comp_map`

English:
theorem fstHom_comp_map
  given: (f : M ->ₗ[R'] N)
  proof: AlgHom.ext fst_map _

@[simp]

中文:
定理 fstHom_comp_map
  条件: (f : M ->ₗ[R'] N)
  证明: AlgHom.ext fst_map _

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ext, fst_map
-/
theorem fstHom_comp_map (f : M ->ₗ[R'] N) :
    (fstHom R' R' N).comp (map f) = fstHom R' R' M :=
AlgHom.ext fst_map _

@[simp]
/--
theorem `sndHom_comp_map` / 定理 `sndHom_comp_map`

English:
theorem sndHom_comp_map
  given: (f : M ->ₗ[R'] N)
  proof: LinearMap.ext snd_map _

@[simp]

中文:
定理 sndHom_comp_map
  条件: (f : M ->ₗ[R'] N)
  证明: LinearMap.ext snd_map _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, snd_map
-/
theorem sndHom_comp_map (f : M ->ₗ[R'] N) :
    sndHom R' N ∘ₗ (map f).toLinearMap = f ∘ₗ sndHom R' M :=
LinearMap.ext snd_map _

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (LinearMap.id : M ->ₗ[R'] M) = AlgHom.id R' _
  proof: by
  apply algHom_ext
  simp only [map_inr, LinearMap.id_coe, id_eq, AlgHom.coe_id, forall_const]

中文:
定理 map_id
  结论: map (LinearMap.id : M ->ₗ[R'] M) = AlgHom.id R' _
  证明: by
  apply algHom_ext
  simp only [map_inr, LinearMap.id_coe, id_eq, AlgHom.coe_id, forall_const]

Depends on / 依赖: AlgHom, AlgHom.coe_id, LinearMap, LinearMap.id_coe, algHom_ext, coe_id, forall_const, id_coe, id_eq, map_inr
-/
theorem map_id : map (LinearMap.id : M ->ₗ[R'] M) = AlgHom.id R' _ := by
  apply algHom_ext
  simp only [map_inr, LinearMap.id_coe, id_eq, AlgHom.coe_id, forall_const]

/--
theorem `map_comp_map` / 定理 `map_comp_map`

English:
theorem map_comp_map
  given: (f : M ->ₗ[R'] N) (g : N ->ₗ[R'] P)
  proof: by
  apply algHom_ext
  simp only [map_inr, LinearMap.coe_comp, Function.comp_apply, AlgHom.coe_comp, forall_const]

中文:
定理 map_comp_map
  条件: (f : M ->ₗ[R'] N) (g : N ->ₗ[R'] P)
  证明: by
  apply algHom_ext
  simp only [map_inr, LinearMap.coe_comp, Function.comp_apply, AlgHom.coe_comp, forall_const]

Depends on / 依赖: AlgHom, AlgHom.coe_comp, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, algHom_ext, coe_comp, comp_apply, forall_const, map_inr
-/
theorem map_comp_map (f : M ->ₗ[R'] N) (g : N ->ₗ[R'] P) :
    map (g.comp f) = (map g).comp (map f) := by
  apply algHom_ext
  simp only [map_inr, LinearMap.coe_comp, Function.comp_apply, AlgHom.coe_comp, forall_const]

end map

end Algebra

end TrivSqZeroExt
