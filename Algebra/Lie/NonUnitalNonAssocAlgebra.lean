/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Lie.Basic

/-!
# Lie algebras as non-unital, non-associative algebras

The definition of Lie algebras uses the `Bracket` typeclass for multiplication whereas we have a
separate `Mul` typeclass used for general algebras.

It is useful to have a special typeclass for Lie algebras because:
* it enables us to use the traditional notation `⁅x, y⁆` for the Lie multiplication,
* associative algebras carry a natural Lie algebra structure via the ring commutator and so we
  need them to carry both `Mul` and `Bracket` simultaneously,
* more generally, Poisson algebras (not yet defined) need both typeclasses.

However there are times when it is convenient to be able to regard a Lie algebra as a general
algebra and we provide some basic definitions for doing so here.

## Main definitions

  * `CommutatorRing` turns a Lie ring into a `NonUnitalNonAssocRing` by turning its
    `Bracket` (denoted `⁅ , ⁆`) into a `Mul` (denoted `*`).
  * `LieHom.toNonUnitalAlgHom`

## Tags

lie algebra, non-unital, non-associative
-/

@[expose] public section


universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/--
Definition of `CommutatorRing` / `CommutatorRing` 的定义

English:
definition CommutatorRing
  signature: (L : Type v)
  body: L

中文:
定义 CommutatorRing
  签名: (L : 类型v)
  定义体: L
-/
def CommutatorRing (L : Type v) : Type v := L

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalNonAssocRing (CommutatorRing L)
  body: have := LieRing.toNonUnitalNonAssocRing L
inferInstanceAs NonUnitalNonAssocRing L

中文:
实例 :
  签名: 非幺非结合环 (CommutatorRing L)
  定义体: have := LieRing.toNonUnitalNonAssocRing L
inferInstanceAs NonUnitalNonAssocRing L

Depends on / 依赖: LieRing, LieRing.toNonUnitalNonAssocRing, NonUnitalNonAssocRing, toNonUnitalNonAssocRing
-/
instance : NonUnitalNonAssocRing (CommutatorRing L) :=
  have := LieRing.toNonUnitalNonAssocRing L
inferInstanceAs NonUnitalNonAssocRing L

namespace LieAlgebra

instance (L : Type v) [Nonempty L] : Nonempty (CommutatorRing L) := ‹Nonempty L›

instance (L : Type v) [Inhabited L] : Inhabited (CommutatorRing L) := ‹Inhabited L›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRing (CommutatorRing L)
  body: inferInstanceAs LieRing L

中文:
实例 :
  签名: Lie环 (CommutatorRing L)
  定义体: inferInstanceAs LieRing L

Depends on / 依赖: LieRing
-/
instance : LieRing (CommutatorRing L) := inferInstanceAs LieRing L

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieAlgebra R (CommutatorRing L)
  body: inferInstanceAs LieAlgebra R L

中文:
实例 :
  签名: Lie代数 R (CommutatorRing L)
  定义体: inferInstanceAs LieAlgebra R L

Depends on / 依赖: LieAlgebra
-/
instance : LieAlgebra R (CommutatorRing L) := inferInstanceAs LieAlgebra R L

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: : IsScalarTower R (CommutatorRing L) (CommutatorRing L)
  body: ⟨smul_lie (L := L) (M := L)⟩

中文:
实例 isScalarTower
  签名: : 标量塔 R (CommutatorRing L) (CommutatorRing L)
  定义体: ⟨smul_lie (L := L) (M := L)⟩

Depends on / 依赖: smul_lie
-/
instance isScalarTower : IsScalarTower R (CommutatorRing L) (CommutatorRing L) :=
  ⟨smul_lie (L := L) (M := L)⟩

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: : SMulCommClass R (CommutatorRing L) (CommutatorRing L)
  body: ⟨fun t x y => (lie_smul t x y).symm⟩

中文:
实例 smulCommClass
  签名: : 标量交换类 R (CommutatorRing L) (CommutatorRing L)
  定义体: ⟨fun t x y => (lie_smul t x y).symm⟩

Depends on / 依赖: lie_smul
-/
instance smulCommClass : SMulCommClass R (CommutatorRing L) (CommutatorRing L) :=
  ⟨fun t x y => (lie_smul t x y).symm⟩

end LieAlgebra

namespace LieHom

variable {R L}
variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

/-- Regarding the `LieRing` of a `LieAlgebra` as a `NonUnitalNonAssocRing`, we can
regard a `LieHom` as a `NonUnitalAlgHom`. -/
@[simps toFun]
/--
Definition of `toNonUnitalAlgHom` / `toNonUnitalAlgHom` 的定义

English:
definition toNonUnitalAlgHom
  signature: (f : L ->ₗ⁅R⁆ L₂)
  body: { f with
    toFun := f
    map_zero' := f.toLinearMap.map_zero
    map_mul' := f.map_lie }

中文:
定义 toNonUnitalAlgHom
  签名: (f : L ->ₗ⁅R⁆ L₂)
  定义体: { f with
    toFun := f
    map_zero' := f.toLinearMap.map_zero
    map_mul' := f.map_lie }

Depends on / 依赖: f.map_lie, f.toLinearMap.map_zero, map_lie, map_mul, map_zero, toLinearMap
-/
def toNonUnitalAlgHom (f : L ->ₗ⁅R⁆ L₂) : CommutatorRing L ->ₙₐ[R] CommutatorRing L₂ :=
  { f with
    toFun := f
    map_zero' := f.toLinearMap.map_zero
    map_mul' := f.map_lie }

/--
theorem `toNonUnitalAlgHom_injective` / 定理 `toNonUnitalAlgHom_injective`

English:
theorem toNonUnitalAlgHom_injective
  proof: fun _ _ h => ext NonUnitalAlgHom.congr_fun h

中文:
定理 toNonUnitalAlgHom_injective
  证明: fun _ _ h => ext NonUnitalAlgHom.congr_fun h

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.congr_fun, congr_fun
-/
theorem toNonUnitalAlgHom_injective :
    Function.Injective (toNonUnitalAlgHom : _ -> CommutatorRing L ->ₙₐ[R] CommutatorRing L₂) :=
fun _ _ h => ext NonUnitalAlgHom.congr_fun h

end LieHom
