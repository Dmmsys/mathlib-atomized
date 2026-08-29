/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Filippo A. E. Nuccio, Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.Prime

/-!
# Prime spectrum of a commutative (semi)ring as a type

The prime spectrum of a commutative (semi)ring is the type of all prime ideals.

For the Zariski topology, see `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `AlgebraicGeometry.StructureSheaf`.)

## Main definitions

* `PrimeSpectrum R`: The prime spectrum of a commutative (semi)ring `R`,
  i.e., the set of all prime ideals of `R`.
-/

@[expose] public section

/-- The prime spectrum of a commutative (semi)ring `R` is the type of all prime ideals of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `Mathlib/AlgebraicGeometry/StructureSheaf.lean`).
It is a fundamental building block in algebraic geometry. -/
@[ext]
/--
Definition of `PrimeSpectrum` / `PrimeSpectrum` 的定义

English:
structure PrimeSpectrum
  parameters: (R : Type*) [CommSemiring R]
  axioms and operations (2):
    - asIdeal : Ideal R
    - isPrime : asIdeal.IsPrime

中文:
结构 素谱
  参数: (R : 类型) [交换半环 R]
  公理与运算 (2 个):
    - asIdeal : 理想 R
    - isPrime : asIdeal.是素
-/
structure PrimeSpectrum (R : Type*) [CommSemiring R] where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime

attribute [instance] PrimeSpectrum.isPrime

namespace PrimeSpectrum

/-!
## The specialization order

We endow `PrimeSpectrum R` with a partial order induced from the ideal lattice.
This is exactly the specialization order.
See the corresponding section at `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.
-/

variable {R : Type*} [CommSemiring R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (PrimeSpectrum R) (Ideal R)
  body: P.asIdeal

中文:
实例 :
  签名: Coe (素谱 R) (理想 R)
  定义体: P.asIdeal

Depends on / 依赖: P.asIdeal, asIdeal
-/
instance : Coe (PrimeSpectrum R) (Ideal R) where
  coe P := P.asIdeal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (PrimeSpectrum R)
  body: PartialOrder.lift asIdeal (@PrimeSpectrum.ext _ _)

@[simp]

中文:
实例 :
  签名: 偏序 (素谱 R)
  定义体: PartialOrder.lift asIdeal (@PrimeSpectrum.ext _ _)

@[simp]

Depends on / 依赖: PartialOrder, PartialOrder.lift, PrimeSpectrum, PrimeSpectrum.ext, asIdeal
-/
instance : PartialOrder (PrimeSpectrum R) :=
  PartialOrder.lift asIdeal (@PrimeSpectrum.ext _ _)

@[simp]
/--
theorem `asIdeal_le_asIdeal` / 定理 `asIdeal_le_asIdeal`

English:
theorem asIdeal_le_asIdeal
  given: (x y : PrimeSpectrum R)
  statement: x.asIdeal <= y.asIdeal ↔ x <= y
  proof: Iff.rfl

@[simp]

中文:
定理 asIdeal_le_asIdeal
  条件: (x y : 素谱 R)
  结论: x.asIdeal <= y.asIdeal ↔ x <= y
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem asIdeal_le_asIdeal (x y : PrimeSpectrum R) : x.asIdeal <= y.asIdeal ↔ x <= y :=
  Iff.rfl

@[simp]
/--
theorem `asIdeal_lt_asIdeal` / 定理 `asIdeal_lt_asIdeal`

English:
theorem asIdeal_lt_asIdeal
  given: (x y : PrimeSpectrum R)
  statement: x.asIdeal < y.asIdeal ↔ x < y
  proof: Iff.rfl

中文:
定理 asIdeal_lt_asIdeal
  条件: (x y : 素谱 R)
  结论: x.asIdeal < y.asIdeal ↔ x < y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem asIdeal_lt_asIdeal (x y : PrimeSpectrum R) : x.asIdeal < y.asIdeal ↔ x < y :=
  Iff.rfl

variable (R) in
/-- The prime spectrum is in bijection with the set of prime ideals. -/
@[simps]
/--
Definition of `equivSubtype` / `equivSubtype` 的定义

English:
definition equivSubtype
  signature: : PrimeSpectrum R ≃o {I : Ideal R // I.IsPrime} where
  body: ⟨I.asIdeal, I.2⟩
  invFun I := ⟨I, I.2⟩
  map_rel_iff' := .rfl

中文:
定义 equivSubtype
  签名: : 素谱 R ≃o {I : 理想 R // I.是素} where
  定义体: ⟨I.asIdeal, I.2⟩
  invFun I := ⟨I, I.2⟩
  map_rel_iff' := .rfl

Depends on / 依赖: I.asIdeal, asIdeal
-/
def equivSubtype : PrimeSpectrum R ≃o {I : Ideal R // I.IsPrime} where
  toFun I := ⟨I.asIdeal, I.2⟩
  invFun I := ⟨I, I.2⟩
  map_rel_iff' := .rfl

end PrimeSpectrum
