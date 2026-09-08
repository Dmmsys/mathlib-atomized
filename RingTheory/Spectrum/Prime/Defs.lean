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
/-
**PrimeSpectrum** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [CommSemiring R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime spectrum of a commutative (semi)ring `R` is the type of all prime idea
ls of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `Mathlib/AlgebraicGeometry/StructureSheaf.
lean`).
It is a fundamental building block in algebraic geometry.
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

/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (PrimeSpectrum R) (Ideal R) where
  coe P := P.asIdeal
/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (PrimeSpectrum R) :=
  PartialOrder.lift asIdeal (@PrimeSpectrum.ext _ _)

@[simp]
/-
**PrimeSpectrum.asIdeal_le_asIdeal** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：asIdeal_le_asIdeal (x y : PrimeSpectrum R) : x.asIdeal <= y.asIdeal ↔ x <=
 y
参数：x y : PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem asIdeal_le_asIdeal (x y : PrimeSpectrum R) : x.asIdeal ≤ y.asIdeal ↔ x ≤ y :=
  Iff.rfl

@[simp]
/-
**PrimeSpectrum.asIdeal_lt_asIdeal** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：asIdeal_lt_asIdeal (x y : PrimeSpectrum R) : x.asIdeal < y.asIdeal ↔ x < y
参数：x y : PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem asIdeal_lt_asIdeal (x y : PrimeSpectrum R) : x.asIdeal < y.asIdeal ↔ x < y :=
  Iff.rfl

variable (R) in
/-- The prime spectrum is in bijection with the set of prime ideals. -/
@[simps]
/-
**PrimeSpectrum.equivSubtype** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：equivSubtype : PrimeSpectrum R ≃o {I : Ideal R // I.IsPrime} where toFun I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
The prime spectrum is in bijection with the set of prime ideals.
-/
def equivSubtype : PrimeSpectrum R ≃o {I : Ideal R // I.IsPrime} where
  toFun I := ⟨I.asIdeal, I.2⟩
  invFun I := ⟨I, I.2⟩
  map_rel_iff' := .rfl

end PrimeSpectrum

