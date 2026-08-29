/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Subalgebras over Commutative Semiring

In this file we define `Subalgebra`s and the usual operations on them (`map`, `comap`).

The `Algebra.adjoin` operation and complete lattice structure can be found in
`Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean`.
-/

@[expose] public section

open Module

universe u u' v w w'

/--
Definition of `Subalgebra` / `Subalgebra` 的定义

English:
structure Subalgebra
  parameters: (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A]
  extends: Subsemiring A
  axioms and operations (3):
    - algebraMap_mem' : forall r, algebraMap R A r in carrier
    - zero_mem' : = (algebraMap R A).map_zero ▸ algebraMap_mem' 0
    - one_mem' : = (algebraMap R A).map_one ▸ algebraMap_mem' 1

中文:
结构 Subalgebra
  参数: (R : 类型u) (A : 类型v) [CommSemiring R] [Semiring A] [Algebra R A]
  继承: Subsemiring A
  公理与运算 (3 个):
    - algebraMap_mem' : 对任意 r, algebraMap R A r in carrier
    - zero_mem' : = (algebraMap R A).map_zero ▸ algebraMap_mem' 0
    - one_mem' : = (algebraMap R A).map_one ▸ algebraMap_mem' 1

Depends on / 依赖: algebraMap, algebraMap_mem, map_zero
-/
structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : Type v
    extends Subsemiring A where
  /-- The image of `algebraMap` is contained in the underlying set of the subalgebra -/
  algebraMap_mem' : forall r, algebraMap R A r in carrier
  zero_mem' := (algebraMap R A).map_zero ▸ algebraMap_mem' 0
  one_mem' := (algebraMap R A).map_one ▸ algebraMap_mem' 1

/-- Reinterpret a `Subalgebra` as a `Subsemiring`. -/
add_decl_doc Subalgebra.toSubsemiring

namespace Subalgebra

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Subalgebra R A) A
  body: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

中文:
实例 :
  签名: SetLike (Subalgebra R A) A
  定义体: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (Subalgebra R A) A where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Subalgebra R A)
  body: .ofSetLike (Subalgebra R A) A

initialize_simps_projections Subalgebra (carrier -> coe, as_prefix coe)

@[simp]

中文:
实例 :
  签名: PartialOrder (Subalgebra R A)
  定义体: .ofSetLike (Subalgebra R A) A

initialize_simps_projections Subalgebra (carrier -> coe, as_prefix coe)

@[simp]

Depends on / 依赖: Subalgebra, ofSetLike
-/
instance : PartialOrder (Subalgebra R A) := .ofSetLike (Subalgebra R A) A

initialize_simps_projections Subalgebra (carrier -> coe, as_prefix coe)

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Subsemiring A) (h)
  statement: (Subalgebra.mk (R := R) s h : Set A) = s
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (s : Subsemiring A) (h)
  结论: (Subalgebra.mk (R := R) s h : Set A) = s
  证明: rfl

@[simp]
-/
theorem coe_mk (s : Subsemiring A) (h) : (Subalgebra.mk (R := R) s h : Set A) = s :=
  rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: (s : Subsemiring A) (h) (x)
  statement: x in Subalgebra.mk (R := R) s h ↔ x in s
  proof: .rfl

中文:
定理 mem_mk
  条件: (s : Subsemiring A) (h) (x)
  结论: x in Subalgebra.mk (R := R) s h ↔ x in s
  证明: .rfl
-/
theorem mem_mk (s : Subsemiring A) (h) (x) : x in Subalgebra.mk (R := R) s h ↔ x in s :=
  .rfl

/-- The actual `Subalgebra` obtained from an element of a type satisfying `SubsemiringClass` and
`SMulMemClass`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  body: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  algebraMap_mem' r :=
    Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)

中文:
定义 ofClass
  签名: {S R A : 类型} [CommSemiring R] [Semiring A] [Algebra R A]
  定义体: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  algebraMap_mem' r :=
    Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)
-/
def ofClass {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [SetLike S A] [SubsemiringClass S A] [SMulMemClass S R A] (s : S) :
    Subalgebra R A where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  algebraMap_mem' r :=
    Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)

instance (priority := 100) : CanLift (Set A) (Subalgebra R A) (↑)
    (fun s => (forall {x y}, x in s -> y in s -> x + y in s) ∧
      (forall {x y}, x in s -> y in s -> x * y in s) ∧ forall (r : R), algebraMap R A r in s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := by simpa using h.2.2 0
        add_mem' := h.1
        one_mem' := by simpa using h.2.2 1
        mul_mem' := h.2.1
        algebraMap_mem' := h.2.2 },
      rfl ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubsemiringClass (Subalgebra R A) A
  body: add_mem (s := s.toSubsemiring)
  mul_mem {s} := mul_mem (s := s.toSubsemiring)
  one_mem {s} := one_mem s.toSubsemiring
  zero_mem {s} := zero_mem s.toSubsemiring

@[simp]

中文:
实例 :
  签名: SubsemiringClass (Subalgebra R A) A
  定义体: add_mem (s := s.toSubsemiring)
  mul_mem {s} := mul_mem (s := s.toSubsemiring)
  one_mem {s} := one_mem s.toSubsemiring
  zero_mem {s} := zero_mem s.toSubsemiring

@[simp]

Depends on / 依赖: add_mem, s.toSubsemiring, toSubsemiring
-/
instance : SubsemiringClass (Subalgebra R A) A where
  add_mem {s} := add_mem (s := s.toSubsemiring)
  mul_mem {s} := mul_mem (s := s.toSubsemiring)
  one_mem {s} := one_mem s.toSubsemiring
  zero_mem {s} := zero_mem s.toSubsemiring

@[simp]
/--
theorem `mem_toSubsemiring` / 定理 `mem_toSubsemiring`

English:
theorem mem_toSubsemiring
  given: {S : Subalgebra R A} {x}
  statement: x in S.toSubsemiring ↔ x in S
  proof: Iff.rfl

中文:
定理 mem_toSubsemiring
  条件: {S : Subalgebra R A} {x}
  结论: x in S.toSubsemiring ↔ x in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubsemiring {S : Subalgebra R A} {x} : x in S.toSubsemiring ↔ x in S :=
  Iff.rfl

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : Subalgebra R A} {x : A}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

@[ext]

中文:
定理 mem_carrier
  条件: {s : Subalgebra R A} {x : A}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

@[ext]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : Subalgebra R A} {x : A} : x in s.carrier ↔ x in s :=
  Iff.rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

@[simp]

中文:
定理 ext
  条件: {S T : Subalgebra R A} (h : 对任意 x : A, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

@[simp]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x in T) : S = T :=
  SetLike.ext h

@[simp]
/--
theorem `coe_toSubsemiring` / 定理 `coe_toSubsemiring`

English:
theorem coe_toSubsemiring
  given: (S : Subalgebra R A)
  statement: (↑S.toSubsemiring : Set A) = S
  proof: rfl

中文:
定理 coe_toSubsemiring
  条件: (S : Subalgebra R A)
  结论: (↑S.toSubsemiring : Set A) = S
  证明: rfl
-/
theorem coe_toSubsemiring (S : Subalgebra R A) : (↑S.toSubsemiring : Set A) = S :=
  rfl

/--
theorem `toSubsemiring_injective` / 定理 `toSubsemiring_injective`

English:
theorem toSubsemiring_injective
  proof: fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]

中文:
定理 toSubsemiring_injective
  证明: fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]
-/
theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : Subalgebra R A -> Subsemiring A) := fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]

/--
theorem `toSubsemiring_inj` / 定理 `toSubsemiring_inj`

English:
theorem toSubsemiring_inj
  given: {S U : Subalgebra R A}
  statement: S.toSubsemiring = U.toSubsemiring ↔ S = U
  proof: toSubsemiring_injective.eq_iff

中文:
定理 toSubsemiring_inj
  条件: {S U : Subalgebra R A}
  结论: S.toSubsemiring = U.toSubsemiring ↔ S = U
  证明: toSubsemiring_injective.eq_iff

Depends on / 依赖: eq_iff, toSubsemiring_injective, toSubsemiring_injective.eq_iff
-/
theorem toSubsemiring_inj {S U : Subalgebra R A} : S.toSubsemiring = U.toSubsemiring ↔ S = U :=
  toSubsemiring_injective.eq_iff

/-- Copy of a subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps coe toSubsemiring]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : Subalgebra R A) (s : Set A) (hs : s = ↑S)
  body: { S.toSubsemiring.copy s hs with
    carrier := s
    algebraMap_mem' := hs.symm ▸ S.algebraMap_mem' }

中文:
定义 copy
  签名: (S : Subalgebra R A) (s : Set A) (hs : s = ↑S)
  定义体: { S.toSubsemiring.copy s hs with
    carrier := s
    algebraMap_mem' := hs.symm ▸ S.algebraMap_mem' }
-/
protected def copy (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : Subalgebra R A :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    algebraMap_mem' := hs.symm ▸ S.algebraMap_mem' }

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : Subalgebra R A) (s : Set A) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : Subalgebra R A) (s : Set A) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : Subalgebra R A) (s : Set A) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

variable (S : Subalgebra R A)

/--
Instance `instSMulMemClass` / 实例 `instSMulMemClass`

English:
instance instSMulMemClass
  signature: : SMulMemClass (Subalgebra R A) R A where
  body: (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem' r) hx

@[simp, aesop safe (rule_sets := [SetLike])]

中文:
实例 instSMulMemClass
  签名: : SMulMemClass (Subalgebra R A) R A where
  定义体: (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem' r) hx

@[simp, aesop safe (rule_sets := [SetLike])]

Depends on / 依赖: Algebra, Algebra.smul_def, S.algebraMap_mem, algebraMap_mem, mul_mem, smul_def
-/
instance instSMulMemClass : SMulMemClass (Subalgebra R A) R A where
  smul_mem {S} r x hx := (Algebra.smul_def r x).symm ▸ mul_mem (S.algebraMap_mem' r) hx

@[simp, aesop safe (rule_sets := [SetLike])]
/--
theorem `_root_.algebraMap_mem` / 定理 `_root_.algebraMap_mem`

English:
theorem _root_.algebraMap_mem
  statement: {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  proof: Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)

中文:
定理 _root_.algebraMap_mem
  结论: {S R A : 类型} [CommSemiring R] [Semiring A] [Algebra R A]
  证明: Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, SMulMemClass, SMulMemClass.smul_mem, algebraMap_eq_smul_one, one_mem, smul_mem
-/
theorem _root_.algebraMap_mem {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [SetLike S A] [OneMemClass S A] [SMulMemClass S R A] (s : S) (r : R) :
    algebraMap R A r in s :=
  Algebra.algebraMap_eq_smul_one (A := A) r ▸ SMulMemClass.smul_mem r (one_mem s)

/--
theorem `algebraMap_mem` / 定理 `algebraMap_mem`

English:
theorem algebraMap_mem
  given: (r : R)
  statement: algebraMap R A r in S
  proof: algebraMap_mem S r

中文:
定理 algebraMap_mem
  条件: (r : R)
  结论: algebraMap R A r in S
  证明: algebraMap_mem S r
-/
protected theorem algebraMap_mem (r : R) : algebraMap R A r in S :=
  algebraMap_mem S r

/--
theorem `rangeS_le` / 定理 `rangeS_le`

English:
theorem rangeS_le
  statement: (algebraMap R A).rangeS <= S.toSubsemiring
  proof: fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r

中文:
定理 rangeS_le
  结论: (algebraMap R A).rangeS <= S.toSubsemiring
  证明: fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r
-/
theorem rangeS_le : (algebraMap R A).rangeS <= S.toSubsemiring := fun _x ⟨r, hr⟩ =>
  hr ▸ S.algebraMap_mem r

/--
theorem `range_subset` / 定理 `range_subset`

English:
theorem range_subset
  statement: Set.range (algebraMap R A) subseteq S
  proof: fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r

中文:
定理 range_subset
  结论: Set.range (algebraMap R A) subseteq S
  证明: fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r

Depends on / 依赖: S.algebraMap_mem, algebraMap_mem
-/
theorem range_subset : Set.range (algebraMap R A) subseteq S := fun _x ⟨r, hr⟩ => hr ▸ S.algebraMap_mem r

/--
theorem `range_le` / 定理 `range_le`

English:
theorem range_le
  statement: Set.range (algebraMap R A) <= S
  proof: S.range_subset

中文:
定理 range_le
  结论: Set.range (algebraMap R A) <= S
  证明: S.range_subset

Depends on / 依赖: S.range_subset, range_subset
-/
theorem range_le : Set.range (algebraMap R A) <= S :=
  S.range_subset

/--
theorem `smul_mem` / 定理 `smul_mem`

English:
theorem smul_mem
  given: {x : A} (hx : x in S) (r : R)
  statement: r • x in S
  proof: SMulMemClass.smul_mem r hx

中文:
定理 smul_mem
  条件: {x : A} (hx : x in S) (r : R)
  结论: r • x in S
  证明: SMulMemClass.smul_mem r hx

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, e.symm, smul_mem
-/
theorem smul_mem {x : A} (hx : x in S) (r : R) : r • x in S :=
  SMulMemClass.smul_mem r hx

/--
theorem `one_mem` / 定理 `one_mem`

English:
theorem one_mem
  statement: (1 : A) in S
  proof: one_mem S

中文:
定理 one_mem
  结论: (1 : A) in S
  证明: one_mem S
-/
protected theorem one_mem : (1 : A) in S :=
  one_mem S

/--
theorem `mul_mem` / 定理 `mul_mem`

English:
theorem mul_mem
  given: {x y : A} (hx : x in S) (hy : y in S)
  statement: x * y in S
  proof: mul_mem hx hy

中文:
定理 mul_mem
  条件: {x y : A} (hx : x in S) (hy : y in S)
  结论: x * y in S
  证明: mul_mem hx hy
-/
protected theorem mul_mem {x y : A} (hx : x in S) (hy : y in S) : x * y in S :=
  mul_mem hx hy

/--
theorem `pow_mem` / 定理 `pow_mem`

English:
theorem pow_mem
  given: {x : A} (hx : x in S) (n : Nat)
  statement: x ^ n in S
  proof: pow_mem hx n

中文:
定理 pow_mem
  条件: {x : A} (hx : x in S) (n : 自然数)
  结论: x ^ n in S
  证明: pow_mem hx n
-/
protected theorem pow_mem {x : A} (hx : x in S) (n : Nat) : x ^ n in S :=
  pow_mem hx n

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : A) in S
  proof: zero_mem S

中文:
定理 zero_mem
  结论: (0 : A) in S
  证明: zero_mem S
-/
protected theorem zero_mem : (0 : A) in S :=
  zero_mem S

/--
theorem `add_mem` / 定理 `add_mem`

English:
theorem add_mem
  given: {x y : A} (hx : x in S) (hy : y in S)
  statement: x + y in S
  proof: add_mem hx hy

中文:
定理 add_mem
  条件: {x y : A} (hx : x in S) (hy : y in S)
  结论: x + y in S
  证明: add_mem hx hy
-/
protected theorem add_mem {x y : A} (hx : x in S) (hy : y in S) : x + y in S :=
  add_mem hx hy

/--
theorem `nsmul_mem` / 定理 `nsmul_mem`

English:
theorem nsmul_mem
  given: {x : A} (hx : x in S) (n : Nat)
  statement: n • x in S
  proof: nsmul_mem hx n

中文:
定理 nsmul_mem
  条件: {x : A} (hx : x in S) (n : 自然数)
  结论: n • x in S
  证明: nsmul_mem hx n
-/
protected theorem nsmul_mem {x : A} (hx : x in S) (n : Nat) : n • x in S :=
  nsmul_mem hx n

/--
theorem `natCast_mem` / 定理 `natCast_mem`

English:
theorem natCast_mem
  given: (n : Nat)
  statement: (n : A) in S
  proof: natCast_mem S n

中文:
定理 natCast_mem
  条件: (n : 自然数)
  结论: (n : A) in S
  证明: natCast_mem S n
-/
protected theorem natCast_mem (n : Nat) : (n : A) in S :=
  natCast_mem S n

/--
theorem `list_prod_mem` / 定理 `list_prod_mem`

English:
theorem list_prod_mem
  given: {L : List A} (h : forall x in L, x in S)
  statement: L.prod in S
  proof: list_prod_mem h

中文:
定理 list_prod_mem
  条件: {L : List A} (h : 对任意 x in L, x in S)
  结论: L.prod in S
  证明: list_prod_mem h
-/
protected theorem list_prod_mem {L : List A} (h : forall x in L, x in S) : L.prod in S :=
  list_prod_mem h

/--
theorem `list_sum_mem` / 定理 `list_sum_mem`

English:
theorem list_sum_mem
  given: {L : List A} (h : forall x in L, x in S)
  statement: L.sum in S
  proof: list_sum_mem h

中文:
定理 list_sum_mem
  条件: {L : List A} (h : 对任意 x in L, x in S)
  结论: L.sum in S
  证明: list_sum_mem h
-/
protected theorem list_sum_mem {L : List A} (h : forall x in L, x in S) : L.sum in S :=
  list_sum_mem h

/--
theorem `multiset_sum_mem` / 定理 `multiset_sum_mem`

English:
theorem multiset_sum_mem
  given: {m : Multiset A} (h : forall x in m, x in S)
  statement: m.sum in S
  proof: multiset_sum_mem m h

中文:
定理 multiset_sum_mem
  条件: {m : Multiset A} (h : 对任意 x in m, x in S)
  结论: m.sum in S
  证明: multiset_sum_mem m h
-/
protected theorem multiset_sum_mem {m : Multiset A} (h : forall x in m, x in S) : m.sum in S :=
  multiset_sum_mem m h

/--
theorem `sum_mem` / 定理 `sum_mem`

English:
theorem sum_mem
  given: {ι : Type w} {t : Finset ι} {f : ι -> A} (h : forall x in t, f x in S)
  proof: sum_mem h

中文:
定理 sum_mem
  条件: {ι : Type w} {t : Finset ι} {f : ι -> A} (h : 对任意 x in t, f x in S)
  证明: sum_mem h
-/
protected theorem sum_mem {ι : Type w} {t : Finset ι} {f : ι -> A} (h : forall x in t, f x in S) :
    (∑ x in t, f x) in S :=
  sum_mem h

/--
theorem `multiset_prod_mem` / 定理 `multiset_prod_mem`

English:
theorem multiset_prod_mem
  statement: {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A]
  proof: multiset_prod_mem m h

中文:
定理 multiset_prod_mem
  结论: {R : 类型u} {A : 类型v} [CommSemiring R] [CommSemiring A]
  证明: multiset_prod_mem m h
-/
protected theorem multiset_prod_mem {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (S : Subalgebra R A) {m : Multiset A} (h : forall x in m, x in S) : m.prod in S :=
  multiset_prod_mem m h

/--
theorem `prod_mem` / 定理 `prod_mem`

English:
theorem prod_mem
  statement: {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
  proof: prod_mem h

中文:
定理 prod_mem
  结论: {R : 类型u} {A : 类型v} [CommSemiring R] [CommSemiring A] [Algebra R A]
  证明: prod_mem h
-/
protected theorem prod_mem {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) {ι : Type w} {t : Finset ι} {f : ι -> A} (h : forall x in t, f x in S) :
    (∏ x in t, f x) in S :=
  prod_mem h

/-- Turn a `Subalgebra` into a `NonUnitalSubalgebra` by forgetting that it contains `1`. -/
@[reducible]
/--
Definition of `toNonUnitalSubalgebra` / `toNonUnitalSubalgebra` 的定义

English:
definition toNonUnitalSubalgebra
  signature: (S : Subalgebra R A)
  body: S
  smul_mem' r _x hx := S.smul_mem hx r

中文:
定义 toNonUnitalSubalgebra
  签名: (S : Subalgebra R A)
  定义体: S
  smul_mem' r _x hx := S.smul_mem hx r
-/
def toNonUnitalSubalgebra (S : Subalgebra R A) : NonUnitalSubalgebra R A where
  __ := S
  smul_mem' r _x hx := S.smul_mem hx r

/--
lemma `one_mem_toNonUnitalSubalgebra` / 引理 `one_mem_toNonUnitalSubalgebra`

English:
lemma one_mem_toNonUnitalSubalgebra
  given: (S : Subalgebra R A)
  statement: (1 : A) in S.toNonUnitalSubalgebra
  proof: S.one_mem

@[simp]

中文:
引理 one_mem_toNonUnitalSubalgebra
  条件: (S : Subalgebra R A)
  结论: (1 : A) in S.toNonUnitalSubalgebra
  证明: S.one_mem

@[simp]

Depends on / 依赖: S.one_mem, one_mem
-/
lemma one_mem_toNonUnitalSubalgebra (S : Subalgebra R A) : (1 : A) in S.toNonUnitalSubalgebra :=
  S.one_mem

@[simp]
/--
lemma `mem_toNonUnitalSubalgebra` / 引理 `mem_toNonUnitalSubalgebra`

English:
lemma mem_toNonUnitalSubalgebra
  given: {S : Subalgebra R A} {x : A}
  proof: Iff.rfl

中文:
引理 mem_toNonUnitalSubalgebra
  条件: {S : Subalgebra R A} {x : A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_toNonUnitalSubalgebra {S : Subalgebra R A} {x : A} :
    x in S.toNonUnitalSubalgebra ↔ x in S :=
  Iff.rfl

/--
lemma `toNonUnitalSubalgebra_injective` / 引理 `toNonUnitalSubalgebra_injective`

English:
lemma toNonUnitalSubalgebra_injective
  statement: Function.Injective
  proof: fun _ _ => by simp [SetLike.ext_iff]

中文:
引理 toNonUnitalSubalgebra_injective
  结论: Function.Injective
  证明: fun _ _ => by simp [SetLike.ext_iff]

Depends on / 依赖: SetLike, SetLike.ext_iff, ext_iff
-/
lemma toNonUnitalSubalgebra_injective : Function.Injective
    (toNonUnitalSubalgebra : Subalgebra R A -> NonUnitalSubalgebra R A) :=
  fun _ _ => by simp [SetLike.ext_iff]

/--
lemma `toNonUnitalSubalgebra_inj` / 引理 `toNonUnitalSubalgebra_inj`

English:
lemma toNonUnitalSubalgebra_inj
  given: {S U : Subalgebra R A}
  proof: toNonUnitalSubalgebra_injective.eq_iff

中文:
引理 toNonUnitalSubalgebra_inj
  条件: {S U : Subalgebra R A}
  证明: toNonUnitalSubalgebra_injective.eq_iff

Depends on / 依赖: eq_iff, toNonUnitalSubalgebra_injective, toNonUnitalSubalgebra_injective.eq_iff
-/
lemma toNonUnitalSubalgebra_inj {S U : Subalgebra R A} :
    S.toNonUnitalSubalgebra = U.toNonUnitalSubalgebra ↔ S = U :=
  toNonUnitalSubalgebra_injective.eq_iff

instance {R A : Type*} [CommRing R] [Ring A] [Algebra R A] : SubringClass (Subalgebra R A) A :=
  { Subalgebra.instSubsemiringClass with
    neg_mem := fun {S x} hx => neg_one_smul R x ▸ S.smul_mem hx _ }

/--
theorem `neg_mem` / 定理 `neg_mem`

English:
theorem neg_mem
  statement: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: neg_mem hx

中文:
定理 neg_mem
  结论: {R : 类型u} {A : 类型v} [CommRing R] [Ring A] [Algebra R A]
  证明: neg_mem hx
-/
protected theorem neg_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x : A} (hx : x in S) : -x in S :=
  neg_mem hx

/--
theorem `sub_mem` / 定理 `sub_mem`

English:
theorem sub_mem
  statement: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: sub_mem hx hy

中文:
定理 sub_mem
  结论: {R : 类型u} {A : 类型v} [CommRing R] [Ring A] [Algebra R A]
  证明: sub_mem hx hy
-/
protected theorem sub_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x y : A} (hx : x in S) (hy : y in S) : x - y in S :=
  sub_mem hx hy

/--
theorem `zsmul_mem` / 定理 `zsmul_mem`

English:
theorem zsmul_mem
  statement: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: zsmul_mem hx n

中文:
定理 zsmul_mem
  结论: {R : 类型u} {A : 类型v} [CommRing R] [Ring A] [Algebra R A]
  证明: zsmul_mem hx n
-/
protected theorem zsmul_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) {x : A} (hx : x in S) (n : Int) : n • x in S :=
  zsmul_mem hx n

/--
theorem `intCast_mem` / 定理 `intCast_mem`

English:
theorem intCast_mem
  statement: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: intCast_mem S n

中文:
定理 intCast_mem
  结论: {R : 类型u} {A : 类型v} [CommRing R] [Ring A] [Algebra R A]
  证明: intCast_mem S n
-/
protected theorem intCast_mem {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) (n : Int) : (n : A) in S :=
  intCast_mem S n

/-- The projection from a subalgebra of `A` to an additive submonoid of `A`. -/
@[reducible]
/--
Definition of `toAddSubmonoid` / `toAddSubmonoid` 的定义

English:
definition toAddSubmonoid
  signature: {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
  body: S.toSubsemiring.toAddSubmonoid

中文:
定义 toAddSubmonoid
  签名: {R : 类型u} {A : 类型v} [CommSemiring R] [Semiring A] [Algebra R A]
  定义体: S.toSubsemiring.toAddSubmonoid

Depends on / 依赖: S.toSubsemiring.toAddSubmonoid, toAddSubmonoid, toSubsemiring
-/
def toAddSubmonoid {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R A) : AddSubmonoid A :=
  S.toSubsemiring.toAddSubmonoid

/-- A subalgebra over a ring is also a `Subring`. -/
@[reducible]
/--
Definition of `toSubring` / `toSubring` 的定义

English:
definition toSubring
  signature: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A)
  body: { S.toSubsemiring with neg_mem' := S.neg_mem }

中文:
定义 toSubring
  签名: {R : 类型u} {A : 类型v} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A)
  定义体: { S.toSubsemiring with neg_mem' := S.neg_mem }

Depends on / 依赖: S.neg_mem, S.toSubsemiring, neg_mem, toSubsemiring
-/
def toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    Subring A :=
  { S.toSubsemiring with neg_mem' := S.neg_mem }

/--
theorem `mem_toSubring` / 定理 `mem_toSubring`

English:
theorem mem_toSubring
  statement: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: Iff.rfl

中文:
定理 mem_toSubring
  结论: {R : 类型u} {A : 类型v} [CommRing R] [Ring A] [Algebra R A]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} {x} : x in S.toSubring ↔ x in S :=
  Iff.rfl

/--
theorem `coe_toSubring` / 定理 `coe_toSubring`

English:
theorem coe_toSubring
  statement: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: rfl

中文:
定理 coe_toSubring
  结论: {R : 类型u} {A : 类型v} [CommRing R] [Ring A] [Algebra R A]
  证明: rfl
-/
theorem coe_toSubring {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (S : Subalgebra R A) : (↑S.toSubring : Set A) = S :=
  rfl

/--
theorem `toSubring_injective` / 定理 `toSubring_injective`

English:
theorem toSubring_injective
  given: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: fun S T h =>
  ext fun x => by rw [← mem_toSubring, ← mem_toSubring, h]

中文:
定理 toSubring_injective
  条件: {R : 类型u} {A : 类型v} [CommRing R] [Ring A] [Algebra R A]
  证明: fun S T h =>
  ext fun x => by rw [← mem_toSubring, ← mem_toSubring, h]
-/
theorem toSubring_injective {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] :
    Function.Injective (toSubring : Subalgebra R A -> Subring A) := fun S T h =>
  ext fun x => by rw [← mem_toSubring, ← mem_toSubring, h]

/--
theorem `toSubring_inj` / 定理 `toSubring_inj`

English:
theorem toSubring_inj
  statement: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: toSubring_injective.eq_iff

中文:
定理 toSubring_inj
  结论: {R : 类型u} {A : 类型v} [CommRing R] [Ring A] [Algebra R A]
  证明: toSubring_injective.eq_iff

Depends on / 依赖: eq_iff, toSubring_injective, toSubring_injective.eq_iff
-/
theorem toSubring_inj {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S U : Subalgebra R A} : S.toSubring = U.toSubring ↔ S = U :=
  toSubring_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited S
  body: ⟨(0 : S.toSubsemiring)⟩

中文:
实例 :
  签名: Inhabited S
  定义体: ⟨(0 : S.toSubsemiring)⟩

Depends on / 依赖: S.toSubsemiring, toSubsemiring
-/
instance : Inhabited S :=
  ⟨(0 : S.toSubsemiring)⟩

section



/--
Instance `toSemiring` / 实例 `toSemiring`

English:
instance toSemiring
  signature: {R A} [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgebra R A)
  body: S.toSubsemiring.toSemiring

中文:
实例 toSemiring
  签名: {R A} [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgebra R A)
  定义体: S.toSubsemiring.toSemiring

Depends on / 依赖: S.toSubsemiring.toSemiring, toSemiring, toSubsemiring
-/
instance toSemiring {R A} [CommSemiring R] [Semiring A] [Algebra R A] (S : Subalgebra R A) :
    Semiring S :=
  S.toSubsemiring.toSemiring

/--
Instance `toCommSemiring` / 实例 `toCommSemiring`

English:
instance toCommSemiring
  signature: {R A} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A)
  body: S.toSubsemiring.toCommSemiring

中文:
实例 toCommSemiring
  签名: {R A} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A)
  定义体: S.toSubsemiring.toCommSemiring

Depends on / 依赖: S.toSubsemiring.toCommSemiring, toCommSemiring, toSubsemiring
-/
instance toCommSemiring {R A} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A) :
    CommSemiring S :=
  S.toSubsemiring.toCommSemiring

/--
Instance `toRing` / 实例 `toRing`

English:
instance toRing
  signature: {R A} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A)
  body: S.toSubring.toRing

中文:
实例 toRing
  签名: {R A} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A)
  定义体: S.toSubring.toRing

Depends on / 依赖: S.toSubring.toRing, toRing, toSubring
-/
instance toRing {R A} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) : Ring S :=
  S.toSubring.toRing

/--
Instance `toCommRing` / 实例 `toCommRing`

English:
instance toCommRing
  signature: {R A} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
  body: S.toSubring.toCommRing

中文:
实例 toCommRing
  签名: {R A} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
  定义体: S.toSubring.toCommRing

Depends on / 依赖: S.toSubring.toCommRing, toCommRing, toSubring
-/
instance toCommRing {R A} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) :
    CommRing S :=
  S.toSubring.toCommRing

end

/-- The forgetful map from `Subalgebra` to `Submodule` as an `OrderEmbedding` -/
@[instance_reducible] -- Not `@[reducible]` because it is an order embedding rather than a function.
/--
Definition of `toSubmodule` / `toSubmodule` 的定义

English:
definition toSubmodule
  signature: : Subalgebra R A ↪o Submodule R A where
  body: { toFun := fun S =>
        { S with
          carrier := S
          smul_mem' := fun c {x} hx =>
            (Algebra.smul_def c x).symm ▸ mul_mem (S.range_le ⟨c, rfl⟩) hx }
      inj' := fun _ _ h => ext fun x => SetLike.ext_iff.mp h x }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike

中文:
定义 toSubmodule
  签名: : Subalgebra R A ↪o Submodule R A where
  定义体: { toFun := fun S =>
        { S with
          carrier := S
          smul_mem' := fun c {x} hx =>
            (Algebra.smul_def c x).symm ▸ mul_mem (S.range_le ⟨c, rfl⟩) hx }
      inj' := fun _ _ h => ext fun x => SetLike.ext_iff.mp h x }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike

Depends on / 依赖: Algebra, Algebra.smul_def, S.range_le, SetLike, SetLike.coe_subset_coe, SetLike.coe_subset_coe.symm.trans, SetLike.ext_iff.mp, carrier, coe_subset_coe, ext_iff, map_rel_iff, mul_mem, range_le, smul_def, smul_mem
-/
def toSubmodule : Subalgebra R A ↪o Submodule R A where
  toEmbedding :=
    { toFun := fun S =>
        { S with
          carrier := S
          smul_mem' := fun c {x} hx =>
            (Algebra.smul_def c x).symm ▸ mul_mem (S.range_le ⟨c, rfl⟩) hx }
      inj' := fun _ _ h => ext fun x => SetLike.ext_iff.mp h x }
  map_rel_iff' := SetLike.coe_subset_coe.symm.trans SetLike.coe_subset_coe

/-! TODO: bundle other forgetful maps between algebraic substructures, e.g.
  `toSubsemiring` and `toSubring` in this file. -/

@[simp]
/--
theorem `mem_toSubmodule` / 定理 `mem_toSubmodule`

English:
theorem mem_toSubmodule
  given: {x}
  statement: x in (toSubmodule S) ↔ x in S
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toSubmodule
  条件: {x}
  结论: x in (toSubmodule S) ↔ x in S
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubmodule {x} : x in (toSubmodule S) ↔ x in S := Iff.rfl

@[simp]
/--
theorem `coe_toSubmodule` / 定理 `coe_toSubmodule`

English:
theorem coe_toSubmodule
  given: (S : Subalgebra R A)
  statement: (toSubmodule S : Set A) = S
  proof: rfl

中文:
定理 coe_toSubmodule
  条件: (S : Subalgebra R A)
  结论: (toSubmodule S : Set A) = S
  证明: rfl
-/
theorem coe_toSubmodule (S : Subalgebra R A) : (toSubmodule S : Set A) = S := rfl

/--
theorem `toSubmodule_injective` / 定理 `toSubmodule_injective`

English:
theorem toSubmodule_injective
  statement: Function.Injective (toSubmodule : Subalgebra R A -> Submodule R A)
  proof: fun _S₁ _S₂ h => SetLike.ext (SetLike.ext_iff.mp h :)

中文:
定理 toSubmodule_injective
  结论: Function.Injective (toSubmodule : Subalgebra R A -> Submodule R A)
  证明: fun _S₁ _S₂ h => SetLike.ext (SetLike.ext_iff.mp h :)

Depends on / 依赖: SetLike, SetLike.ext, SetLike.ext_iff.mp, ext_iff
-/
theorem toSubmodule_injective : Function.Injective (toSubmodule : Subalgebra R A -> Submodule R A) :=
  fun _S₁ _S₂ h => SetLike.ext (SetLike.ext_iff.mp h :)

section

/-! `Subalgebra`s inherit structure from their `Submodule` coercions. -/


instance (priority := low) module' [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] :
    Module R' S :=
  inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R S
  body: inferInstance

中文:
实例 :
  签名: Module R S
  定义体: inferInstance
-/
instance : Module R S :=
  inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : IsScalarTower R' R S
  body: inferInstance

中文:
实例 [Semiring
  签名: R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : IsScalarTower R' R S
  定义体: inferInstance
-/
instance [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] : IsScalarTower R' R S :=
  inferInstance

/-- More general form of `Subalgebra.algebra`.

This instance should have low priority since it is slow to fail:
before failing, it will cause a search through all `SMul R' R` instances,
which can quickly get expensive.
-/
instance (priority := 500) algebra' [CommSemiring R'] [SMul R' R] [Algebra R' A]
    [IsScalarTower R' R A] :
    Algebra R' S where
  algebraMap := (algebraMap R' A).codRestrict S fun x => by
    rw [Algebra.algebraMap_eq_smul_one]; rw [← smul_one_smul R x (1 : A)]; rw [←
      Algebra.algebraMap_eq_smul_one]
    exact algebraMap_mem S _
commutes' := fun _ _ => Subtype.ext Algebra.commutes _ _
smul_def' := fun _ _ => Subtype.ext Algebra.smul_def _ _

/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: : Algebra R S
  body: S.algebra'

@[simp]

中文:
实例 algebra
  签名: : Algebra R S
  定义体: S.algebra'

@[simp]

Depends on / 依赖: S.algebra, algebra
-/
instance algebra : Algebra R S := S.algebra'

@[simp]
/--
theorem `mk_algebraMap` / 定理 `mk_algebraMap`

English:
theorem mk_algebraMap
  given: {S : Subalgebra R A} (r : R) (hr : algebraMap R A r in S)
  proof: rfl

中文:
定理 mk_algebraMap
  条件: {S : Subalgebra R A} (r : R) (hr : algebraMap R A r in S)
  证明: rfl
-/
theorem mk_algebraMap {S : Subalgebra R A} (r : R) (hr : algebraMap R A r in S) :
    ⟨algebraMap R A r, hr⟩ = algebraMap R S r := rfl

end

/--
Instance `instIsTorsionFree` / 实例 `instIsTorsionFree`

English:
instance instIsTorsionFree
  signature: [IsTorsionFree R A]
  body: S.toSubmodule.instIsTorsionFree

中文:
实例 instIsTorsionFree
  签名: [IsTorsionFree R A]
  定义体: S.toSubmodule.instIsTorsionFree

Depends on / 依赖: S.toSubmodule.instIsTorsionFree, instIsTorsionFree, toSubmodule
-/
instance instIsTorsionFree [IsTorsionFree R A] : IsTorsionFree R S :=
  S.toSubmodule.instIsTorsionFree

/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : S)
  statement: (↑(x + y) : A) = ↑x + ↑y
  proof: rfl

中文:
定理 coe_add
  条件: (x y : S)
  结论: (↑(x + y) : A) = ↑x + ↑y
  证明: rfl
-/
protected theorem coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y := rfl

/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : S)
  statement: (↑(x * y) : A) = ↑x * ↑y
  proof: rfl

中文:
定理 coe_mul
  条件: (x y : S)
  结论: (↑(x * y) : A) = ↑x * ↑y
  证明: rfl
-/
protected theorem coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y := rfl

/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : S) : A) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ((0 : S) : A) = 0
  证明: rfl
-/
protected theorem coe_zero : ((0 : S) : A) = 0 := rfl

/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : S) : A) = 1
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : S) : A) = 1
  证明: rfl
-/
protected theorem coe_one : ((1 : S) : A) = 1 := rfl

/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: rfl

中文:
定理 coe_neg
  结论: {R : 类型u} {A : 类型v} [CommRing R] [Ring A] [Algebra R A]
  证明: rfl
-/
protected theorem coe_neg {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} (x : S) : (↑(-x) : A) = -↑x := rfl

/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sub
  结论: {R : 类型u} {A : 类型v} [CommRing R] [Ring A] [Algebra R A]
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_sub {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {S : Subalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y := rfl

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_smul
  条件: [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_smul [SMul R' R] [SMul R' A] [IsScalarTower R' R A] (r : R') (x : S) :
    (↑(r • x) : A) = r • (x : A) := rfl

@[simp, norm_cast]
/--
theorem `coe_algebraMap` / 定理 `coe_algebraMap`

English:
theorem coe_algebraMap
  statement: [CommSemiring R'] [SMul R' R] [Algebra R' A] [IsScalarTower R' R A]
  proof: rfl

中文:
定理 coe_algebraMap
  结论: [CommSemiring R'] [SMul R' R] [Algebra R' A] [IsScalarTower R' R A]
  证明: rfl
-/
theorem coe_algebraMap [CommSemiring R'] [SMul R' R] [Algebra R' A] [IsScalarTower R' R A]
    (r : R') : ↑(algebraMap R' S r) = algebraMap R' A r := rfl

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (x : S) (n : Nat)
  statement: (↑(x ^ n) : A) = (x : A) ^ n
  proof: SubmonoidClass.coe_pow x n

中文:
定理 coe_pow
  条件: (x : S) (n : 自然数)
  结论: (↑(x ^ n) : A) = (x : A) ^ n
  证明: SubmonoidClass.coe_pow x n
-/
protected theorem coe_pow (x : S) (n : Nat) : (↑(x ^ n) : A) = (x : A) ^ n :=
  SubmonoidClass.coe_pow x n

/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  given: {x : S}
  statement: (x : A) = 0 ↔ x = 0
  proof: ZeroMemClass.coe_eq_zero

中文:
定理 coe_eq_zero
  条件: {x : S}
  结论: (x : A) = 0 ↔ x = 0
  证明: ZeroMemClass.coe_eq_zero
-/
protected theorem coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
  ZeroMemClass.coe_eq_zero

/--
theorem `coe_eq_one` / 定理 `coe_eq_one`

English:
theorem coe_eq_one
  given: {x : S}
  statement: (x : A) = 1 ↔ x = 1
  proof: OneMemClass.coe_eq_one

中文:
定理 coe_eq_one
  条件: {x : S}
  结论: (x : A) = 1 ↔ x = 1
  证明: OneMemClass.coe_eq_one
-/
protected theorem coe_eq_one {x : S} : (x : A) = 1 ↔ x = 1 :=
  OneMemClass.coe_eq_one

-- todo: standardize on the names these morphisms
-- compare with submodule.subtype
/--
Definition of `val` / `val` 的定义

English:
definition val
  signature: : S ->ₐ[R] A
  body: { toFun := ((↑) : S -> A)
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl }

@[simp]

中文:
定义 val
  签名: : S ->ₐ[R] A
  定义体: { toFun := ((↑) : S -> A)
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl }

@[simp]

Depends on / 依赖: commutes, map_add, map_mul, map_one, map_zero
-/
def val : S ->ₐ[R] A :=
  { toFun := ((↑) : S -> A)
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl
    commutes' := fun _ => rfl }

@[simp]
/--
theorem `coe_val` / 定理 `coe_val`

English:
theorem coe_val
  statement: (S.val : S -> A) = ((↑) : S -> A)
  proof: rfl

中文:
定理 coe_val
  结论: (S.val : S -> A) = ((↑) : S -> A)
  证明: rfl
-/
theorem coe_val : (S.val : S -> A) = ((↑) : S -> A) := rfl

/--
theorem `val_apply` / 定理 `val_apply`

English:
theorem val_apply
  given: (x : S)
  statement: S.val x = (x : A)
  proof: rfl

@[simp]

中文:
定理 val_apply
  条件: (x : S)
  结论: S.val x = (x : A)
  证明: rfl

@[simp]
-/
theorem val_apply (x : S) : S.val x = (x : A) := rfl

@[simp]
/--
theorem `toSubsemiring_subtype` / 定理 `toSubsemiring_subtype`

English:
theorem toSubsemiring_subtype
  statement: S.toSubsemiring.subtype = (S.val : S ->+* A)
  proof: rfl

@[simp]

中文:
定理 toSubsemiring_subtype
  结论: S.toSubsemiring.subtype = (S.val : S ->+* A)
  证明: rfl

@[simp]
-/
theorem toSubsemiring_subtype : S.toSubsemiring.subtype = (S.val : S ->+* A) := rfl

@[simp]
/--
theorem `toSubring_subtype` / 定理 `toSubring_subtype`

English:
theorem toSubring_subtype
  given: {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A)
  proof: rfl

中文:
定理 toSubring_subtype
  条件: {R A : 类型} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A)
  证明: rfl
-/
theorem toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    S.toSubring.subtype = (S.val : S ->+* A) := rfl

/--
Definition of `toSubmoduleEquiv` / `toSubmoduleEquiv` 的定义

English:
definition toSubmoduleEquiv
  signature: (S : Subalgebra R A)
  body: LinearEquiv.ofEq _ _ rfl

中文:
定义 toSubmoduleEquiv
  签名: (S : Subalgebra R A)
  定义体: LinearEquiv.ofEq _ _ rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.ofEq
-/
def toSubmoduleEquiv (S : Subalgebra R A) : toSubmodule S ≃ₗ[R] S :=
  LinearEquiv.ofEq _ _ rfl

/-- Transport a subalgebra via an algebra homomorphism. -/
@[simps! coe toSubsemiring]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : A ->ₐ[R] B) (S : Subalgebra R A)
  body: { S.toSubsemiring.map (f : A ->+* B) with
    algebraMap_mem' := fun r => f.commutes r ▸ Set.mem_image_of_mem _ (S.algebraMap_mem r) }

@[gcongr]

中文:
定义 map
  签名: (f : A ->ₐ[R] B) (S : Subalgebra R A)
  定义体: { S.toSubsemiring.map (f : A ->+* B) with
    algebraMap_mem' := fun r => f.commutes r ▸ Set.mem_image_of_mem _ (S.algebraMap_mem r) }

@[gcongr]

Depends on / 依赖: S.algebraMap_mem, S.toSubsemiring.map, Set.mem_image_of_mem, algebraMap_mem, commutes, f.commutes, mem_image_of_mem, toSubsemiring
-/
def map (f : A ->ₐ[R] B) (S : Subalgebra R A) : Subalgebra R B :=
  { S.toSubsemiring.map (f : A ->+* B) with
    algebraMap_mem' := fun r => f.commutes r ▸ Set.mem_image_of_mem _ (S.algebraMap_mem r) }

@[gcongr]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: {S₁ S₂ : Subalgebra R A} {f : A ->ₐ[R] B}
  statement: S₁ <= S₂ -> S₁.map f <= S₂.map f
  proof: Set.image_mono

中文:
定理 map_mono
  条件: {S₁ S₂ : Subalgebra R A} {f : A ->ₐ[R] B}
  结论: S₁ <= S₂ -> S₁.map f <= S₂.map f
  证明: Set.image_mono

Depends on / 依赖: Set.image_mono, image_mono
-/
theorem map_mono {S₁ S₂ : Subalgebra R A} {f : A ->ₐ[R] B} : S₁ <= S₂ -> S₁.map f <= S₂.map f :=
  Set.image_mono

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : A ->ₐ[R] B} (hf : Function.Injective f)
  statement: Function.Injective (map f)
  proof: fun _S₁ _S₂ ih =>
ext Set.ext_iff.1 Set.image_injective.2 hf Set.ext SetLike.ext_iff.mp ih

@[simp]

中文:
定理 map_injective
  条件: {f : A ->ₐ[R] B} (hf : Function.Injective f)
  结论: Function.Injective (map f)
  证明: fun _S₁ _S₂ ih =>
ext Set.ext_iff.1 Set.image_injective.2 hf Set.ext SetLike.ext_iff.mp ih

@[simp]

Depends on / 依赖: Set.ext, Set.ext_iff, Set.image_injective, SetLike, SetLike.ext_iff.mp, ext_iff, image_injective
-/
theorem map_injective {f : A ->ₐ[R] B} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun _S₁ _S₂ ih =>
ext Set.ext_iff.1 Set.image_injective.2 hf Set.ext SetLike.ext_iff.mp ih

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (S : Subalgebra R A)
  statement: S.map (AlgHom.id R A) = S
  proof: SetLike.coe_injective Set.image_id _

中文:
定理 map_id
  条件: (S : Subalgebra R A)
  结论: S.map (AlgHom.id R A) = S
  证明: SetLike.coe_injective Set.image_id _

Depends on / 依赖: Set.image_id, SetLike, SetLike.coe_injective, coe_injective, image_id
-/
theorem map_id (S : Subalgebra R A) : S.map (AlgHom.id R A) = S :=
SetLike.coe_injective Set.image_id _

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (S : Subalgebra R A) (g : B ->ₐ[R] C) (f : A ->ₐ[R] B)
  proof: SetLike.coe_injective Set.image_image _ _ _

@[simp]

中文:
定理 map_map
  条件: (S : Subalgebra R A) (g : B ->ₐ[R] C) (f : A ->ₐ[R] B)
  证明: SetLike.coe_injective Set.image_image _ _ _

@[simp]

Depends on / 依赖: Set.image_image, SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (S : Subalgebra R A) (g : B ->ₐ[R] C) (f : A ->ₐ[R] B) :
    (S.map f).map g = S.map (g.comp f) :=
SetLike.coe_injective Set.image_image _ _ _

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {S : Subalgebra R A} {f : A ->ₐ[R] B} {y : B}
  statement: y in map f S ↔ exists x in S, f x = y
  proof: Subsemiring.mem_map

中文:
定理 mem_map
  条件: {S : Subalgebra R A} {f : A ->ₐ[R] B} {y : B}
  结论: y in map f S ↔ 存在 x in S, f x = y
  证明: Subsemiring.mem_map

Depends on / 依赖: Subsemiring, Subsemiring.mem_map, mem_map
-/
theorem mem_map {S : Subalgebra R A} {f : A ->ₐ[R] B} {y : B} : y in map f S ↔ exists x in S, f x = y :=
  Subsemiring.mem_map

/--
theorem `map_toSubmodule` / 定理 `map_toSubmodule`

English:
theorem map_toSubmodule
  given: {S : Subalgebra R A} {f : A ->ₐ[R] B}
  proof: SetLike.coe_injective rfl

中文:
定理 map_toSubmodule
  条件: {S : Subalgebra R A} {f : A ->ₐ[R] B}
  证明: SetLike.coe_injective rfl

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem map_toSubmodule {S : Subalgebra R A} {f : A ->ₐ[R] B} :
    (toSubmodule <| S.map f) = S.toSubmodule.map f.toLinearMap :=
  SetLike.coe_injective rfl

/-- Preimage of a subalgebra under an algebra homomorphism. -/
@[simps! coe toSubsemiring]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : A ->ₐ[R] B) (S : Subalgebra R B)
  body: { S.toSubsemiring.comap (f : A ->+* B) with
    algebraMap_mem' := fun r =>
      show f (algebraMap R A r) in S from (f.commutes r).symm ▸ S.algebraMap_mem r }

中文:
定义 comap
  签名: (f : A ->ₐ[R] B) (S : Subalgebra R B)
  定义体: { S.toSubsemiring.comap (f : A ->+* B) with
    algebraMap_mem' := fun r =>
      show f (algebraMap R A r) in S from (f.commutes r).symm ▸ S.algebraMap_mem r }

Depends on / 依赖: S.algebraMap_mem, S.toSubsemiring.comap, algebraMap, algebraMap_mem, commutes, f.commutes, toSubsemiring
-/
def comap (f : A ->ₐ[R] B) (S : Subalgebra R B) : Subalgebra R A :=
  { S.toSubsemiring.comap (f : A ->+* B) with
    algebraMap_mem' := fun r =>
      show f (algebraMap R A r) in S from (f.commutes r).symm ▸ S.algebraMap_mem r }

attribute [norm_cast] coe_comap

/--
theorem `map_le` / 定理 `map_le`

English:
theorem map_le
  given: {S : Subalgebra R A} {f : A ->ₐ[R] B} {U : Subalgebra R B}
  proof: Set.image_subset_iff

中文:
定理 map_le
  条件: {S : Subalgebra R A} {f : A ->ₐ[R] B} {U : Subalgebra R B}
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff
-/
theorem map_le {S : Subalgebra R A} {f : A ->ₐ[R] B} {U : Subalgebra R B} :
    map f S <= U ↔ S <= comap f U :=
  Set.image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : A ->ₐ[R] B)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _S _U => map_le

@[simp]

中文:
定理 gc_map_comap
  条件: (f : A ->ₐ[R] B)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _S _U => map_le

@[simp]

Depends on / 依赖: map_le
-/
theorem gc_map_comap (f : A ->ₐ[R] B) : GaloisConnection (map f) (comap f) := fun _S _U => map_le

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: (S : Subalgebra R B) (f : A ->ₐ[R] B) (x : A)
  statement: x in S.comap f ↔ f x in S
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: (S : Subalgebra R B) (f : A ->ₐ[R] B) (x : A)
  结论: x in S.comap f ↔ f x in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap (S : Subalgebra R B) (f : A ->ₐ[R] B) (x : A) : x in S.comap f ↔ f x in S :=
  Iff.rfl

/--
Instance `noZeroDivisors` / 实例 `noZeroDivisors`

English:
instance noZeroDivisors
  signature: {R A : Type*} [CommSemiring R] [Semiring A] [NoZeroDivisors A]
  body: inferInstanceAs (NoZeroDivisors S.toSubsemiring)

中文:
实例 noZeroDivisors
  签名: {R A : 类型} [CommSemiring R] [Semiring A] [NoZeroDivisors A]
  定义体: inferInstanceAs (NoZeroDivisors S.toSubsemiring)

Depends on / 依赖: NoZeroDivisors, S.toSubsemiring, toSubsemiring
-/
instance noZeroDivisors {R A : Type*} [CommSemiring R] [Semiring A] [NoZeroDivisors A]
    [Algebra R A] (S : Subalgebra R A) : NoZeroDivisors S :=
  inferInstanceAs (NoZeroDivisors S.toSubsemiring)

/--
Instance `isDomain` / 实例 `isDomain`

English:
instance isDomain
  signature: {R A : Type*} [CommRing R] [Ring A] [IsDomain A] [Algebra R A]
  body: inferInstanceAs (IsDomain S.toSubring)

中文:
实例 isDomain
  签名: {R A : 类型} [CommRing R] [Ring A] [IsDomain A] [Algebra R A]
  定义体: inferInstanceAs (IsDomain S.toSubring)

Depends on / 依赖: IsDomain, S.toSubring, toSubring
-/
instance isDomain {R A : Type*} [CommRing R] [Ring A] [IsDomain A] [Algebra R A]
    (S : Subalgebra R A) : IsDomain S :=
  inferInstanceAs (IsDomain S.toSubring)

end Subalgebra

namespace SubalgebraClass

variable {S R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable [SetLike S A] [SubsemiringClass S A] [hSR : SMulMemClass S R A] (s : S)

instance (priority := 75) toAlgebra : Algebra R s where
  algebraMap := {
    toFun r := ⟨algebraMap R A r, algebraMap_mem s r⟩
map_one' := Subtype.ext by simp
map_mul' _ _ := Subtype.ext by simp
map_zero' := Subtype.ext by simp
map_add' _ _ := Subtype.ext by simp }
commutes' r x := Subtype.ext Algebra.commutes r (x : A)
smul_def' r x := Subtype.ext (algebraMap_smul A r (x : A)).symm

@[simp, norm_cast]
/--
lemma `coe_algebraMap` / 引理 `coe_algebraMap`

English:
lemma coe_algebraMap
  given: (r : R)
  statement: (algebraMap R s r : A) = algebraMap R A r
  proof: rfl

中文:
引理 coe_algebraMap
  条件: (r : R)
  结论: (algebraMap R s r : A) = algebraMap R A r
  证明: rfl
-/
lemma coe_algebraMap (r : R) : (algebraMap R s r : A) = algebraMap R A r := rfl

/--
Definition of `val` / `val` 的定义

English:
definition val
  signature: (s : S)
  body: { SubsemiringClass.subtype s, SMulMemClass.subtype s with
    toFun := (↑)
    commutes' := fun _ => rfl }

@[simp]

中文:
定义 val
  签名: (s : S)
  定义体: { SubsemiringClass.subtype s, SMulMemClass.subtype s with
    toFun := (↑)
    commutes' := fun _ => rfl }

@[simp]

Depends on / 依赖: SMulMemClass, SMulMemClass.subtype, SubsemiringClass, SubsemiringClass.subtype, commutes, subtype
-/
def val (s : S) : s ->ₐ[R] A :=
  { SubsemiringClass.subtype s, SMulMemClass.subtype s with
    toFun := (↑)
    commutes' := fun _ => rfl }

@[simp]
/--
theorem `coe_val` / 定理 `coe_val`

English:
theorem coe_val
  statement: (val s : s -> A) = ((↑) : s -> A)
  proof: rfl

中文:
定理 coe_val
  结论: (val s : s -> A) = ((↑) : s -> A)
  证明: rfl
-/
theorem coe_val : (val s : s -> A) = ((↑) : s -> A) :=
  rfl

end SubalgebraClass

namespace Submodule

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable (p : Submodule R A)

/-- A submodule containing `1` and closed under multiplication is a subalgebra. -/
@[simps coe toSubsemiring]
/--
Definition of `toSubalgebra` / `toSubalgebra` 的定义

English:
definition toSubalgebra
  signature: (p : Submodule R A) (h_one : (1 : A) in p)
  body: { p with
    mul_mem' := fun hx hy => h_mul _ _ hx hy
    one_mem' := h_one
    algebraMap_mem' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one]
      exact p.smul_mem _ h_one }

@[simp]

中文:
定义 toSubalgebra
  签名: (p : Submodule R A) (h_one : (1 : A) in p)
  定义体: { p with
    mul_mem' := fun hx hy => h_mul _ _ hx hy
    one_mem' := h_one
    algebraMap_mem' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one]
      exact p.smul_mem _ h_one }

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, algebraMap_mem, h_mul, h_one, mul_mem, one_mem, p.smul_mem, smul_mem
-/
def toSubalgebra (p : Submodule R A) (h_one : (1 : A) in p)
    (h_mul : forall x y, x in p -> y in p -> x * y in p) : Subalgebra R A :=
  { p with
    mul_mem' := fun hx hy => h_mul _ _ hx hy
    one_mem' := h_one
    algebraMap_mem' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one]
      exact p.smul_mem _ h_one }

@[simp]
/--
theorem `mem_toSubalgebra` / 定理 `mem_toSubalgebra`

English:
theorem mem_toSubalgebra
  given: {p : Submodule R A} {h_one h_mul} {x}
  proof: Iff.rfl

中文:
定理 mem_toSubalgebra
  条件: {p : Submodule R A} {h_one h_mul} {x}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubalgebra {p : Submodule R A} {h_one h_mul} {x} :
    x in p.toSubalgebra h_one h_mul ↔ x in p := Iff.rfl

/--
theorem `toSubalgebra_mk` / 定理 `toSubalgebra_mk`

English:
theorem toSubalgebra_mk
  given: (s : Submodule R A) (h1 hmul)
  proof: rfl

@[simp]

中文:
定理 toSubalgebra_mk
  条件: (s : Submodule R A) (h1 hmul)
  证明: rfl

@[simp]
-/
theorem toSubalgebra_mk (s : Submodule R A) (h1 hmul) :
    s.toSubalgebra h1 hmul =
      Subalgebra.mk ⟨⟨⟨s, @hmul⟩, h1⟩, s.add_mem, s.zero_mem⟩
        (by intro r; rw [Algebra.algebraMap_eq_smul_one]; apply s.smul_mem _ h1) :=
  rfl

@[simp]
/--
theorem `toSubalgebra_toSubmodule` / 定理 `toSubalgebra_toSubmodule`

English:
theorem toSubalgebra_toSubmodule
  given: (p : Submodule R A) (h_one h_mul)
  proof: SetLike.coe_injective rfl

@[simp]

中文:
定理 toSubalgebra_toSubmodule
  条件: (p : Submodule R A) (h_one h_mul)
  证明: SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem toSubalgebra_toSubmodule (p : Submodule R A) (h_one h_mul) :
    Subalgebra.toSubmodule (p.toSubalgebra h_one h_mul) = p :=
  SetLike.coe_injective rfl

@[simp]
/--
theorem `_root_.Subalgebra.toSubmodule_toSubalgebra` / 定理 `_root_.Subalgebra.toSubmodule_toSubalgebra`

English:
theorem _root_.Subalgebra.toSubmodule_toSubalgebra
  given: (S : Subalgebra R A)
  proof: SetLike.coe_injective rfl

中文:
定理 _root_.Subalgebra.toSubmodule_toSubalgebra
  条件: (S : Subalgebra R A)
  证明: SetLike.coe_injective rfl

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem _root_.Subalgebra.toSubmodule_toSubalgebra (S : Subalgebra R A) :
    (S.toSubmodule.toSubalgebra S.one_mem fun _ _ => S.mul_mem) = S :=
  SetLike.coe_injective rfl

end Submodule

namespace AlgHom

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
variable (φ : A ->ₐ[R] B)

/-- Range of an `AlgHom` as a subalgebra. -/
@[simps! coe toSubsemiring]
/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (φ : A ->ₐ[R] B)
  body: { φ.toRingHom.rangeS with algebraMap_mem' := fun r => ⟨algebraMap R A r, φ.commutes r⟩ }

@[simp]

中文:
定义 range
  签名: (φ : A ->ₐ[R] B)
  定义体: { φ.toRingHom.rangeS with algebraMap_mem' := fun r => ⟨algebraMap R A r, φ.commutes r⟩ }

@[simp]
-/
protected def range (φ : A ->ₐ[R] B) : Subalgebra R B :=
  { φ.toRingHom.rangeS with algebraMap_mem' := fun r => ⟨algebraMap R A r, φ.commutes r⟩ }

@[simp]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: (φ : A ->ₐ[R] B) {y : B}
  statement: y in φ.range ↔ exists x, φ x = y
  proof: RingHom.mem_rangeS

中文:
定理 mem_range
  条件: (φ : A ->ₐ[R] B) {y : B}
  结论: y in φ.range ↔ 存在 x, φ x = y
  证明: RingHom.mem_rangeS

Depends on / 依赖: RingHom, RingHom.mem_rangeS, mem_rangeS
-/
theorem mem_range (φ : A ->ₐ[R] B) {y : B} : y in φ.range ↔ exists x, φ x = y :=
  RingHom.mem_rangeS

/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: (φ : A ->ₐ[R] B) (x : A)
  statement: φ x in φ.range
  proof: φ.mem_range.2 ⟨x, rfl⟩

中文:
定理 mem_range_self
  条件: (φ : A ->ₐ[R] B) (x : A)
  结论: φ x in φ.range
  证明: φ.mem_range.2 ⟨x, rfl⟩

Depends on / 依赖: mem_range
-/
theorem mem_range_self (φ : A ->ₐ[R] B) (x : A) : φ x in φ.range :=
  φ.mem_range.2 ⟨x, rfl⟩

/--
theorem `range_comp` / 定理 `range_comp`

English:
theorem range_comp
  given: (f : A ->ₐ[R] B) (g : B ->ₐ[R] C)
  statement: (g.comp f).range = f.range.map g
  proof: SetLike.coe_injective (Set.range_comp g f)

中文:
定理 range_comp
  条件: (f : A ->ₐ[R] B) (g : B ->ₐ[R] C)
  结论: (g.comp f).range = f.range.map g
  证明: SetLike.coe_injective (Set.range_comp g f)

Depends on / 依赖: Set.range_comp, SetLike, SetLike.coe_injective, coe_injective, range_comp
-/
theorem range_comp (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : (g.comp f).range = f.range.map g :=
  SetLike.coe_injective (Set.range_comp g f)

/--
theorem `range_comp_le_range` / 定理 `range_comp_le_range`

English:
theorem range_comp_le_range
  given: (f : A ->ₐ[R] B) (g : B ->ₐ[R] C)
  statement: (g.comp f).range <= g.range
  proof: SetLike.coe_mono (Set.range_comp_subset_range f g)

中文:
定理 range_comp_le_range
  条件: (f : A ->ₐ[R] B) (g : B ->ₐ[R] C)
  结论: (g.comp f).range <= g.range
  证明: SetLike.coe_mono (Set.range_comp_subset_range f g)

Depends on / 依赖: Set.range_comp_subset_range, SetLike, SetLike.coe_mono, coe_mono, range_comp_subset_range
-/
theorem range_comp_le_range (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : (g.comp f).range <= g.range :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x, f x in S)
  body: { RingHom.codRestrict (f : A ->+* B) S hf with commutes' := fun r => Subtype.ext <| f.commutes r }

@[simp]

中文:
定义 codRestrict
  签名: (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : 对任意 x, f x in S)
  定义体: { RingHom.codRestrict (f : A ->+* B) S hf with commutes' := fun r => Subtype.ext <| f.commutes r }

@[simp]

Depends on / 依赖: RingHom, RingHom.codRestrict, Subtype, Subtype.ext, codRestrict, commutes, f.commutes
-/
def codRestrict (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x, f x in S) : A ->ₐ[R] S :=
  { RingHom.codRestrict (f : A ->+* B) S hf with commutes' := fun r => Subtype.ext <| f.commutes r }

@[simp]
/--
theorem `val_comp_codRestrict` / 定理 `val_comp_codRestrict`

English:
theorem val_comp_codRestrict
  given: (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x, f x in S)
  proof: AlgHom.ext fun _ => rfl

@[simp]

中文:
定理 val_comp_codRestrict
  条件: (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : 对任意 x, f x in S)
  证明: AlgHom.ext fun _ => rfl

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ext
-/
theorem val_comp_codRestrict (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x, f x in S) :
    S.val.comp (f.codRestrict S hf) = f :=
  AlgHom.ext fun _ => rfl

@[simp]
/--
theorem `coe_codRestrict` / 定理 `coe_codRestrict`

English:
theorem coe_codRestrict
  given: (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x, f x in S) (x : A)
  proof: rfl

中文:
定理 coe_codRestrict
  条件: (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : 对任意 x, f x in S) (x : A)
  证明: rfl
-/
theorem coe_codRestrict (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x, f x in S) (x : A) :
    ↑(f.codRestrict S hf x) = f x :=
  rfl

/--
theorem `injective_codRestrict` / 定理 `injective_codRestrict`

English:
theorem injective_codRestrict
  given: (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x, f x in S)
  proof: ⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

中文:
定理 injective_codRestrict
  条件: (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : 对任意 x, f x in S)
  证明: ⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

Depends on / 依赖: Subtype, Subtype.ext, Subtype.val, congr_arg
-/
theorem injective_codRestrict (f : A ->ₐ[R] B) (S : Subalgebra R B) (hf : forall x, f x in S) :
    Function.Injective (f.codRestrict S hf) ↔ Function.Injective f :=
⟨fun H _x _y hxy => H Subtype.ext hxy, fun H _x _y hxy => H (congr_arg Subtype.val hxy :)⟩

/--
Definition of `rangeRestrict` / `rangeRestrict` 的定义

English:
abbreviation rangeRestrict
  signature: (f : A ->ₐ[R] B)
  body: f.codRestrict f.range f.mem_range_self

中文:
缩写 rangeRestrict
  签名: (f : A ->ₐ[R] B)
  定义体: f.codRestrict f.range f.mem_range_self

Depends on / 依赖: codRestrict, f.codRestrict, f.mem_range_self, f.range, mem_range_self
-/
abbrev rangeRestrict (f : A ->ₐ[R] B) : A ->ₐ[R] f.range :=
  f.codRestrict f.range f.mem_range_self

/--
theorem `val_comp_rangeRestrict` / 定理 `val_comp_rangeRestrict`

English:
theorem val_comp_rangeRestrict
  proof: by simp

中文:
定理 val_comp_rangeRestrict
  证明: by simp
-/
theorem val_comp_rangeRestrict :
    (Subalgebra.val _).comp φ.rangeRestrict = φ := by simp

/--
theorem `rangeRestrict_surjective` / 定理 `rangeRestrict_surjective`

English:
theorem rangeRestrict_surjective
  given: (f : A ->ₐ[R] B)
  statement: Function.Surjective (f.rangeRestrict)
  proof: fun ⟨_y, hy⟩ =>
    let ⟨x, hx⟩ := hy
    ⟨x, SetCoe.ext hx⟩

中文:
定理 rangeRestrict_surjective
  条件: (f : A ->ₐ[R] B)
  结论: Function.Surjective (f.rangeRestrict)
  证明: fun ⟨_y, hy⟩ =>
    let ⟨x, hx⟩ := hy
    ⟨x, SetCoe.ext hx⟩

Depends on / 依赖: SetCoe, SetCoe.ext
-/
theorem rangeRestrict_surjective (f : A ->ₐ[R] B) : Function.Surjective (f.rangeRestrict) :=
  fun ⟨_y, hy⟩ =>
    let ⟨x, hx⟩ := hy
    ⟨x, SetCoe.ext hx⟩

/--
Instance `fintypeRange` / 实例 `fintypeRange`

English:
instance fintypeRange
  signature: [Fintype A] [DecidableEq B] (φ : A ->ₐ[R] B)
  body: Set.fintypeRange φ

中文:
实例 fintypeRange
  签名: [Fintype A] [DecidableEq B] (φ : A ->ₐ[R] B)
  定义体: Set.fintypeRange φ

Depends on / 依赖: Set.fintypeRange, fintypeRange
-/
instance fintypeRange [Fintype A] [DecidableEq B] (φ : A ->ₐ[R] B) : Fintype φ.range :=
  Set.fintypeRange φ

end AlgHom

namespace AlgEquiv

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/--
Definition of `ofLeftInverse` / `ofLeftInverse` 的定义

English:
definition ofLeftInverse
  signature: {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftInverse g f)
  body: { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.val
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := f.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]

中文:
定义 ofLeftInverse
  签名: {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftInverse g f)
  定义体: { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.val
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := f.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]

Depends on / 依赖: AlgHomClass, LinearMapClass, Subtype, Subtype.ext, f.mem_range.mp, f.range.val, f.rangeRestrict, invFun, left_inv, linearMapClass, mem_range, rangeRestrict, right_inv, x.prop
-/
def ofLeftInverse {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftInverse g f) : A ≃ₐ[R] f.range :=
  { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.val
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := f.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/--
theorem `ofLeftInverse_apply` / 定理 `ofLeftInverse_apply`

English:
theorem ofLeftInverse_apply
  given: {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftInverse g f) (x : A)
  proof: rfl

@[simp]

中文:
定理 ofLeftInverse_apply
  条件: {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftInverse g f) (x : A)
  证明: rfl

@[simp]
-/
theorem ofLeftInverse_apply {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftInverse g f) (x : A) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[simp]
/--
theorem `ofLeftInverse_symm_apply` / 定理 `ofLeftInverse_symm_apply`

English:
theorem ofLeftInverse_symm_apply
  statement: {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftInverse g f)
  proof: rfl

中文:
定理 ofLeftInverse_symm_apply
  结论: {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftInverse g f)
  证明: rfl
-/
theorem ofLeftInverse_symm_apply {g : B -> A} {f : A ->ₐ[R] B} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl

/--
Definition of `ofInjective` / `ofInjective` 的定义

English:
definition ofInjective
  signature: (f : A ->ₐ[R] B) (hf : Function.Injective f)
  body: ofLeftInverse (Classical.choose_spec hf.hasLeftInverse)

@[simp]

中文:
定义 ofInjective
  签名: (f : A ->ₐ[R] B) (hf : Function.Injective f)
  定义体: ofLeftInverse (Classical.choose_spec hf.hasLeftInverse)

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, hasLeftInverse, hf.hasLeftInverse, ofLeftInverse
-/
noncomputable def ofInjective (f : A ->ₐ[R] B) (hf : Function.Injective f) : A ≃ₐ[R] f.range :=
  ofLeftInverse (Classical.choose_spec hf.hasLeftInverse)

@[simp]
/--
theorem `ofInjective_apply` / 定理 `ofInjective_apply`

English:
theorem ofInjective_apply
  given: (f : A ->ₐ[R] B) (hf : Function.Injective f) (x : A)
  proof: rfl

中文:
定理 ofInjective_apply
  条件: (f : A ->ₐ[R] B) (hf : Function.Injective f) (x : A)
  证明: rfl
-/
theorem ofInjective_apply (f : A ->ₐ[R] B) (hf : Function.Injective f) (x : A) :
    ↑(ofInjective f hf x) = f x :=
  rfl

/--
Definition of `ofInjectiveField` / `ofInjectiveField` 的定义

English:
definition ofInjectiveField
  signature: {E F : Type*} [DivisionRing E] [Semiring F] [Nontrivial F]
  body: ofInjective f f.toRingHom.injective

#adaptation_note

中文:
定义 ofInjectiveField
  签名: {E F : 类型} [DivisionRing E] [Semiring F] [Nontrivial F]
  定义体: ofInjective f f.toRingHom.injective

#adaptation_note

Depends on / 依赖: f.toRingHom.injective, injective, ofInjective, toRingHom
-/
noncomputable def ofInjectiveField {E F : Type*} [DivisionRing E] [Semiring F] [Nontrivial F]
    [Algebra R E] [Algebra R F] (f : E ->ₐ[R] F) : E ≃ₐ[R] f.range :=
  ofInjective f f.toRingHom.injective

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given an equivalence `e : A ≃ₐ[R] B` of `R`-algebras and a subalgebra `S` of `A`,
`subalgebraMap` is the induced equivalence between `S` and `S.map e` -/
@[simps!]
/--
Definition of `subalgebraMap` / `subalgebraMap` 的定义

English:
definition subalgebraMap
  signature: (e : A ≃ₐ[R] B) (S : Subalgebra R A)
  body: { e.toRingEquiv.subsemiringMap S.toSubsemiring with
    commutes' := fun r => by ext; exact e.commutes r }

中文:
定义 subalgebraMap
  签名: (e : A ≃ₐ[R] B) (S : Subalgebra R A)
  定义体: { e.toRingEquiv.subsemiringMap S.toSubsemiring with
    commutes' := fun r => by ext; exact e.commutes r }

Depends on / 依赖: S.toSubsemiring, commutes, e.commutes, e.toRingEquiv.subsemiringMap, subsemiringMap, toRingEquiv, toSubsemiring
-/
def subalgebraMap (e : A ≃ₐ[R] B) (S : Subalgebra R A) : S ≃ₐ[R] S.map (e : A ->ₐ[R] B) :=
  { e.toRingEquiv.subsemiringMap S.toSubsemiring with
    commutes' := fun r => by ext; exact e.commutes r }

end AlgEquiv

namespace Subalgebra

open Algebra

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S T U : Subalgebra R A)

/--
Instance `subsingleton_of_subsingleton` / 实例 `subsingleton_of_subsingleton`

English:
instance subsingleton_of_subsingleton
  signature: [Subsingleton A]
  body: ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

中文:
实例 subsingleton_of_subsingleton
  签名: [Subsingleton A]
  定义体: ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, zero_mem
-/
instance subsingleton_of_subsingleton [Subsingleton A] : Subsingleton (Subalgebra R A) :=
  ⟨fun B C => ext fun x => by simp only [Subsingleton.elim x 0, zero_mem B, zero_mem C]⟩

/--
theorem `range_val` / 定理 `range_val`

English:
theorem range_val
  statement: S.val.range = S
  proof: ext Set.ext_iff.1 S.val.coe_range.trans Subtype.range_val

中文:
定理 range_val
  结论: S.val.range = S
  证明: ext Set.ext_iff.1 S.val.coe_range.trans Subtype.range_val

Depends on / 依赖: S.val.coe_range.trans, Set.ext_iff, Subtype, Subtype.range_val, coe_range, ext_iff, range_val
-/
theorem range_val : S.val.range = S :=
ext Set.ext_iff.1 S.val.coe_range.trans Subtype.range_val

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : Subalgebra R A} (h : S <= T)
  body: Set.inclusion h
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  commutes' _ := rfl

中文:
定义 inclusion
  签名: {S T : Subalgebra R A} (h : S <= T)
  定义体: Set.inclusion h
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  commutes' _ := rfl

Depends on / 依赖: Set.inclusion, inclusion
-/
def inclusion {S T : Subalgebra R A} (h : S <= T) : S ->ₐ[R] T where
  toFun := Set.inclusion h
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  commutes' _ := rfl

variable {S T U} (h : S <= T)

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  statement: Function.Injective (inclusion h)
  proof: fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]

中文:
定理 inclusion_injective
  结论: Function.Injective (inclusion h)
  证明: fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, Subtype.mk.inj
-/
theorem inclusion_injective : Function.Injective (inclusion h) :=
  fun _ _ => Subtype.ext ∘ Subtype.mk.inj

@[simp]
/--
theorem `inclusion_self` / 定理 `inclusion_self`

English:
theorem inclusion_self
  statement: inclusion (le_refl S) = AlgHom.id R S
  proof: AlgHom.ext fun _x => Subtype.ext rfl

@[simp]

中文:
定理 inclusion_self
  结论: inclusion (le_refl S) = AlgHom.id R S
  证明: AlgHom.ext fun _x => Subtype.ext rfl

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ext, Subtype, Subtype.ext
-/
theorem inclusion_self : inclusion (le_refl S) = AlgHom.id R S :=
  AlgHom.ext fun _x => Subtype.ext rfl

@[simp]
/--
theorem `inclusion_mk` / 定理 `inclusion_mk`

English:
theorem inclusion_mk
  given: (x : A) (hx : x in S)
  statement: inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩
  proof: rfl

中文:
定理 inclusion_mk
  条件: (x : A) (hx : x in S)
  结论: inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩
  证明: rfl
-/
theorem inclusion_mk (x : A) (hx : x in S) : inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ :=
  rfl

/--
theorem `inclusion_right` / 定理 `inclusion_right`

English:
theorem inclusion_right
  given: (x : T) (m : (x : A) in S)
  statement: inclusion h ⟨x, m⟩ = x
  proof: Subtype.ext rfl

@[simp]

中文:
定理 inclusion_right
  条件: (x : T) (m : (x : A) in S)
  结论: inclusion h ⟨x, m⟩ = x
  证明: Subtype.ext rfl

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem inclusion_right (x : T) (m : (x : A) in S) : inclusion h ⟨x, m⟩ = x :=
  Subtype.ext rfl

@[simp]
/--
theorem `inclusion_inclusion` / 定理 `inclusion_inclusion`

English:
theorem inclusion_inclusion
  given: (hst : S <= T) (htu : T <= U) (x : S)
  proof: Subtype.ext rfl

@[simp]

中文:
定理 inclusion_inclusion
  条件: (hst : S <= T) (htu : T <= U) (x : S)
  证明: Subtype.ext rfl

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem inclusion_inclusion (hst : S <= T) (htu : T <= U) (x : S) :
    inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
  Subtype.ext rfl

@[simp]
/--
theorem `val_comp_inclusion` / 定理 `val_comp_inclusion`

English:
theorem val_comp_inclusion
  given: (hst : S <= T)
  proof: rfl

@[simp]

中文:
定理 val_comp_inclusion
  条件: (hst : S <= T)
  证明: rfl

@[simp]
-/
theorem val_comp_inclusion (hst : S <= T) :
    T.val.comp (inclusion hst) = S.val :=
  rfl

@[simp]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: (s : S)
  statement: (inclusion h s : A) = s
  proof: rfl

中文:
定理 coe_inclusion
  条件: (s : S)
  结论: (inclusion h s : A) = s
  证明: rfl
-/
theorem coe_inclusion (s : S) : (inclusion h s : A) = s :=
  rfl

namespace inclusion

scoped instance isScalarTower_left (X) [SMul X R] [SMul X A] [IsScalarTower X R A] :
    letI := (inclusion h).toModule; IsScalarTower X S T :=
  letI := (inclusion h).toModule
⟨fun x s t => Subtype.ext by
    rw [← one_smul R s]; rw [← smul_assoc]; rw [one_smul]; rw [← one_smul R (s • t)]; rw [← smul_assoc]; rw [Algebra.smul_def]; rw [Algebra.smul_def]
    apply mul_assoc⟩

scoped instance isScalarTower_right (X) [MulAction A X] :
    letI := (inclusion h).toModule; IsScalarTower S T X :=
  letI := (inclusion h).toModule; ⟨fun _ => mul_smul _⟩

scoped instance faithfulSMul :
    letI := (inclusion h).toModule; FaithfulSMul S T :=
  letI := (inclusion h).toModule
⟨fun {x y} h => Subtype.ext by
    convert! Subtype.ext_iff.mp (h 1) using 1 <;> exact (mul_one _).symm⟩

end inclusion

variable (S)

/-- Two subalgebras that are equal are also equivalent as algebras.

This is the `Subalgebra` version of `LinearEquiv.ofEq` and `Equiv.setCongr`. -/
@[simps apply]
/--
Definition of `equivOfEq` / `equivOfEq` 的定义

English:
definition equivOfEq
  signature: (S T : Subalgebra R A) (h : S = T)
  body: LinearEquiv.ofEq _ _ (congr_arg toSubmodule h)
  toFun x := ⟨x, h ▸ x.2⟩
  invFun x := ⟨x, h.symm ▸ x.2⟩
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]

中文:
定义 equivOfEq
  签名: (S T : Subalgebra R A) (h : S = T)
  定义体: LinearEquiv.ofEq _ _ (congr_arg toSubmodule h)
  toFun x := ⟨x, h ▸ x.2⟩
  invFun x := ⟨x, h.symm ▸ x.2⟩
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofEq, congr_arg, toSubmodule
-/
def equivOfEq (S T : Subalgebra R A) (h : S = T) : S ≃ₐ[R] T where
  __ := LinearEquiv.ofEq _ _ (congr_arg toSubmodule h)
  toFun x := ⟨x, h ▸ x.2⟩
  invFun x := ⟨x, h.symm ▸ x.2⟩
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]
/--
theorem `equivOfEq_symm` / 定理 `equivOfEq_symm`

English:
theorem equivOfEq_symm
  given: (S T : Subalgebra R A) (h : S = T)
  proof: rfl

@[simp]

中文:
定理 equivOfEq_symm
  条件: (S T : Subalgebra R A) (h : S = T)
  证明: rfl

@[simp]
-/
theorem equivOfEq_symm (S T : Subalgebra R A) (h : S = T) :
    (equivOfEq S T h).symm = equivOfEq T S h.symm := rfl

@[simp]
/--
theorem `equivOfEq_rfl` / 定理 `equivOfEq_rfl`

English:
theorem equivOfEq_rfl
  given: (S : Subalgebra R A)
  statement: equivOfEq S S rfl = AlgEquiv.refl
  proof: by ext; rfl

@[simp]

中文:
定理 equivOfEq_rfl
  条件: (S : Subalgebra R A)
  结论: equivOfEq S S rfl = AlgEquiv.refl
  证明: by ext; rfl

@[simp]
-/
theorem equivOfEq_rfl (S : Subalgebra R A) : equivOfEq S S rfl = AlgEquiv.refl := by ext; rfl

@[simp]
/--
theorem `equivOfEq_trans` / 定理 `equivOfEq_trans`

English:
theorem equivOfEq_trans
  given: (S T U : Subalgebra R A) (hST : S = T) (hTU : T = U)
  proof: rfl

中文:
定理 equivOfEq_trans
  条件: (S T U : Subalgebra R A) (hST : S = T) (hTU : T = U)
  证明: rfl
-/
theorem equivOfEq_trans (S T U : Subalgebra R A) (hST : S = T) (hTU : T = U) :
    (equivOfEq S T hST).trans (equivOfEq T U hTU) = equivOfEq S U (hST.trans hTU) := rfl

section equivMapOfInjective

variable (f : A ->ₐ[R] B)

/--
theorem `range_comp_val` / 定理 `range_comp_val`

English:
theorem range_comp_val
  statement: (f.comp S.val).range = S.map f
  proof: by
  rw [AlgHom.range_comp]; rw [range_val]

中文:
定理 range_comp_val
  结论: (f.comp S.val).range = S.map f
  证明: by
  rw [AlgHom.range_comp]; rw [range_val]

Depends on / 依赖: AlgHom, AlgHom.range_comp, range_comp, range_val
-/
theorem range_comp_val : (f.comp S.val).range = S.map f := by
  rw [AlgHom.range_comp]; rw [range_val]

/--
Definition of `_root_.AlgHom.subalgebraMap` / `_root_.AlgHom.subalgebraMap` 的定义

English:
definition _root_.AlgHom.subalgebraMap
  signature: : S ->ₐ[R] S.map f
  body: (f.comp S.val).codRestrict _ fun x => ⟨_, x.2, rfl⟩

中文:
定义 _root_.AlgHom.subalgebraMap
  签名: : S ->ₐ[R] S.map f
  定义体: (f.comp S.val).codRestrict _ fun x => ⟨_, x.2, rfl⟩

Depends on / 依赖: S.val, codRestrict, f.comp
-/
def _root_.AlgHom.subalgebraMap : S ->ₐ[R] S.map f :=
  (f.comp S.val).codRestrict _ fun x => ⟨_, x.2, rfl⟩

variable {S} in
@[simp]
/--
theorem `_root_.AlgHom.subalgebraMap_coe_apply` / 定理 `_root_.AlgHom.subalgebraMap_coe_apply`

English:
theorem _root_.AlgHom.subalgebraMap_coe_apply
  given: (x : S)
  statement: f.subalgebraMap S x = f x
  proof: rfl

中文:
定理 _root_.AlgHom.subalgebraMap_coe_apply
  条件: (x : S)
  结论: f.subalgebraMap S x = f x
  证明: rfl
-/
theorem _root_.AlgHom.subalgebraMap_coe_apply (x : S) : f.subalgebraMap S x = f x := rfl

/--
theorem `_root_.AlgHom.subalgebraMap_surjective` / 定理 `_root_.AlgHom.subalgebraMap_surjective`

English:
theorem _root_.AlgHom.subalgebraMap_surjective
  statement: Function.Surjective (f.subalgebraMap S)
  proof: f.toAddMonoidHom.addSubmonoidMap_surjective S.toAddSubmonoid

中文:
定理 _root_.AlgHom.subalgebraMap_surjective
  结论: Function.Surjective (f.subalgebraMap S)
  证明: f.toAddMonoidHom.addSubmonoidMap_surjective S.toAddSubmonoid

Depends on / 依赖: S.toAddSubmonoid, addSubmonoidMap_surjective, f.toAddMonoidHom.addSubmonoidMap_surjective, toAddMonoidHom, toAddSubmonoid
-/
theorem _root_.AlgHom.subalgebraMap_surjective : Function.Surjective (f.subalgebraMap S) :=
  f.toAddMonoidHom.addSubmonoidMap_surjective S.toAddSubmonoid

variable (hf : Function.Injective f)

/--
Definition of `equivMapOfInjective` / `equivMapOfInjective` 的定义

English:
definition equivMapOfInjective
  signature: : S ≃ₐ[R] S.map f
  body: (AlgEquiv.ofInjective (f.comp S.val) (hf.comp Subtype.val_injective)).trans
    (equivOfEq _ _ (range_comp_val S f))

@[simp]

中文:
定义 equivMapOfInjective
  签名: : S ≃ₐ[R] S.map f
  定义体: (AlgEquiv.ofInjective (f.comp S.val) (hf.comp Subtype.val_injective)).trans
    (equivOfEq _ _ (range_comp_val S f))

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, S.val, Subtype, Subtype.val_injective, equivOfEq, f.comp, hf.comp, ofInjective, range_comp_val, val_injective
-/
noncomputable def equivMapOfInjective : S ≃ₐ[R] S.map f :=
  (AlgEquiv.ofInjective (f.comp S.val) (hf.comp Subtype.val_injective)).trans
    (equivOfEq _ _ (range_comp_val S f))

@[simp]
/--
theorem `coe_equivMapOfInjective_apply` / 定理 `coe_equivMapOfInjective_apply`

English:
theorem coe_equivMapOfInjective_apply
  given: (x : S)
  statement: ↑(equivMapOfInjective S f hf x) = f x
  proof: rfl

中文:
定理 coe_equivMapOfInjective_apply
  条件: (x : S)
  结论: ↑(equivMapOfInjective S f hf x) = f x
  证明: rfl
-/
theorem coe_equivMapOfInjective_apply (x : S) : ↑(equivMapOfInjective S f hf x) = f x := rfl

end equivMapOfInjective

/-! ## Actions by `Subalgebra`s

These are just copies of the definitions about `Subsemiring` starting from
`Subring.mulAction`.
-/


section Actions

variable {α β : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: A α] (S
  body: inferInstanceAs (SMul S.toSubsemiring α)

中文:
实例 [SMul
  签名: A α] (S
  定义体: inferInstanceAs (SMul S.toSubsemiring α)

Depends on / 依赖: S.toSubsemiring, toSubsemiring
-/
instance [SMul A α] (S : Subalgebra R A) : SMul S α :=
  inferInstanceAs (SMul S.toSubsemiring α)

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: [SMul A α] {S : Subalgebra R A} (g : S) (m : α)
  statement: g • m = (g : A) • m
  proof: rfl

中文:
定理 smul_def
  条件: [SMul A α] {S : Subalgebra R A} (g : S) (m : α)
  结论: g • m = (g : A) • m
  证明: rfl
-/
theorem smul_def [SMul A α] {S : Subalgebra R A} (g : S) (m : α) : g • m = (g : A) • m := rfl

/--
Instance `smulCommClass_left` / 实例 `smulCommClass_left`

English:
instance smulCommClass_left
  signature: [SMul A β] [SMul α β] [SMulCommClass A α β] (S : Subalgebra R A)
  body: S.toSubsemiring.smulCommClass_left

中文:
实例 smulCommClass_left
  签名: [SMul A β] [SMul α β] [SMulCommClass A α β] (S : Subalgebra R A)
  定义体: S.toSubsemiring.smulCommClass_left

Depends on / 依赖: S.toSubsemiring.smulCommClass_left, smulCommClass_left, toSubsemiring
-/
instance smulCommClass_left [SMul A β] [SMul α β] [SMulCommClass A α β] (S : Subalgebra R A) :
    SMulCommClass S α β :=
  S.toSubsemiring.smulCommClass_left

/--
Instance `smulCommClass_right` / 实例 `smulCommClass_right`

English:
instance smulCommClass_right
  signature: [SMul α β] [SMul A β] [SMulCommClass α A β] (S : Subalgebra R A)
  body: S.toSubsemiring.smulCommClass_right

中文:
实例 smulCommClass_right
  签名: [SMul α β] [SMul A β] [SMulCommClass α A β] (S : Subalgebra R A)
  定义体: S.toSubsemiring.smulCommClass_right

Depends on / 依赖: S.toSubsemiring.smulCommClass_right, smulCommClass_right, toSubsemiring
-/
instance smulCommClass_right [SMul α β] [SMul A β] [SMulCommClass α A β] (S : Subalgebra R A) :
    SMulCommClass α S β :=
  S.toSubsemiring.smulCommClass_right

/--
Instance `isScalarTower_left` / 实例 `isScalarTower_left`

English:
instance isScalarTower_left
  signature: [SMul α β] [SMul A α] [SMul A β] [IsScalarTower A α β]
  body: inferInstanceAs (IsScalarTower S.toSubsemiring α β)

中文:
实例 isScalarTower_left
  签名: [SMul α β] [SMul A α] [SMul A β] [IsScalarTower A α β]
  定义体: inferInstanceAs (IsScalarTower S.toSubsemiring α β)

Depends on / 依赖: IsScalarTower, S.toSubsemiring, toSubsemiring
-/
instance isScalarTower_left [SMul α β] [SMul A α] [SMul A β] [IsScalarTower A α β] :
    IsScalarTower S α β :=
  inferInstanceAs (IsScalarTower S.toSubsemiring α β)

instance (priority := low) isScalarTower_mid [SMul α R] [SMul α A]
    [IsScalarTower α R A] [SMul A β] [SMul α β] [IsScalarTower α A β] :
    IsScalarTower α S β :=
  ⟨fun a b c => smul_assoc a b.1 c⟩

instance (priority := low) isScalarTower_right [SMul α R] [SMul α A] [IsScalarTower α R A]
    [SMul β R] [SMul β A] [IsScalarTower β R A] [SMul α β] [IsScalarTower α β A] :
    IsScalarTower α β S :=
  ⟨fun a b c => Subtype.ext (smul_assoc a b c.1)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: A α] [FaithfulSMul A α] (S
  body: inferInstanceAs (FaithfulSMul S.toSubsemiring α)

中文:
实例 [SMul
  签名: A α] [FaithfulSMul A α] (S
  定义体: inferInstanceAs (FaithfulSMul S.toSubsemiring α)

Depends on / 依赖: FaithfulSMul, S.toSubsemiring, toSubsemiring
-/
instance [SMul A α] [FaithfulSMul A α] (S : Subalgebra R A) : FaithfulSMul S α :=
  inferInstanceAs (FaithfulSMul S.toSubsemiring α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulAction
  signature: A α] (S
  body: inferInstanceAs (MulAction S.toSubsemiring α)

中文:
实例 [MulAction
  签名: A α] (S
  定义体: inferInstanceAs (MulAction S.toSubsemiring α)

Depends on / 依赖: MulAction, S.toSubsemiring, toSubsemiring
-/
instance [MulAction A α] (S : Subalgebra R A) : MulAction S α :=
  inferInstanceAs (MulAction S.toSubsemiring α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: α] [DistribMulAction A α] (S
  body: inferInstanceAs (DistribMulAction S.toSubsemiring α)

中文:
实例 [AddMonoid
  签名: α] [DistribMulAction A α] (S
  定义体: inferInstanceAs (DistribMulAction S.toSubsemiring α)

Depends on / 依赖: DistribMulAction, S.toSubsemiring, toSubsemiring
-/
instance [AddMonoid α] [DistribMulAction A α] (S : Subalgebra R A) : DistribMulAction S α :=
  inferInstanceAs (DistribMulAction S.toSubsemiring α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: α] [SMulWithZero A α] (S
  body: inferInstanceAs (SMulWithZero S.toSubsemiring α)

中文:
实例 [Zero
  签名: α] [SMulWithZero A α] (S
  定义体: inferInstanceAs (SMulWithZero S.toSubsemiring α)

Depends on / 依赖: S.toSubsemiring, SMulWithZero, toSubsemiring
-/
instance [Zero α] [SMulWithZero A α] (S : Subalgebra R A) : SMulWithZero S α :=
  inferInstanceAs (SMulWithZero S.toSubsemiring α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: α] [MulActionWithZero A α] (S
  body: inferInstanceAs (MulActionWithZero S.toSubsemiring α)

中文:
实例 [Zero
  签名: α] [MulActionWithZero A α] (S
  定义体: inferInstanceAs (MulActionWithZero S.toSubsemiring α)

Depends on / 依赖: MulActionWithZero, S.toSubsemiring, toSubsemiring
-/
instance [Zero α] [MulActionWithZero A α] (S : Subalgebra R A) : MulActionWithZero S α :=
  inferInstanceAs (MulActionWithZero S.toSubsemiring α)

/--
Instance `moduleLeft` / 实例 `moduleLeft`

English:
instance moduleLeft
  signature: [AddCommMonoid α] [Module A α] (S : Subalgebra R A)
  body: inferInstanceAs (Module S.toSubsemiring α)

中文:
实例 moduleLeft
  签名: [AddCommMonoid α] [Module A α] (S : Subalgebra R A)
  定义体: inferInstanceAs (Module S.toSubsemiring α)

Depends on / 依赖: Module, S.toSubsemiring, toSubsemiring
-/
instance moduleLeft [AddCommMonoid α] [Module A α] (S : Subalgebra R A) : Module S α :=
  inferInstanceAs (Module S.toSubsemiring α)

/--
Instance `toAlgebra` / 实例 `toAlgebra`

English:
instance toAlgebra
  signature: {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
  body: Algebra.ofSubsemiring S.toSubsemiring

中文:
实例 toAlgebra
  签名: {R A : 类型} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
  定义体: Algebra.ofSubsemiring S.toSubsemiring

Depends on / 依赖: Algebra, Algebra.ofSubsemiring, S.toSubsemiring, ofSubsemiring, toSubsemiring
-/
instance toAlgebra {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
    [Algebra A α] (S : Subalgebra R A) : Algebra S α :=
  Algebra.ofSubsemiring S.toSubsemiring

/--
theorem `algebraMap_eq` / 定理 `algebraMap_eq`

English:
theorem algebraMap_eq
  statement: {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
  proof: rfl

中文:
定理 algebraMap_eq
  结论: {R A : 类型} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
  证明: rfl
-/
theorem algebraMap_eq {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α] [Algebra R A]
    [Algebra A α] (S : Subalgebra R A) : algebraMap S α = (algebraMap A α).comp S.val :=
  rfl

/--
theorem `algebraMap_def` / 定理 `algebraMap_def`

English:
theorem algebraMap_def
  statement: {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α]
  proof: rfl

@[simp]

中文:
定理 algebraMap_def
  结论: {R A : 类型} [CommSemiring R] [CommSemiring A] [Semiring α]
  证明: rfl

@[simp]
-/
theorem algebraMap_def {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α]
    [Algebra R A] [Algebra A α] {S : Subalgebra R A} (s : S) :
  algebraMap S α s = algebraMap A α (s : A) := rfl

@[simp]
/--
theorem `algebraMap_mk` / 定理 `algebraMap_mk`

English:
theorem algebraMap_mk
  statement: {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α]
  proof: rfl

@[simp]

中文:
定理 algebraMap_mk
  结论: {R A : 类型} [CommSemiring R] [CommSemiring A] [Semiring α]
  证明: rfl

@[simp]
-/
theorem algebraMap_mk {R A : Type*} [CommSemiring R] [CommSemiring A] [Semiring α]
    [Algebra R A] [Algebra A α] {S : Subalgebra R A} (a : A) (ha : a in S) :
  algebraMap S α (⟨a, ha⟩ : S) = algebraMap A α a := rfl

@[simp]
/--
lemma `algebraMap_apply` / 引理 `algebraMap_apply`

English:
lemma algebraMap_apply
  statement: {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  proof: rfl

@[simp]

中文:
引理 algebraMap_apply
  结论: {R A : 类型} [CommSemiring R] [CommSemiring A] [Algebra R A]
  证明: rfl

@[simp]
-/
lemma algebraMap_apply {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) (x : S) : algebraMap S A x = x :=
  rfl

@[simp]
/--
theorem `rangeS_algebraMap` / 定理 `rangeS_algebraMap`

English:
theorem rangeS_algebraMap
  statement: {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  proof: by
  rw [algebraMap_eq]; rw [Algebra.algebraMap_self]; rw [RingHom.id_comp]; rw [← toSubsemiring_subtype]; rw [Subsemiring.rangeS_subtype]

@[simp]

中文:
定理 rangeS_algebraMap
  结论: {R A : 类型} [CommSemiring R] [CommSemiring A] [Algebra R A]
  证明: by
  rw [algebraMap_eq]; rw [Algebra.algebraMap_self]; rw [RingHom.id_comp]; rw [← toSubsemiring_subtype]; rw [Subsemiring.rangeS_subtype]

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_self, RingHom, RingHom.id_comp, Subsemiring, Subsemiring.rangeS_subtype, algebraMap_eq, algebraMap_self, id_comp, rangeS_subtype, toSubsemiring_subtype
-/
theorem rangeS_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).rangeS = S.toSubsemiring := by
  rw [algebraMap_eq]; rw [Algebra.algebraMap_self]; rw [RingHom.id_comp]; rw [← toSubsemiring_subtype]; rw [Subsemiring.rangeS_subtype]

@[simp]
/--
theorem `range_algebraMap` / 定理 `range_algebraMap`

English:
theorem range_algebraMap
  statement: {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  proof: by
  rw [algebraMap_eq]; rw [Algebra.algebraMap_self]; rw [RingHom.id_comp]; rw [← toSubring_subtype]; rw [Subring.range_subtype]

@[simp]

中文:
定理 range_algebraMap
  结论: {R A : 类型} [CommRing R] [CommRing A] [Algebra R A]
  证明: by
  rw [algebraMap_eq]; rw [Algebra.algebraMap_self]; rw [RingHom.id_comp]; rw [← toSubring_subtype]; rw [Subring.range_subtype]

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_self, RingHom, RingHom.id_comp, Subring, Subring.range_subtype, algebraMap_eq, algebraMap_self, id_comp, range_subtype, toSubring_subtype
-/
theorem range_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).range = S.toSubring := by
  rw [algebraMap_eq]; rw [Algebra.algebraMap_self]; rw [RingHom.id_comp]; rw [← toSubring_subtype]; rw [Subring.range_subtype]

@[simp]
/--
lemma `setRange_algebraMap` / 引理 `setRange_algebraMap`

English:
lemma setRange_algebraMap
  statement: {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  proof: SetLike.ext'_iff.mp S.rangeS_algebraMap

中文:
引理 setRange_algebraMap
  结论: {R A : 类型} [CommSemiring R] [CommSemiring A] [Algebra R A]
  证明: SetLike.ext'_iff.mp S.rangeS_algebraMap

Depends on / 依赖: S.rangeS_algebraMap, SetLike, SetLike.ext, _iff, _iff.mp, rangeS_algebraMap
-/
lemma setRange_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : Set.range (algebraMap S A) = (S : Set A) :=
  SetLike.ext'_iff.mp S.rangeS_algebraMap

/--
Instance `instIsTorsionFree'` / 实例 `instIsTorsionFree'`

English:
instance instIsTorsionFree'
  signature: [IsDomain A] (S : Subalgebra R A)
  body: .comap Subtype.val (fun r hr => by simpa [isRegular_iff_ne_zero] using hr.ne_zero)
    (by simp [smul_def])

中文:
实例 instIsTorsionFree'
  签名: [IsDomain A] (S : Subalgebra R A)
  定义体: .comap Subtype.val (fun r hr => by simpa [isRegular_iff_ne_zero] using hr.ne_zero)
    (by simp [smul_def])

Depends on / 依赖: Subtype, Subtype.val, hr.ne_zero, isRegular_iff_ne_zero, ne_zero, smul_def
-/
instance instIsTorsionFree' [IsDomain A] (S : Subalgebra R A) : IsTorsionFree S A :=
  .comap Subtype.val (fun r hr => by simpa [isRegular_iff_ne_zero] using hr.ne_zero)
    (by simp [smul_def])

end Actions

section Center

/--
theorem `_root_.Set.algebraMap_mem_center` / 定理 `_root_.Set.algebraMap_mem_center`

English:
theorem _root_.Set.algebraMap_mem_center
  given: (r : R)
  statement: algebraMap R A r in Set.center A
  proof: by
  simp only [Semigroup.mem_center_iff, commutes, forall_const]

中文:
定理 _root_.Set.algebraMap_mem_center
  条件: (r : R)
  结论: algebraMap R A r in Set.center A
  证明: by
  simp only [Semigroup.mem_center_iff, commutes, forall_const]

Depends on / 依赖: Semigroup, Semigroup.mem_center_iff, commutes, forall_const, mem_center_iff
-/
theorem _root_.Set.algebraMap_mem_center (r : R) : algebraMap R A r in Set.center A := by
  simp only [Semigroup.mem_center_iff, commutes, forall_const]

variable (R A)

/-- The center of an algebra is the set of elements which commute with every element. They form a
subalgebra. -/
@[simps! coe toSubsemiring]
/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : Subalgebra R A
  body: { Subsemiring.center A with algebraMap_mem' := Set.algebraMap_mem_center }

@[simp]

中文:
定义 center
  签名: : Subalgebra R A
  定义体: { Subsemiring.center A with algebraMap_mem' := Set.algebraMap_mem_center }

@[simp]

Depends on / 依赖: Set.algebraMap_mem_center, Subsemiring, Subsemiring.center, algebraMap_mem, algebraMap_mem_center, center
-/
def center : Subalgebra R A :=
  { Subsemiring.center A with algebraMap_mem' := Set.algebraMap_mem_center }

@[simp]
/--
theorem `center_toSubring` / 定理 `center_toSubring`

English:
theorem center_toSubring
  given: (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
  proof: rfl

中文:
定理 center_toSubring
  条件: (R A : 类型) [CommRing R] [Ring A] [Algebra R A]
  证明: rfl
-/
theorem center_toSubring (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    (center R A).toSubring = Subring.center A :=
  rfl

variable {R A}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring (center R A)
  body: inferInstanceAs (CommSemiring (Subsemiring.center A))

中文:
实例 :
  签名: CommSemiring (center R A)
  定义体: inferInstanceAs (CommSemiring (Subsemiring.center A))

Depends on / 依赖: CommSemiring, Subsemiring, Subsemiring.center, center
-/
instance : CommSemiring (center R A) :=
  inferInstanceAs (CommSemiring (Subsemiring.center A))

instance {A : Type*} [Ring A] [Algebra R A] : CommRing (center R A) :=
  inferInstanceAs (CommRing (Subring.center A))

/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {a : A}
  statement: a in center R A ↔ forall b : A, b * a = a * b
  proof: Subsemigroup.mem_center_iff

中文:
定理 mem_center_iff
  条件: {a : A}
  结论: a in center R A ↔ 对任意 b : A, b * a = a * b
  证明: Subsemigroup.mem_center_iff

Depends on / 依赖: Subsemigroup, Subsemigroup.mem_center_iff, mem_center_iff
-/
theorem mem_center_iff {a : A} : a in center R A ↔ forall b : A, b * a = a * b :=
  Subsemigroup.mem_center_iff

end Center

section Centralizer

@[simp]
/--
theorem `_root_.Set.algebraMap_mem_centralizer` / 定理 `_root_.Set.algebraMap_mem_centralizer`

English:
theorem _root_.Set.algebraMap_mem_centralizer
  given: {s : Set A} (r : R)
  proof: fun _a _h => (Algebra.commutes _ _).symm

中文:
定理 _root_.Set.algebraMap_mem_centralizer
  条件: {s : Set A} (r : R)
  证明: fun _a _h => (Algebra.commutes _ _).symm

Depends on / 依赖: Algebra, Algebra.commutes, commutes
-/
theorem _root_.Set.algebraMap_mem_centralizer {s : Set A} (r : R) :
    algebraMap R A r in s.centralizer :=
  fun _a _h => (Algebra.commutes _ _).symm

variable (R)

/--
Definition of `centralizer` / `centralizer` 的定义

English:
definition centralizer
  signature: (s : Set A)
  body: { Subsemiring.centralizer s with algebraMap_mem' := Set.algebraMap_mem_centralizer }

@[simp, norm_cast]

中文:
定义 centralizer
  签名: (s : Set A)
  定义体: { Subsemiring.centralizer s with algebraMap_mem' := Set.algebraMap_mem_centralizer }

@[simp, norm_cast]

Depends on / 依赖: Set.algebraMap_mem_centralizer, Subsemiring, Subsemiring.centralizer, algebraMap_mem, algebraMap_mem_centralizer, centralizer
-/
def centralizer (s : Set A) : Subalgebra R A :=
  { Subsemiring.centralizer s with algebraMap_mem' := Set.algebraMap_mem_centralizer }

@[simp, norm_cast]
/--
theorem `coe_centralizer` / 定理 `coe_centralizer`

English:
theorem coe_centralizer
  given: (s : Set A)
  statement: (centralizer R s : Set A) = s.centralizer
  proof: rfl

中文:
定理 coe_centralizer
  条件: (s : Set A)
  结论: (centralizer R s : Set A) = s.centralizer
  证明: rfl
-/
theorem coe_centralizer (s : Set A) : (centralizer R s : Set A) = s.centralizer :=
  rfl

/--
theorem `mem_centralizer_iff` / 定理 `mem_centralizer_iff`

English:
theorem mem_centralizer_iff
  given: {s : Set A} {z : A}
  statement: z in centralizer R s ↔ forall g in s, g * z = z * g
  proof: Iff.rfl

中文:
定理 mem_centralizer_iff
  条件: {s : Set A} {z : A}
  结论: z in centralizer R s ↔ 对任意 g in s, g * z = z * g
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_centralizer_iff {s : Set A} {z : A} : z in centralizer R s ↔ forall g in s, g * z = z * g :=
  Iff.rfl

/--
theorem `center_le_centralizer` / 定理 `center_le_centralizer`

English:
theorem center_le_centralizer
  given: (s)
  statement: center R A <= centralizer R s
  proof: s.center_subset_centralizer

中文:
定理 center_le_centralizer
  条件: (s)
  结论: center R A <= centralizer R s
  证明: s.center_subset_centralizer

Depends on / 依赖: center_subset_centralizer, s.center_subset_centralizer
-/
theorem center_le_centralizer (s) : center R A <= centralizer R s :=
  s.center_subset_centralizer

/--
theorem `centralizer_le` / 定理 `centralizer_le`

English:
theorem centralizer_le
  given: (s t : Set A) (h : s subseteq t)
  statement: centralizer R t <= centralizer R s
  proof: Set.centralizer_subset h

@[simp]

中文:
定理 centralizer_le
  条件: (s t : Set A) (h : s subseteq t)
  结论: centralizer R t <= centralizer R s
  证明: Set.centralizer_subset h

@[simp]

Depends on / 依赖: Set.centralizer_subset, centralizer_subset
-/
theorem centralizer_le (s t : Set A) (h : s subseteq t) : centralizer R t <= centralizer R s :=
  Set.centralizer_subset h

@[simp]
/--
theorem `centralizer_univ` / 定理 `centralizer_univ`

English:
theorem centralizer_univ
  statement: centralizer R Set.univ = center R A
  proof: SetLike.ext' (Set.centralizer_univ A)

中文:
定理 centralizer_univ
  结论: centralizer R Set.univ = center R A
  证明: SetLike.ext' (Set.centralizer_univ A)

Depends on / 依赖: Set.centralizer_univ, SetLike, SetLike.ext, centralizer_univ
-/
theorem centralizer_univ : centralizer R Set.univ = center R A :=
  SetLike.ext' (Set.centralizer_univ A)

/--
lemma `le_centralizer_centralizer` / 引理 `le_centralizer_centralizer`

English:
lemma le_centralizer_centralizer
  given: {s : Subalgebra R A}
  proof: Set.subset_centralizer_centralizer

@[simp]

中文:
引理 le_centralizer_centralizer
  条件: {s : Subalgebra R A}
  证明: Set.subset_centralizer_centralizer

@[simp]

Depends on / 依赖: Set.subset_centralizer_centralizer, subset_centralizer_centralizer
-/
lemma le_centralizer_centralizer {s : Subalgebra R A} :
    s <= centralizer R (centralizer R (s : Set A)) :=
  Set.subset_centralizer_centralizer

@[simp]
/--
lemma `centralizer_centralizer_centralizer` / 引理 `centralizer_centralizer_centralizer`

English:
lemma centralizer_centralizer_centralizer
  given: {s : Set A}
  proof: by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

中文:
引理 centralizer_centralizer_centralizer
  条件: {s : Set A}
  证明: by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

Depends on / 依赖: Set.centralizer_centralizer_centralizer, SetLike, SetLike.coe_injective, centralizer_centralizer_centralizer, coe_centralizer, coe_injective
-/
lemma centralizer_centralizer_centralizer {s : Set A} :
    centralizer R s.centralizer.centralizer = centralizer R s := by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

end Centralizer

end Subalgebra

section Nat

variable {R : Type*} [Semiring R]

/-- A subsemiring is an `ℕ`-subalgebra. -/
@[simps toSubsemiring]
/--
Definition of `subalgebraOfSubsemiring` / `subalgebraOfSubsemiring` 的定义

English:
definition subalgebraOfSubsemiring
  signature: (S : Subsemiring R)
  body: { S with algebraMap_mem' := fun i => natCast_mem S i }

@[simp]

中文:
定义 subalgebraOfSubsemiring
  签名: (S : Subsemiring R)
  定义体: { S with algebraMap_mem' := fun i => natCast_mem S i }

@[simp]

Depends on / 依赖: algebraMap_mem, natCast_mem
-/
def subalgebraOfSubsemiring (S : Subsemiring R) : Subalgebra Nat R :=
  { S with algebraMap_mem' := fun i => natCast_mem S i }

@[simp]
/--
theorem `mem_subalgebraOfSubsemiring` / 定理 `mem_subalgebraOfSubsemiring`

English:
theorem mem_subalgebraOfSubsemiring
  given: {x : R} {S : Subsemiring R}
  proof: Iff.rfl

中文:
定理 mem_subalgebraOfSubsemiring
  条件: {x : R} {S : Subsemiring R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_subalgebraOfSubsemiring {x : R} {S : Subsemiring R} :
    x in subalgebraOfSubsemiring S ↔ x in S :=
  Iff.rfl

end Nat

section Int

variable {R : Type*} [Ring R]

/-- A subring is a `ℤ`-subalgebra. -/
@[simps toSubsemiring]
/--
Definition of `subalgebraOfSubring` / `subalgebraOfSubring` 的定义

English:
definition subalgebraOfSubring
  signature: (S : Subring R)
  body: { S with
    algebraMap_mem' := fun i =>
      Int.induction_on i (by simp)
        (fun i ih => by simpa using S.add_mem ih S.one_mem) fun i ih =>
        show ((-i - 1 : Int) : R) in S by
          rw [Int.cast_sub]; rw [Int.cast_one]
          exact S.sub_mem ih S.one_mem }

中文:
定义 subalgebraOfSubring
  签名: (S : Subring R)
  定义体: { S with
    algebraMap_mem' := fun i =>
      Int.induction_on i (by simp)
        (fun i ih => by simpa using S.add_mem ih S.one_mem) fun i ih =>
        show ((-i - 1 : Int) : R) in S by
          rw [Int.cast_sub]; rw [Int.cast_one]
          exact S.sub_mem ih S.one_mem }

Depends on / 依赖: Int.cast_one, Int.cast_sub, Int.induction_on, S.add_mem, S.one_mem, S.sub_mem, add_mem, algebraMap_mem, cast_one, cast_sub, induction_on, one_mem, sub_mem
-/
def subalgebraOfSubring (S : Subring R) : Subalgebra Int R :=
  { S with
    algebraMap_mem' := fun i =>
      Int.induction_on i (by simp)
        (fun i ih => by simpa using S.add_mem ih S.one_mem) fun i ih =>
        show ((-i - 1 : Int) : R) in S by
          rw [Int.cast_sub]; rw [Int.cast_one]
          exact S.sub_mem ih S.one_mem }

variable {S : Type*} [Semiring S]

@[simp]
/--
theorem `mem_subalgebraOfSubring` / 定理 `mem_subalgebraOfSubring`

English:
theorem mem_subalgebraOfSubring
  given: {x : R} {S : Subring R}
  statement: x in subalgebraOfSubring S ↔ x in S
  proof: Iff.rfl

中文:
定理 mem_subalgebraOfSubring
  条件: {x : R} {S : Subring R}
  结论: x in subalgebraOfSubring S ↔ x in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_subalgebraOfSubring {x : R} {S : Subring R} : x in subalgebraOfSubring S ↔ x in S :=
  Iff.rfl

end Int

section Equalizer

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- The equalizer of two R-algebra homomorphisms -/
@[simps coe toSubsemiring]
/--
Definition of `equalizer` / `equalizer` 的定义

English:
definition equalizer
  signature: (ϕ ψ : A ->ₐ[R] B)
  body: { a | ϕ a = ψ a }
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]
  one_mem' := by simp only [Set.mem_ofPred_eq, map_one]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq]; rw [map_add]; rw [map_add]; rw [hx]; rw [hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy 

中文:
定义 equalizer
  签名: (ϕ ψ : A ->ₐ[R] B)
  定义体: { a | ϕ a = ψ a }
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]
  one_mem' := by simp only [Set.mem_ofPred_eq, map_one]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq]; rw [map_add]; rw [map_add]; rw [hx]; rw [hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy 
-/
def equalizer (ϕ ψ : A ->ₐ[R] B) : Subalgebra R A where
  carrier := { a | ϕ a = ψ a }
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]
  one_mem' := by simp only [Set.mem_ofPred_eq, map_one]
  add_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq]; rw [map_add]; rw [map_add]; rw [hx]; rw [hy]
  mul_mem' {x y} (hx : ϕ x = ψ x) (hy : ϕ y = ψ y) := by
    rw [Set.mem_ofPred_eq]; rw [map_mul]; rw [map_mul]; rw [hx]; rw [hy]
  algebraMap_mem' x := by
    simp only [Set.mem_ofPred_eq, AlgHomClass.commutes]

@[simp]
/--
theorem `mem_equalizer` / 定理 `mem_equalizer`

English:
theorem mem_equalizer
  given: (φ ψ : A ->ₐ[R] B) (x : A)
  statement: x in equalizer φ ψ ↔ φ x = ψ x
  proof: Iff.rfl

中文:
定理 mem_equalizer
  条件: (φ ψ : A ->ₐ[R] B) (x : A)
  结论: x in equalizer φ ψ ↔ φ x = ψ x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_equalizer (φ ψ : A ->ₐ[R] B) (x : A) : x in equalizer φ ψ ↔ φ x = ψ x :=
  Iff.rfl

/--
theorem `equalizer_toSubmodule` / 定理 `equalizer_toSubmodule`

English:
theorem equalizer_toSubmodule
  given: {φ ψ : A ->ₐ[R] B}
  proof: rfl

中文:
定理 equalizer_toSubmodule
  条件: {φ ψ : A ->ₐ[R] B}
  证明: rfl
-/
theorem equalizer_toSubmodule {φ ψ : A ->ₐ[R] B} :
    Subalgebra.toSubmodule (equalizer φ ψ) = LinearMap.eqLocus
      (LinearMapClass.linearMap φ) (LinearMapClass.linearMap ψ) := rfl

/--
theorem `le_equalizer` / 定理 `le_equalizer`

English:
theorem le_equalizer
  given: {φ ψ : A ->ₐ[R] B} {S : Subalgebra R A}
  proof: Iff.rfl

中文:
定理 le_equalizer
  条件: {φ ψ : A ->ₐ[R] B} {S : Subalgebra R A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_equalizer {φ ψ : A ->ₐ[R] B} {S : Subalgebra R A} :
    S <= equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl

end AlgHom

end Equalizer

section MapComap

namespace Subalgebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/--
theorem `comap_map_eq_self_of_injective` / 定理 `comap_map_eq_self_of_injective`

English:
theorem comap_map_eq_self_of_injective
  proof: SetLike.coe_injective (Set.preimage_image_eq _ hf)

中文:
定理 comap_map_eq_self_of_injective
  证明: SetLike.coe_injective (Set.preimage_image_eq _ hf)

Depends on / 依赖: Set.preimage_image_eq, SetLike, SetLike.coe_injective, coe_injective, preimage_image_eq
-/
theorem comap_map_eq_self_of_injective
    {f : A ->ₐ[R] B} (hf : Function.Injective f) (S : Subalgebra R A) : (S.map f).comap f = S :=
  SetLike.coe_injective (Set.preimage_image_eq _ hf)

end Subalgebra

end MapComap

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/--
Definition of `NonUnitalSubalgebra.toSubalgebra` / `NonUnitalSubalgebra.toSubalgebra` 的定义

English:
definition NonUnitalSubalgebra.toSubalgebra
  signature: (S : NonUnitalSubalgebra R A) (h1 : (1 : A) in S)
  body: { S with
    one_mem' := h1
    algebraMap_mem' := fun r =>
      (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1 }

中文:
定义 NonUnitalSubalgebra.toSubalgebra
  签名: (S : NonUnitalSubalgebra R A) (h1 : (1 : A) in S)
  定义体: { S with
    one_mem' := h1
    algebraMap_mem' := fun r =>
      (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1 }

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, SMulMemClass, SMulMemClass.smul_mem, algebraMap_eq_smul_one, algebraMap_mem, one_mem, smul_mem
-/
def NonUnitalSubalgebra.toSubalgebra (S : NonUnitalSubalgebra R A) (h1 : (1 : A) in S) :
    Subalgebra R A :=
  { S with
    one_mem' := h1
    algebraMap_mem' := fun r =>
      (Algebra.algebraMap_eq_smul_one (R := R) (A := A) r).symm ▸ SMulMemClass.smul_mem r h1 }

/--
lemma `Subalgebra.toNonUnitalSubalgebra_toSubalgebra` / 引理 `Subalgebra.toNonUnitalSubalgebra_toSubalgebra`

English:
lemma Subalgebra.toNonUnitalSubalgebra_toSubalgebra
  given: (S : Subalgebra R A)
  proof: by cases S; rfl

中文:
引理 Subalgebra.toNonUnitalSubalgebra_toSubalgebra
  条件: (S : Subalgebra R A)
  证明: by cases S; rfl
-/
lemma Subalgebra.toNonUnitalSubalgebra_toSubalgebra (S : Subalgebra R A) :
    S.toNonUnitalSubalgebra.toSubalgebra S.one_mem = S := by cases S; rfl

/--
lemma `NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra` / 引理 `NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra`

English:
lemma NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra
  statement: (S : NonUnitalSubalgebra R A)
  proof: by
  cases S; rfl

中文:
引理 NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra
  结论: (S : NonUnitalSubalgebra R A)
  证明: by
  cases S; rfl
-/
lemma NonUnitalSubalgebra.toSubalgebra_toNonUnitalSubalgebra (S : NonUnitalSubalgebra R A)
    (h1 : (1 : A) in S) : (NonUnitalSubalgebra.toSubalgebra S h1).toNonUnitalSubalgebra = S := by
  cases S; rfl
