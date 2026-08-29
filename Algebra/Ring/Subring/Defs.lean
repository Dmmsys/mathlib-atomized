/-
Copyright (c) 2020 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.RingTheory.NonUnitalSubring.Defs

/-!
# Subrings

Let `R` be a ring. This file defines the "bundled" subring type `Subring R`, a type
whose terms correspond to subrings of `R`. This is the preferred way to talk
about subrings in mathlib. Unbundled subrings (`s : Set R` and `IsSubring s`)
are not in this file, and they will ultimately be deprecated.

We prove that subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set R` to `Subring R`, sending a subset of `R`
to the subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [Ring R] (S : Type u) [Ring S] (f g : R →+* S)`
`(A : Subring R) (B : Subring S) (s : Set R)`

* `Subring R` : the type of subrings of a ring `R`.

* `instance : CompleteLattice (Subring R)` : the complete lattice structure on the subrings.

* `Subring.center` : the center of a ring `R`.

* `Subring.closure` : subring closure of a set, i.e., the smallest subring that includes the set.

* `Subring.gi` : `closure : Set M → Subring M` and coercion `(↑) : Subring M → et M`
  form a `GaloisInsertion`.

* `comap f B : Subring A` : the preimage of a subring `B` along the ring homomorphism `f`

* `map f A : Subring B` : the image of a subring `A` along the ring homomorphism `f`.

* `prod A B : Subring (R × S)` : the product of subrings

* `f.range : Subring B` : the range of the ring homomorphism `f`.

* `eqLocus f g : Subring R` : given ring homomorphisms `f g : R →+* S`,
     the subring of `R` where `f x = g x`

## Implementation notes

A subring is implemented as a subsemiring which is also an additive subgroup.
The initial PR was as a submonoid which is also an additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subring's underlying set.

## Tags
subring, subrings
-/

@[expose] public section

assert_not_exists RelIso Even IsOrderedMonoid

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

section SubringClass

/--
Definition of `SubringClass` / `SubringClass` 的定义

English:
class SubringClass
  parameters: (S : Type*) (R : outParam (Type u)) [NonAssocRing R] [SetLike S R]
  extends: SubsemiringClass S R, NegMemClass S R
  (no additional axioms)

中文:
类 子环类
  参数: (S : 类型) (R : outParam (类型u)) [非结合环 R] [集合状 S R]
  继承: 子半环类 S R, NegMem类 S R
  (无附加公理)
-/
class SubringClass (S : Type*) (R : outParam (Type u)) [NonAssocRing R] [SetLike S R] : Prop
    extends SubsemiringClass S R, NegMemClass S R

-- See note [lower instance priority]
instance (priority := 100) SubringClass.addSubgroupClass (S : Type*) (R : Type u)
    [SetLike S R] [NonAssocRing R] [h : SubringClass S R] : AddSubgroupClass S R :=
  { h with }

instance (priority := 100) SubringClass.nonUnitalSubringClass (S : Type*) (R : Type u)
    [SetLike S R] [NonAssocRing R] [SubringClass S R] : NonUnitalSubringClass S R where

variable [SetLike S R] [hSR : SubringClass S R] (s : S)

@[simp, aesop safe (rule_sets := [SetLike])]
/--
theorem `intCast_mem` / 定理 `intCast_mem`

English:
theorem intCast_mem
  given: (n : Int)
  statement: (n : R) in s
  proof: by simp only [← zsmul_one, zsmul_mem, one_mem]

中文:
定理 intCast_mem
  条件: (n : 整数)
  结论: (n : R) in s
  证明: by simp only [← zsmul_one, zsmul_mem, one_mem]

Depends on / 依赖: one_mem, zsmul_mem, zsmul_one
-/
theorem intCast_mem (n : Int) : (n : R) in s := by simp only [← zsmul_one, zsmul_mem, one_mem]

namespace SubringClass

instance (priority := 75) toHasIntCast : IntCast s :=
  ⟨fun n => ⟨n, intCast_mem s n⟩⟩

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a non-unital ring inherits a non-unital ring structure -/
instance (priority := 75) toNonAssocRing (s : S) : NonAssocRing s := fast_instance%
  Subtype.coe_injective.nonAssocRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a ring inherits a ring structure -/
instance (priority := 75) toRing {R} [Ring R] [SetLike S R] [SubringClass S R] :
    Ring s := fast_instance%
  Subtype.coe_injective.ring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a `NonAssocCommRing` is a `NonAssocCommRing`. -/
instance (priority := 75) toNonAssocCommRing {R} [NonAssocCommRing R] [SetLike S R]
    [SubringClass S R] : NonAssocCommRing s := fast_instance%
  Subtype.coe_injective.nonAssocCommRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a `CommRing` is a `CommRing`. -/
instance (priority := 75) toCommRing {R} [CommRing R] [SetLike S R] [SubringClass S R] :
    CommRing s := fast_instance%
  Subtype.coe_injective.commRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a domain is a domain. -/
instance (priority := 75) {R} [Ring R] [IsDomain R] [SetLike S R] [SubringClass S R] : IsDomain s :=
  NoZeroDivisors.to_isDomain _

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (s : S)
  body: { SubmonoidClass.subtype s, AddSubgroupClass.subtype s with
    toFun := (↑) }

中文:
定义 subtype
  签名: (s : S)
  定义体: { SubmonoidClass.subtype s, AddSubgroupClass.subtype s with
    toFun := (↑) }

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.subtype, SubmonoidClass, SubmonoidClass.subtype, subtype
-/
def subtype (s : S) : s ->+* R :=
  { SubmonoidClass.subtype s, AddSubgroupClass.subtype s with
    toFun := (↑) }

variable {s} in
@[simp]
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: (x : s)
  proof: rfl

中文:
引理 subtype_apply
  条件: (x : s)
  证明: rfl
-/
lemma subtype_apply (x : s) :
    SubringClass.subtype s x = x := rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  proof: Subtype.coe_injective

@[simp]

中文:
引理 subtype_injective
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective :
    Function.Injective (subtype s) :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: (subtype s : s -> R) = ((↑) : s -> R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_subtype
  结论: (subtype s : s -> R) = ((↑) : s -> R)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_subtype : (subtype s : s -> R) = ((↑) : s -> R) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: ((n : s) : R) = n
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: ((n : s) : R) = n
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_natCast (n : Nat) : ((n : s) : R) = n := rfl

@[simp, norm_cast]
/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: (n : Int)
  statement: ((n : s) : R) = n
  proof: rfl

中文:
定理 coe_intCast
  条件: (n : 整数)
  结论: ((n : s) : R) = n
  证明: rfl
-/
theorem coe_intCast (n : Int) : ((n : s) : R) = n := rfl

end SubringClass

end SubringClass

/-- `Subring R` is the type of subrings of `R`. A subring of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
@[wikidata Q929536]
/--
Definition of `Subring` / `Subring` 的定义

English:
structure Subring
  parameters: (R : Type u) [NonAssocRing R]
  extends: Subsemiring R, AddSubgroup R
  (no additional axioms)

中文:
结构 子环
  参数: (R : 类型u) [非结合环 R]
  继承: 子半环 R, 加法子群 R
  (无附加公理)
-/
structure Subring (R : Type u) [NonAssocRing R] extends Subsemiring R, AddSubgroup R

/-- Reinterpret a `Subring` as a `Subsemiring`. -/
add_decl_doc Subring.toSubsemiring

/-- Reinterpret a `Subring` as an `AddSubgroup`. -/
add_decl_doc Subring.toAddSubgroup

namespace Subring

/--
lemma `toSubsemiring_injective` / 引理 `toSubsemiring_injective`

English:
lemma toSubsemiring_injective
  statement: (toSubsemiring : Subring R -> Subsemiring R).Injective
  proof: fun ⟨s, hs⟩ t => by congr!

中文:
引理 toSubsemiring_injective
  结论: (toSubsemiring : 子环 R -> 子半环 R).单射
  证明: fun ⟨s, hs⟩ t => by congr!
-/
lemma toSubsemiring_injective : (toSubsemiring : Subring R -> Subsemiring R).Injective :=
  fun ⟨s, hs⟩ t => by congr!

/--
lemma `toSubsemiring_inj` / 引理 `toSubsemiring_inj`

English:
lemma toSubsemiring_inj
  given: {s t : Subring R}
  statement: s.toSubsemiring = t.toSubsemiring ↔ s = t
  proof: toSubsemiring_injective.eq_iff

中文:
引理 toSubsemiring_inj
  条件: {s t : 子环 R}
  结论: s.toSubsemiring = t.toSubsemiring ↔ s = t
  证明: toSubsemiring_injective.eq_iff
-/
@[simp] lemma toSubsemiring_inj {s t : Subring R} : s.toSubsemiring = t.toSubsemiring ↔ s = t :=
  toSubsemiring_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Subring R) R
  body: s.carrier
  coe_injective := SetLike.coe_injective.comp toSubsemiring_injective

中文:
实例 :
  签名: 集合状 (子环 R) R
  定义体: s.carrier
  coe_injective := SetLike.coe_injective.comp toSubsemiring_injective

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (Subring R) R where
  coe s := s.carrier
  coe_injective := SetLike.coe_injective.comp toSubsemiring_injective

/--
lemma `toAddSubgroup_injective` / 引理 `toAddSubgroup_injective`

English:
lemma toAddSubgroup_injective
  statement: (toAddSubgroup : Subring R -> AddSubgroup R).Injective
  proof: fun _ _ h => SetLike.ext (SetLike.ext_iff.mp h :)

中文:
引理 toAddSubgroup_injective
  结论: (toAddSubgroup : 子环 R -> 加法子群 R).单射
  证明: fun _ _ h => SetLike.ext (SetLike.ext_iff.mp h :)

Depends on / 依赖: SetLike, SetLike.ext, SetLike.ext_iff.mp, ext_iff
-/
lemma toAddSubgroup_injective : (toAddSubgroup : Subring R -> AddSubgroup R).Injective :=
  fun _ _ h => SetLike.ext (SetLike.ext_iff.mp h :)

/--
lemma `toSubmonoid_injective` / 引理 `toSubmonoid_injective`

English:
lemma toSubmonoid_injective
  statement: (fun s : Subring R => s.toSubmonoid).Injective
  proof: fun _ _ h => SetLike.ext (SetLike.ext_iff.mp h :)

中文:
引理 toSubmonoid_injective
  结论: (fun s : 子环 R => s.toSubmonoid).单射
  证明: fun _ _ h => SetLike.ext (SetLike.ext_iff.mp h :)

Depends on / 依赖: SetLike, SetLike.ext, SetLike.ext_iff.mp, ext_iff
-/
lemma toSubmonoid_injective : (fun s : Subring R => s.toSubmonoid).Injective :=
  fun _ _ h => SetLike.ext (SetLike.ext_iff.mp h :)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Subring R)
  body: .ofSetLike (Subring R) R

initialize_simps_projections Subring (carrier -> coe, as_prefix coe)

中文:
实例 :
  签名: 偏序 (子环 R)
  定义体: .ofSetLike (Subring R) R

initialize_simps_projections Subring (carrier -> coe, as_prefix coe)

Depends on / 依赖: Subring, ofSetLike
-/
instance : PartialOrder (Subring R) := .ofSetLike (Subring R) R

initialize_simps_projections Subring (carrier -> coe, as_prefix coe)

/-- The actual `Subring` obtained from an element of a `SubringClass`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S R : Type*} [NonAssocRing R] [SetLike S R] [SubringClass S R]
  body: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  neg_mem' := neg_mem
  one_mem' := one_mem _

中文:
定义 ofClass
  签名: {S R : 类型} [非结合环 R] [集合状 S R] [子环类 S R]
  定义体: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  neg_mem' := neg_mem
  one_mem' := one_mem _
-/
def ofClass {S R : Type*} [NonAssocRing R] [SetLike S R] [SubringClass S R]
    (s : S) : Subring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  neg_mem' := neg_mem
  one_mem' := one_mem _

instance (priority := 100) : CanLift (Set R) (Subring R) (↑)
    (fun s => 0 in s ∧ (forall {x y}, x in s -> y in s -> x + y in s) ∧ 1 in s ∧
      (forall {x y}, x in s -> y in s -> x * y in s) ∧ forall {x}, x in s -> -x in s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        one_mem' := h.2.2.1
        mul_mem' := h.2.2.2.1
        neg_mem' := h.2.2.2.2 },
      rfl ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubringClass (Subring R) R
  body: s.zero_mem'
  add_mem {s} := s.add_mem'
  one_mem s := s.one_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

中文:
实例 :
  签名: 子环类 (子环 R) R
  定义体: s.zero_mem'
  add_mem {s} := s.add_mem'
  one_mem s := s.one_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

Depends on / 依赖: s.zero_mem, zero_mem
-/
instance : SubringClass (Subring R) R where
  zero_mem s := s.zero_mem'
  add_mem {s} := s.add_mem'
  one_mem s := s.one_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

/-- Turn a `Subring` into a `NonUnitalSubring` by forgetting that it contains `1`. -/
@[reducible]
/--
Definition of `toNonUnitalSubring` / `toNonUnitalSubring` 的定义

English:
definition toNonUnitalSubring
  signature: (S : Subring R)
  body: S

@[simp]

中文:
定义 toNonUnitalSubring
  签名: (S : 子环 R)
  定义体: S

@[simp]
-/
def toNonUnitalSubring (S : Subring R) : NonUnitalSubring R where __ := S

@[simp]
/--
theorem `mem_toSubsemiring` / 定理 `mem_toSubsemiring`

English:
theorem mem_toSubsemiring
  given: {s : Subring R} {x : R}
  statement: x in s.toSubsemiring ↔ x in s
  proof: Iff.rfl

中文:
定理 mem_toSubsemiring
  条件: {s : 子环 R} {x : R}
  结论: x in s.toSubsemiring ↔ x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubsemiring {s : Subring R} {x : R} : x in s.toSubsemiring ↔ x in s := Iff.rfl

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : Subring R} {x : R}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_carrier
  条件: {s : 子环 R} {x : R}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : Subring R} {x : R} : x in s.carrier ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {S : Subsemiring R} {x : R} (h)
  statement: x in (⟨S, h⟩ : Subring R) ↔ x in S
  proof: Iff.rfl

中文:
定理 mem_mk
  条件: {S : 子半环 R} {x : R} (h)
  结论: x in (⟨S, h⟩ : 子环 R) ↔ x in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {S : Subsemiring R} {x : R} (h) : x in (⟨S, h⟩ : Subring R) ↔ x in S := Iff.rfl

/--
theorem `coe_set_mk` / 定理 `coe_set_mk`

English:
theorem coe_set_mk
  given: (S : Subsemiring R) (h)
  statement: ((⟨S, h⟩ : Subring R) : Set R) = S
  proof: rfl

@[simp]

中文:
定理 coe_set_mk
  条件: (S : 子半环 R) (h)
  结论: ((⟨S, h⟩ : 子环 R) : 集合 R) = S
  证明: rfl

@[simp]
-/
@[simp] theorem coe_set_mk (S : Subsemiring R) (h) : ((⟨S, h⟩ : Subring R) : Set R) = S := rfl

@[simp]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {S S' : Subsemiring R} (h₁ h₂)
  proof: Iff.rfl

中文:
定理 mk_le_mk
  条件: {S S' : 子半环 R} (h₁ h₂)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mk_le_mk {S S' : Subsemiring R} (h₁ h₂) :
    (⟨S, h₁⟩ : Subring R) <= (⟨S', h₂⟩ : Subring R) ↔ S <= S' :=
  Iff.rfl

/--
lemma `one_mem_toNonUnitalSubring` / 引理 `one_mem_toNonUnitalSubring`

English:
lemma one_mem_toNonUnitalSubring
  given: (S : Subring R)
  statement: 1 in S.toNonUnitalSubring
  proof: S.one_mem

中文:
引理 one_mem_toNonUnitalSubring
  条件: (S : 子环 R)
  结论: 1 in S.toNonUnitalSubring
  证明: S.one_mem

Depends on / 依赖: S.one_mem, one_mem
-/
lemma one_mem_toNonUnitalSubring (S : Subring R) : 1 in S.toNonUnitalSubring := S.one_mem

/-- Two subrings are equal if they have the same elements. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : Subring R} (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

中文:
定理 ext
  条件: {S T : 子环 R} (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : Subring R} (h : forall x, x in S ↔ x in T) : S = T :=
  SetLike.ext h

/-- Copy of a subring with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps coe toSubsemiring]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : Subring R) (s : Set R) (hs : s = ↑S)
  body: { S.toSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }

中文:
定义 copy
  签名: (S : 子环 R) (s : 集合 R) (hs : s = ↑S)
  定义体: { S.toSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }
-/
protected def copy (S : Subring R) (s : Set R) (hs : s = ↑S) : Subring R :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : Subring R) (s : Set R) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : 子环 R) (s : 集合 R) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : Subring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

/-- Construct a `Subring R` from a set `s`, a submonoid `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
@[simps! coe]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (s : Set R) (sm : Submonoid R) (sa : AddSubgroup R) (hm : ↑sm = s)
  body: { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]

中文:
定义 mk'
  签名: (s : 集合 R) (sm : 子幺半群 R) (sa : 加法子群 R) (hm : ↑sm = s)
  定义体: { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]
-/
protected def mk' (s : Set R) (sm : Submonoid R) (sa : AddSubgroup R) (hm : ↑sm = s)
    (ha : ↑sa = s) : Subring R :=
  { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]
/--
theorem `mem_mk'` / 定理 `mem_mk'`

English:
theorem mem_mk'
  statement: {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk'
  结论: {s : 集合 R} {sm : 子幺半群 R} (hm : ↑sm = s) {sa : 加法子群 R} (ha : ↑sa = s)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
    {x : R} : x in Subring.mk' s sm sa hm ha ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `mk'_toSubmonoid` / 定理 `mk'_toSubmonoid`

English:
theorem mk'_toSubmonoid
  statement: {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
  proof: SetLike.coe_injective hm.symm

@[simp]

中文:
定理 mk'_toSubmonoid
  结论: {s : 集合 R} {sm : 子幺半群 R} (hm : ↑sm = s) {sa : 加法子群 R}
  证明: SetLike.coe_injective hm.symm

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, hm.symm
-/
theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm

@[simp]
/--
theorem `mk'_toAddSubgroup` / 定理 `mk'_toAddSubgroup`

English:
theorem mk'_toAddSubgroup
  statement: {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
  proof: SetLike.coe_injective ha.symm

中文:
定理 mk'_toAddSubgroup
  结论: {s : 集合 R} {sm : 子幺半群 R} (hm : ↑sm = s) {sa : 加法子群 R}
  证明: SetLike.coe_injective ha.symm
-/
theorem mk'_toAddSubgroup {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toAddSubgroup = sa :=
  SetLike.coe_injective ha.symm

end Subring

/-- A `Subsemiring` containing -1 is a `Subring`. -/
@[simps toSubsemiring]
/--
Definition of `Subsemiring.toSubring` / `Subsemiring.toSubring` 的定义

English:
definition Subsemiring.toSubring
  signature: (s : Subsemiring R) (hneg : (-1 : R) in s)
  body: s
  neg_mem' h := by
    rw [← neg_one_mul]
    exact mul_mem hneg h

中文:
定义 子半环.toSubring
  签名: (s : 子半环 R) (hneg : (-1 : R) in s)
  定义体: s
  neg_mem' h := by
    rw [← neg_one_mul]
    exact mul_mem hneg h
-/
def Subsemiring.toSubring (s : Subsemiring R) (hneg : (-1 : R) in s) : Subring R where
  toSubsemiring := s
  neg_mem' h := by
    rw [← neg_one_mul]
    exact mul_mem hneg h

namespace Subring

variable (s : Subring R)

/--
theorem `one_mem` / 定理 `one_mem`

English:
theorem one_mem
  statement: (1 : R) in s
  proof: one_mem _

中文:
定理 one_mem
  结论: (1 : R) in s
  证明: one_mem _
-/
protected theorem one_mem : (1 : R) in s :=
  one_mem _

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : R) in s
  proof: zero_mem _

中文:
定理 zero_mem
  结论: (0 : R) in s
  证明: zero_mem _
-/
protected theorem zero_mem : (0 : R) in s :=
  zero_mem _

/--
theorem `mul_mem` / 定理 `mul_mem`

English:
theorem mul_mem
  given: {x y : R}
  statement: x in s -> y in s -> x * y in s
  proof: mul_mem

中文:
定理 mul_mem
  条件: {x y : R}
  结论: x in s -> y in s -> x * y in s
  证明: mul_mem
-/
protected theorem mul_mem {x y : R} : x in s -> y in s -> x * y in s :=
  mul_mem

/--
theorem `add_mem` / 定理 `add_mem`

English:
theorem add_mem
  given: {x y : R}
  statement: x in s -> y in s -> x + y in s
  proof: add_mem

中文:
定理 add_mem
  条件: {x y : R}
  结论: x in s -> y in s -> x + y in s
  证明: add_mem
-/
protected theorem add_mem {x y : R} : x in s -> y in s -> x + y in s :=
  add_mem

/--
theorem `neg_mem` / 定理 `neg_mem`

English:
theorem neg_mem
  given: {x : R}
  statement: x in s -> -x in s
  proof: neg_mem

中文:
定理 neg_mem
  条件: {x : R}
  结论: x in s -> -x in s
  证明: neg_mem
-/
protected theorem neg_mem {x : R} : x in s -> -x in s :=
  neg_mem

/--
theorem `sub_mem` / 定理 `sub_mem`

English:
theorem sub_mem
  given: {x y : R} (hx : x in s) (hy : y in s)
  statement: x - y in s
  proof: sub_mem hx hy

中文:
定理 sub_mem
  条件: {x y : R} (hx : x in s) (hy : y in s)
  结论: x - y in s
  证明: sub_mem hx hy
-/
protected theorem sub_mem {x y : R} (hx : x in s) (hy : y in s) : x - y in s :=
  sub_mem hx hy

/--
Instance `toRing` / 实例 `toRing`

English:
instance toRing
  signature: {R} [Ring R] (s : Subring R)
  body: SubringClass.toRing s

中文:
实例 toRing
  签名: {R} [环 R] (s : 子环 R)
  定义体: SubringClass.toRing s

Depends on / 依赖: SubringClass, SubringClass.toRing, toRing
-/
instance toRing {R} [Ring R] (s : Subring R) : Ring s := SubringClass.toRing s

/--
theorem `zsmul_mem` / 定理 `zsmul_mem`

English:
theorem zsmul_mem
  given: {x : R} (hx : x in s) (n : Int)
  statement: n • x in s
  proof: zsmul_mem hx n

中文:
定理 zsmul_mem
  条件: {x : R} (hx : x in s) (n : 整数)
  结论: n • x in s
  证明: zsmul_mem hx n
-/
protected theorem zsmul_mem {x : R} (hx : x in s) (n : Int) : n • x in s :=
  zsmul_mem hx n

/--
theorem `pow_mem` / 定理 `pow_mem`

English:
theorem pow_mem
  given: {R : Type*} [Ring R] (s : Subring R) {x : R} (hx : x in s) (n : Nat)
  proof: pow_mem hx n

@[simp, norm_cast]

中文:
定理 pow_mem
  条件: {R : 类型} [环 R] (s : 子环 R) {x : R} (hx : x in s) (n : 自然数)
  证明: pow_mem hx n

@[simp, norm_cast]
-/
protected theorem pow_mem {R : Type*} [Ring R] (s : Subring R) {x : R} (hx : x in s) (n : Nat) :
    x ^ n in s := pow_mem hx n

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : s)
  statement: (↑(x + y) : R) = ↑x + ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (x y : s)
  结论: (↑(x + y) : R) = ↑x + ↑y
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (x : s)
  statement: (↑(-x) : R) = -↑x
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_neg
  条件: (x : s)
  结论: (↑(-x) : R) = -↑x
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_neg (x : s) : (↑(-x) : R) = -↑x :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : s)
  statement: (↑(x * y) : R) = ↑x * ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (x y : s)
  结论: (↑(x * y) : R) = ↑x * ↑y
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : s) : R) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ((0 : s) : R) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ((0 : s) : R) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : s) : R) = 1
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_one
  结论: ((1 : s) : R) = 1
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_one : ((1 : s) : R) = 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: {R} [Ring R] (s : Subring R) (x : s) (n : Nat)
  statement: ↑(x ^ n) = (x : R) ^ n
  proof: SubmonoidClass.coe_pow x n

中文:
定理 coe_pow
  条件: {R} [环 R] (s : 子环 R) (x : s) (n : 自然数)
  结论: ↑(x ^ n) = (x : R) ^ n
  证明: SubmonoidClass.coe_pow x n

Depends on / 依赖: SubmonoidClass, SubmonoidClass.coe_pow, coe_pow
-/
theorem coe_pow {R} [Ring R] (s : Subring R) (x : s) (n : Nat) : ↑(x ^ n) = (x : R) ^ n :=
  SubmonoidClass.coe_pow x n

/--
theorem `coe_eq_zero_iff` / 定理 `coe_eq_zero_iff`

English:
theorem coe_eq_zero_iff
  given: {x : s}
  statement: (x : R) = 0 ↔ x = 0
  proof: ⟨fun h => Subtype.ext (Trans.trans h s.coe_zero.symm), fun h => h.symm ▸ s.coe_zero⟩

中文:
定理 coe_eq_zero_iff
  条件: {x : s}
  结论: (x : R) = 0 ↔ x = 0
  证明: ⟨fun h => Subtype.ext (Trans.trans h s.coe_zero.symm), fun h => h.symm ▸ s.coe_zero⟩

Depends on / 依赖: Subtype, Subtype.ext, Trans.trans, coe_zero, h.symm, s.coe_zero, s.coe_zero.symm
-/
theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 :=
  ⟨fun h => Subtype.ext (Trans.trans h s.coe_zero.symm), fun h => h.symm ▸ s.coe_zero⟩

/--
lemma `mk_eq_zero` / 引理 `mk_eq_zero`

English:
lemma mk_eq_zero
  given: {x : R} (hx : x in s)
  statement: (⟨x, hx⟩ : s) = 0 ↔ x = 0
  proof: Subtype.ext_iff

中文:
引理 mk_eq_zero
  条件: {x : R} (hx : x in s)
  结论: (⟨x, hx⟩ : s) = 0 ↔ x = 0
  证明: Subtype.ext_iff
-/
@[simp] lemma mk_eq_zero {x : R} (hx : x in s) : (⟨x, hx⟩ : s) = 0 ↔ x = 0 := Subtype.ext_iff

/--
Instance `toCommRing` / 实例 `toCommRing`

English:
instance toCommRing
  signature: {R} [CommRing R] (s : Subring R)
  body: SubringClass.toCommRing s

中文:
实例 toCommRing
  签名: {R} [交换环 R] (s : 子环 R)
  定义体: SubringClass.toCommRing s

Depends on / 依赖: SubringClass, SubringClass.toCommRing, toCommRing
-/
instance toCommRing {R} [CommRing R] (s : Subring R) : CommRing s :=
  SubringClass.toCommRing s

/-- A subring of a non-trivial ring is non-trivial. -/
instance {R} [NonAssocRing R] [Nontrivial R] (s : Subring R) : Nontrivial s :=
  s.toSubsemiring.nontrivial

/-- A subring of a ring with no zero divisors has no zero divisors. -/
instance {R} [NonAssocRing R] [NoZeroDivisors R] (s : Subring R) : NoZeroDivisors s :=
  s.toSubsemiring.noZeroDivisors

/-- A subring of a domain is a domain. -/
instance {R} [Ring R] [IsDomain R] (s : Subring R) : IsDomain s :=
  NoZeroDivisors.to_isDomain _

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (s : Subring R)
  body: { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]

中文:
定义 subtype
  签名: (s : 子环 R)
  定义体: { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]

Depends on / 依赖: s.toAddSubgroup.subtype, s.toSubmonoid.subtype, subtype, toAddSubgroup, toSubmonoid
-/
def subtype (s : Subring R) : s ->+* R :=
  { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: {s : Subring R} (x : s)
  proof: rfl

中文:
引理 subtype_apply
  条件: {s : 子环 R} (x : s)
  证明: rfl

Depends on / 依赖: CommRingCat, MorphismProperty, MorphismProperty.injective, X.exists_germ_injective, appIso, cancel_left_of_respectsIso, cancel_right_of_respectsIso, exists_germ_injective, f.appIso, f.stalkMap, hU.image_of_isOpenImmersion, image_of_isOpenImmersion, injective, stalkMap
-/
lemma subtype_apply {s : Subring R} (x : s) :
    s.subtype x = x := rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  given: (s : Subring R)
  proof: s.toSubmonoid.subtype_injective

@[simp]

中文:
引理 subtype_injective
  条件: (s : 子环 R)
  证明: s.toSubmonoid.subtype_injective

@[simp]

Depends on / 依赖: s.toSubmonoid.subtype_injective, subtype_injective, toSubmonoid
-/
lemma subtype_injective (s : Subring R) :
    Function.Injective s.subtype :=
  s.toSubmonoid.subtype_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: ⇑s.subtype = ((↑) : s -> R)
  proof: rfl

@[norm_cast]

中文:
定理 coe_subtype
  结论: ⇑s.subtype = ((↑) : s -> R)
  证明: rfl

@[norm_cast]
-/
theorem coe_subtype : ⇑s.subtype = ((↑) : s -> R) :=
  rfl

@[norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: ((n : s) : R) = n
  proof: rfl

@[norm_cast]

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: ((n : s) : R) = n
  证明: rfl

@[norm_cast]
-/
theorem coe_natCast (n : Nat) : ((n : s) : R) = n := rfl

@[norm_cast]
/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: (n : Int)
  statement: ((n : s) : R) = n
  proof: rfl

中文:
定理 coe_intCast
  条件: (n : 整数)
  结论: ((n : s) : R) = n
  证明: rfl
-/
theorem coe_intCast (n : Int) : ((n : s) : R) = n := rfl

/-! ## Partial order -/

@[simp]
/--
theorem `coe_toSubsemiring` / 定理 `coe_toSubsemiring`

English:
theorem coe_toSubsemiring
  given: (s : Subring R)
  statement: (s.toSubsemiring : Set R) = s
  proof: rfl

中文:
定理 coe_toSubsemiring
  条件: (s : 子环 R)
  结论: (s.toSubsemiring : 集合 R) = s
  证明: rfl

Depends on / 依赖: Ideal.primeCompl_le_nonZeroDivisors, IsGermInjective, IsIntegral, IsLocalization, IsLocalization.injective, Nonempty, X.IsGermInjective, X.affineCover.covers, X.affineCover.f, affineCover, covers, injective, isAffineOpen_opensRange, isLocalization_stalk, opensRange, primeCompl_le_nonZeroDivisors
-/
theorem coe_toSubsemiring (s : Subring R) : (s.toSubsemiring : Set R) = s :=
  rfl

/--
theorem `mem_toSubmonoid` / 定理 `mem_toSubmonoid`

English:
theorem mem_toSubmonoid
  given: {s : Subring R} {x : R}
  statement: x in s.toSubmonoid ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toSubmonoid
  条件: {s : 子环 R} {x : R}
  结论: x in s.toSubmonoid ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: AtPrime, CommRingCat, Iff.rfl, IsGermInjective, IsLocallyNoetherian, IsNoetherianRing, Localization, Localization.AtPrime, RingHom, RingHom.ker, Scheme, Scheme.IsGermInjective.Spec, Scheme.IsGermInjective.of_openCover, X.IsGermInjective, X.affineOpenCover.f, X.affineOpenCover.openCover, affineOpenCover, algebraMap, isLocallyNoetherian_Spec, isLocallyNoetherian_Spec.mp
-/
theorem mem_toSubmonoid {s : Subring R} {x : R} : x in s.toSubmonoid ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `coe_toSubmonoid` / 定理 `coe_toSubmonoid`

English:
theorem coe_toSubmonoid
  given: (s : Subring R)
  statement: (s.toSubmonoid : Set R) = s
  proof: rfl

中文:
定理 coe_toSubmonoid
  条件: (s : 子环 R)
  结论: (s.toSubmonoid : 集合 R) = s
  证明: rfl
-/
theorem coe_toSubmonoid (s : Subring R) : (s.toSubmonoid : Set R) = s :=
  rfl

/--
theorem `mem_toAddSubgroup` / 定理 `mem_toAddSubgroup`

English:
theorem mem_toAddSubgroup
  given: {s : Subring R} {x : R}
  statement: x in s.toAddSubgroup ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toAddSubgroup
  条件: {s : 子环 R} {x : R}
  结论: x in s.toAddSubgroup ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toAddSubgroup {s : Subring R} {x : R} : x in s.toAddSubgroup ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `coe_toAddSubgroup` / 定理 `coe_toAddSubgroup`

English:
theorem coe_toAddSubgroup
  given: (s : Subring R)
  statement: (s.toAddSubgroup : Set R) = s
  proof: rfl

中文:
定理 coe_toAddSubgroup
  条件: (s : 子环 R)
  结论: (s.toAddSubgroup : 集合 R) = s
  证明: rfl
-/
theorem coe_toAddSubgroup (s : Subring R) : (s.toAddSubgroup : Set R) = s :=
  rfl

end Subring

/--
Definition of `NonUnitalSubring.toSubring` / `NonUnitalSubring.toSubring` 的定义

English:
definition NonUnitalSubring.toSubring
  signature: (S : NonUnitalSubring R) (h1 : (1 : R) in S)
  body: S
  one_mem' := h1

中文:
定义 NonUnital子环.toSubring
  签名: (S : NonUnital子环 R) (h1 : (1 : R) in S)
  定义体: S
  one_mem' := h1
-/
def NonUnitalSubring.toSubring (S : NonUnitalSubring R) (h1 : (1 : R) in S) : Subring R where
  __ := S
  one_mem' := h1

/--
lemma `Subring.toNonUnitalSubring_toSubring` / 引理 `Subring.toNonUnitalSubring_toSubring`

English:
lemma Subring.toNonUnitalSubring_toSubring
  given: (S : Subring R)
  proof: by cases S; rfl

中文:
引理 子环.toNonUnitalSubring_toSubring
  条件: (S : 子环 R)
  证明: by cases S; rfl
-/
lemma Subring.toNonUnitalSubring_toSubring (S : Subring R) :
    S.toNonUnitalSubring.toSubring S.one_mem = S := by cases S; rfl

/--
lemma `NonUnitalSubring.toSubring_toNonUnitalSubring` / 引理 `NonUnitalSubring.toSubring_toNonUnitalSubring`

English:
lemma NonUnitalSubring.toSubring_toNonUnitalSubring
  given: (S : NonUnitalSubring R) (h1 : (1 : R) in S)
  proof: by cases S; rfl

中文:
引理 NonUnital子环.toSubring_toNonUnitalSubring
  条件: (S : NonUnital子环 R) (h1 : (1 : R) in S)
  证明: by cases S; rfl
-/
lemma NonUnitalSubring.toSubring_toNonUnitalSubring (S : NonUnitalSubring R) (h1 : (1 : R) in S) :
    (NonUnitalSubring.toSubring S h1).toNonUnitalSubring = S := by cases S; rfl
