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

/-- `SubringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup. -/
/-
**SubringClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_1) → (R : outParam (Type u)) → [NonAssocRing R] → [SetLike S R
] → Prop
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SubringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup.
-/
class SubringClass (S : Type*) (R : outParam (Type u)) [NonAssocRing R] [SetLike S R] : Prop
    extends SubsemiringClass S R, NegMemClass S R

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SubringClass.addSubgroupClass (S : Type*) (R : Type u)
    [SetLike S R] [NonAssocRing R] [h : SubringClass S R] : AddSubgroupClass S R :=
  { h with }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SubringClass.nonUnitalSubringClass (S : Type*) (R : Type u)
    [SetLike S R] [NonAssocRing R] [SubringClass S R] : NonUnitalSubringClass S R where

variable [SetLike S R] [hSR : SubringClass S R] (s : S)

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**intCast_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intCast_mem (n : Int) : (n : R) in s
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
-/
theorem intCast_mem (n : ℤ) : (n : R) ∈ s := by simp only [← zsmul_one, zsmul_mem, one_mem]

namespace SubringClass

/-
**SubringClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) toHasIntCast : IntCast s :=
  ⟨fun n => ⟨n, intCast_mem s n⟩⟩

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a non-unital ring inherits a non-unital ring structure -/
/-
**SubringClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring of a non-unital ring inherits a non-unital ring structure
-/
instance (priority := 75) toNonAssocRing (s : S) : NonAssocRing s := fast_instance%
  Subtype.coe_injective.nonAssocRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a ring inherits a ring structure -/
/-
**SubringClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring of a ring inherits a ring structure
-/
instance (priority := 75) toRing {R} [Ring R] [SetLike S R] [SubringClass S R] :
    Ring s := fast_instance%
  Subtype.coe_injective.ring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a `NonAssocCommRing` is a `NonAssocCommRing`. -/
/-
**SubringClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring of a `NonAssocCommRing` is a `NonAssocCommRing`.
-/
instance (priority := 75) toNonAssocCommRing {R} [NonAssocCommRing R] [SetLike S R]
    [SubringClass S R] : NonAssocCommRing s := fast_instance%
  Subtype.coe_injective.nonAssocCommRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a `CommRing` is a `CommRing`. -/
/-
**SubringClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring of a `CommRing` is a `CommRing`.
-/
instance (priority := 75) toCommRing {R} [CommRing R] [SetLike S R] [SubringClass S R] :
    CommRing s := fast_instance%
  Subtype.coe_injective.commRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a domain is a domain. -/
/-
**SubringClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring of a domain is a domain.
-/
instance (priority := 75) {R} [Ring R] [IsDomain R] [SetLike S R] [SubringClass S R] : IsDomain s :=
  NoZeroDivisors.to_isDomain _

/-- The natural ring hom from a subring of ring `R` to `R`. -/
/-
**SubringClass.subtype** 是 Mathlib 中的一个定义，位于命名空间 `SubringClass`。
形式化陈述：subtype (s : S) : s ->+* R
参数：s : S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R

--- 原说明 ---
The natural ring hom from a subring of ring `R` to `R`.
-/
def subtype (s : S) : s →+* R :=
  { SubmonoidClass.subtype s, AddSubgroupClass.subtype s with
    toFun := (↑) }

variable {s} in
@[simp]
/-
**SubringClass.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `SubringClass`。
形式化陈述：subtype_apply (x : s) : SubringClass.subtype s x = x
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply (x : s) :
    SubringClass.subtype s x = x := rfl
/-
**SubringClass.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `SubringClass`。
形式化陈述：subtype_injective : Function.Injective (subtype s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective :
    Function.Injective (subtype s) :=
  Subtype.coe_injective

@[simp]
/-
**SubringClass.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `SubringClass`。
形式化陈述：coe_subtype : (subtype s : s -> R) = ((↑) : s -> R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : (subtype s : s → R) = ((↑) : s → R) :=
  rfl

@[simp, norm_cast]
/-
**SubringClass.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `SubringClass`。
形式化陈述：coe_natCast (n : Nat) : ((n : s) : R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natCast (n : ℕ) : ((n : s) : R) = n := rfl

@[simp, norm_cast]
/-
**SubringClass.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `SubringClass`。
形式化陈述：coe_intCast (n : Int) : ((n : s) : R) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_intCast (n : ℤ) : ((n : s) : R) = n := rfl

end SubringClass

end SubringClass

/-- `Subring R` is the type of subrings of `R`. A subring of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
@[wikidata Q929536]
/-
**Subring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [NonAssocRing R] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subring R` is the type of subrings of `R`. A subring of `R` is a subset `s` tha
t is a
  multiplicative submonoid and an additive subgroup. Note in particular that it 
shares the
  same 0 and 1 as R.
-/
structure Subring (R : Type u) [NonAssocRing R] extends Subsemiring R, AddSubgroup R

/-- Reinterpret a `Subring` as a `Subsemiring`. -/
add_decl_doc Subring.toSubsemiring

/-- Reinterpret a `Subring` as an `AddSubgroup`. -/
add_decl_doc Subring.toAddSubgroup

namespace Subring

/-
**Subring.toSubsemiring_injective** 是 Mathlib 中的一个引理，位于命名空间 `Subring`。
形式化陈述：toSubsemiring_injective : (toSubsemiring : Subring R -> Subsemiring R).Inj
ective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subring.neg_mem'`：∀ {R : Type u} [inst : NonAssocRing R] (self : Subring
 R) {x : R}, x ∈ self.carrier → -x ∈ self.carrier
-/
lemma toSubsemiring_injective : (toSubsemiring : Subring R → Subsemiring R).Injective :=
  fun ⟨s, hs⟩ t ↦ by congr!
/-
**Subring.toSubsemiring_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] {s t : Subring R}, s.toSubsemiring 
= t.toSubsemiring ↔ s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Subring.toSubsemiring_injective`：toSubsemiring_injective : (toSubsemirin
g : Subring R -> Subsemiring R).Injective
-/
@[simp] lemma toSubsemiring_inj {s t : Subring R} : s.toSubsemiring = t.toSubsemiring ↔ s = t :=
  toSubsemiring_injective.eq_iff
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Subring R) R where
  coe s := s.carrier
  coe_injective := SetLike.coe_injective.comp toSubsemiring_injective
/-
**Subring.toAddSubgroup_injective** 是 Mathlib 中的一个引理，位于命名空间 `Subring`。
形式化陈述：toAddSubgroup_injective : (toAddSubgroup : Subring R -> AddSubgroup R).Inj
ective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
lemma toAddSubgroup_injective : (toAddSubgroup : Subring R → AddSubgroup R).Injective :=
  fun _ _ h ↦ SetLike.ext (SetLike.ext_iff.mp h :)
/-
**Subring.toSubmonoid_injective** 是 Mathlib 中的一个引理，位于命名空间 `Subring`。
形式化陈述：toSubmonoid_injective : (fun s : Subring R => s.toSubmonoid).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
lemma toSubmonoid_injective : (fun s : Subring R => s.toSubmonoid).Injective :=
  fun _ _ h ↦ SetLike.ext (SetLike.ext_iff.mp h :)
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Subring R) := .ofSetLike (Subring R) R

initialize_simps_projections Subring (carrier → coe, as_prefix coe)

/-- The actual `Subring` obtained from an element of a `SubringClass`. -/
@[simps]
/-
**Subring.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：ofClass {S R : Type*} [NonAssocRing R] [SetLike S R] [SubringClass S R] (s
 : S) : Subring R where carrier
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The actual `Subring` obtained from an element of a `SubringClass`.
-/
def ofClass {S R : Type*} [NonAssocRing R] [SetLike S R] [SubringClass S R]
    (s : S) : Subring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  neg_mem' := neg_mem
  one_mem' := one_mem _
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set R) (Subring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ 1 ∈ s ∧
      (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧ ∀ {x}, x ∈ s → -x ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        one_mem' := h.2.2.1
        mul_mem' := h.2.2.2.1
        neg_mem' := h.2.2.2.2 },
      rfl ⟩
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubringClass (Subring R) R where
  zero_mem s := s.zero_mem'
  add_mem {s} := s.add_mem'
  one_mem s := s.one_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'

/-- Turn a `Subring` into a `NonUnitalSubring` by forgetting that it contains `1`. -/
@[reducible]
/-
**Subring.toNonUnitalSubring** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：toNonUnitalSubring (S : Subring R) : NonUnitalSubring R where __
参数：S : Subring R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.neg_mem'`：∀ {R : Type u} [inst : NonAssocRing R] (self : Subring
 R) {x : R}, x ∈ self.carrier → -x ∈ self.carrier

--- 原说明 ---
Turn a `Subring` into a `NonUnitalSubring` by forgetting that it contains `1`.
-/
def toNonUnitalSubring (S : Subring R) : NonUnitalSubring R where __ := S

@[simp]
/-
**Subring.mem_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_toSubsemiring {s : Subring R} {x : R} : x in s.toSubsemiring ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubsemiring {s : Subring R} {x : R} : x ∈ s.toSubsemiring ↔ x ∈ s := Iff.rfl
/-
**Subring.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_carrier {s : Subring R} {x : R} : x in s.carrier ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : Subring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**Subring.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_mk {S : Subsemiring R} {x : R} (h) : x in (⟨S, h⟩ : Subring R) ↔ x in 
S
参数：h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {S : Subsemiring R} {x : R} (h) : x ∈ (⟨S, h⟩ : Subring R) ↔ x ∈ S := Iff.rfl
/-
**Subring.coe_set_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] (S : Subsemiring R) (h : ∀ {x : R},
 x ∈ S.carrier → -x ∈ S.carrier),   ↑{ toSubsemiring := S, neg_mem' := h } = ↑S
参数：S : Subsemiring R；h : ∀ {x : R}, x ∈ S.carrier → -x ∈ S.carrier。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_set_mk (S : Subsemiring R) (h) : ((⟨S, h⟩ : Subring R) : Set R) = S := rfl

@[simp]
/-
**Subring.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mk_le_mk {S S' : Subsemiring R} (h₁ h₂) : (⟨S, h₁⟩ : Subring R) <= (⟨S', h
₂⟩ : Subring R) ↔ S <= S'
参数：h₁ h₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk {S S' : Subsemiring R} (h₁ h₂) :
    (⟨S, h₁⟩ : Subring R) ≤ (⟨S', h₂⟩ : Subring R) ↔ S ≤ S' :=
  Iff.rfl
/-
**Subring.one_mem_toNonUnitalSubring** 是 Mathlib 中的一个引理，位于命名空间 `Subring`。
形式化陈述：one_mem_toNonUnitalSubring (S : Subring R) : 1 in S.toNonUnitalSubring
参数：S : Subring R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.one_mem`：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Sub
semiring R), 1 ∈ s
-/
lemma one_mem_toNonUnitalSubring (S : Subring R) : 1 ∈ S.toNonUnitalSubring := S.one_mem

/-- Two subrings are equal if they have the same elements. -/
@[ext]
/-
**Subring.ext** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：ext {S T : Subring R} (h : forall x, x in S ↔ x in T) : S = T
参数：h : forall x, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two subrings are equal if they have the same elements.
-/
theorem ext {S T : Subring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subring with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps coe toSubsemiring]
/-
**Subring.copy** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：{R : Type u} → [inst : NonAssocRing R] → (S : Subring R) → (s : Set R) → s
 = ↑S → Subring R
参数：S : Subring R；s : Set R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a subring with a new `carrier` equal to the old one. Useful to fix defin
itional
equalities.
-/
protected def copy (S : Subring R) (s : Set R) (hs : s = ↑S) : Subring R :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }
/-
**Subring.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：copy_eq (S : Subring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S
参数：S : Subring R；s : Set R；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : Subring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

/-- Construct a `Subring R` from a set `s`, a submonoid `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
@[simps! coe]
/-
**Subring.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSub
group R} (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toSubmonoid = sm
参数：hm : ↑sm = s；ha : ↑sa = s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `Subring R` from a set `s`, a submonoid `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`.
-/
protected def mk' (s : Set R) (sm : Submonoid R) (sa : AddSubgroup R) (hm : ↑sm = s)
    (ha : ↑sa = s) : Subring R :=
  { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]
/-
**Subring.mem_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
 (ha : ↑sa = s) {x : R} : x in Subring.mk' s sm sa hm ha ↔ x in s
参数：hm : ↑sm = s；ha : ↑sa = s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Subring.mk'`：mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = 
s) {sa : AddSubgroup R} (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toSubmonoid
 …
-/
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
    {x : R} : x ∈ Subring.mk' s sm sa hm ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**Subring.mk'_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] {s : Set R} {sm : Submonoid R} (hm 
: ↑sm = s) {sa : AddSubgroup R}   (ha : ↑sa = s), (Subring.mk' s sm sa hm ha).to
Submonoid = sm
参数：hm : ↑sm = s；ha : ↑sa = s；Subring.mk' s sm sa hm ha。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Subring.mk'`：mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = 
s) {sa : AddSubgroup R} (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toSubmonoid
 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm

@[simp]
/-
**Subring.mk'_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] {s : Set R} {sm : Submonoid R} (hm 
: ↑sm = s) {sa : AddSubgroup R}   (ha : ↑sa = s), (Subring.mk' s sm sa hm ha).to
AddSubgroup = sa
参数：hm : ↑sm = s；ha : ↑sa = s；Subring.mk' s sm sa hm ha。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Subring.mk'`：mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = 
s) {sa : AddSubgroup R} (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toSubmonoid
 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mk'_toAddSubgroup {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toAddSubgroup = sa :=
  SetLike.coe_injective ha.symm

end Subring

/-- A `Subsemiring` containing -1 is a `Subring`. -/
@[simps toSubsemiring]
/-
**Subsemiring.toSubring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subsemiring.toSubring (s : Subsemiring R) (hneg : (-1 : R) in s) : Subring
 R where toSubsemiring
参数：s : Subsemiring R；hneg : (-1 : R) in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Subsemiring` containing -1 is a `Subring`.
-/
def Subsemiring.toSubring (s : Subsemiring R) (hneg : (-1 : R) ∈ s) : Subring R where
  toSubsemiring := s
  neg_mem' h := by
    rw [← neg_one_mul]
    exact mul_mem hneg h

namespace Subring

variable (s : Subring R)

/-- A subring contains the ring's 1. -/
/-
**Subring.one_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R), 1 ∈ s
参数：s : Subring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
A subring contains the ring's 1.
-/
protected theorem one_mem : (1 : R) ∈ s :=
  one_mem _

/-- A subring contains the ring's 0. -/
/-
**Subring.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R), 0 ∈ s
参数：s : Subring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
A subring contains the ring's 0.
-/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem _

/-- A subring is closed under multiplication. -/
/-
**Subring.mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) {x y : R}, x ∈ s → 
y ∈ s → x * y ∈ s
参数：s : Subring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
A subring is closed under multiplication.
-/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A subring is closed under addition. -/
/-
**Subring.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) {x y : R}, x ∈ s → 
y ∈ s → x + y ∈ s
参数：s : Subring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
A subring is closed under addition.
-/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A subring is closed under negation. -/
/-
**Subring.neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) {x : R}, x ∈ s → -x
 ∈ s
参数：s : Subring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
A subring is closed under negation.
-/
protected theorem neg_mem {x : R} : x ∈ s → -x ∈ s :=
  neg_mem

/-- A subring is closed under subtraction -/
/-
**Subring.sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) {x y : R}, x ∈ s → 
y ∈ s → x - y ∈ s
参数：s : Subring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
A subring is closed under subtraction
-/
protected theorem sub_mem {x y : R} (hx : x ∈ s) (hy : y ∈ s) : x - y ∈ s :=
  sub_mem hx hy

/-- A subring of a ring inherits a ring structure -/
/-
**Subring.toRing** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
形式化陈述：toRing {R} [Ring R] (s : Subring R) : Ring s
参数：s : Subring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring of a ring inherits a ring structure
-/
instance toRing {R} [Ring R] (s : Subring R) : Ring s := SubringClass.toRing s
/-
**Subring.zsmul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) {x : R}, x ∈ s → ∀ 
(n : ℤ), n • x ∈ s
参数：s : Subring R；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zsmul_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst
_1 : SetLike S M] [hSM : AddSubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n …
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
protected theorem zsmul_mem {x : R} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n
/-
**Subring.pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] (s : Subring R) {x : R}, x ∈ s → ∀ (n : ℕ
), x ^ n ∈ s
参数：s : Subring R；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
protected theorem pow_mem {R : Type*} [Ring R] (s : Subring R) {x : R} (hx : x ∈ s) (n : ℕ) :
    x ^ n ∈ s := pow_mem hx n

@[simp, norm_cast]
/-
**Subring.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
/-
**Subring.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_neg (x : s) : (↑(-x) : R) = -↑x
参数：x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_neg (x : s) : (↑(-x) : R) = -↑x :=
  rfl

@[simp, norm_cast]
/-
**Subring.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
/-
**Subring.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_zero : ((0 : s) : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_zero : ((0 : s) : R) = 0 :=
  rfl

@[simp, norm_cast]
/-
**Subring.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_one : ((1 : s) : R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_one : ((1 : s) : R) = 1 :=
  rfl

@[simp, norm_cast]
/-
**Subring.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_pow {R} [Ring R] (s : Subring R) (x : s) (n : Nat) : ↑(x ^ n) = (x : R
) ^ n
参数：s : Subring R；x : s；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.coe_pow`：coe_pow {M} [Monoid M] {A : Type*} [SetLike A M]
 [SubmonoidClass A M] {S : A} (x : S) (n : Nat) : ↑(x ^ n) = (x : M) ^ n
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_pow {R} [Ring R] (s : Subring R) (x : s) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n :=
  SubmonoidClass.coe_pow x n
/-
**Subring.coe_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subring.coe_zero`：coe_zero : ((0 : s) : R) = 0
-/
theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 :=
  ⟨fun h => Subtype.ext (Trans.trans h s.coe_zero.symm), fun h => h.symm ▸ s.coe_zero⟩
/-
**Subring.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) {x : R} (hx : x ∈ s
), ⟨x, hx⟩ = 0 ↔ x = 0
参数：s : Subring R；hx : x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
@[simp] lemma mk_eq_zero {x : R} (hx : x ∈ s) : (⟨x, hx⟩ : s) = 0 ↔ x = 0 := Subtype.ext_iff

/-- A subring of a `CommRing` is a `CommRing`. -/
/-
**Subring.toCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
形式化陈述：toCommRing {R} [CommRing R] (s : Subring R) : CommRing s
参数：s : Subring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring of a `CommRing` is a `CommRing`.
-/
instance toCommRing {R} [CommRing R] (s : Subring R) : CommRing s :=
  SubringClass.toCommRing s

/-- A subring of a non-trivial ring is non-trivial. -/
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring of a non-trivial ring is non-trivial.
-/
instance {R} [NonAssocRing R] [Nontrivial R] (s : Subring R) : Nontrivial s :=
  s.toSubsemiring.nontrivial

/-- A subring of a ring with no zero divisors has no zero divisors. -/
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring of a ring with no zero divisors has no zero divisors.
-/
instance {R} [NonAssocRing R] [NoZeroDivisors R] (s : Subring R) : NoZeroDivisors s :=
  s.toSubsemiring.noZeroDivisors

/-- A subring of a domain is a domain. -/
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subring of a domain is a domain.
-/
instance {R} [Ring R] [IsDomain R] (s : Subring R) : IsDomain s :=
  NoZeroDivisors.to_isDomain _

/-- The natural ring hom from a subring of ring `R` to `R`. -/
/-
**Subring.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：subtype (s : Subring R) : s ->+* R
参数：s : Subring R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
The natural ring hom from a subring of ring `R` to `R`.
-/
def subtype (s : Subring R) : s →+* R :=
  { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]
/-
**Subring.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `Subring`。
形式化陈述：subtype_apply {s : Subring R} (x : s) : s.subtype x = x
参数：x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
lemma subtype_apply {s : Subring R} (x : s) :
    s.subtype x = x := rfl
/-
**Subring.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `Subring`。
形式化陈述：subtype_injective (s : Subring R) : Function.Injective s.subtype
参数：s : Subring R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submonoid.subtype_injective`：subtype_injective (s : Submonoid M) : Funct
ion.Injective s.subtype
-/
lemma subtype_injective (s : Subring R) :
    Function.Injective s.subtype :=
  s.toSubmonoid.subtype_injective

@[simp]
/-
**Subring.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_subtype : ⇑s.subtype = ((↑) : s -> R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_subtype : ⇑s.subtype = ((↑) : s → R) :=
  rfl

@[norm_cast]
/-
**Subring.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_natCast (n : Nat) : ((n : s) : R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_natCast (n : ℕ) : ((n : s) : R) = n := rfl

@[norm_cast]
/-
**Subring.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_intCast (n : Int) : ((n : s) : R) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_intCast (n : ℤ) : ((n : s) : R) = n := rfl

/-! ## Partial order -/

@[simp]
/-
**Subring.coe_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_toSubsemiring (s : Subring R) : (s.toSubsemiring : Set R) = s
参数：s : Subring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## Partial order
-/
theorem coe_toSubsemiring (s : Subring R) : (s.toSubsemiring : Set R) = s :=
  rfl
/-
**Subring.mem_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_toSubmonoid {s : Subring R} {x : R} : x in s.toSubmonoid ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubmonoid {s : Subring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**Subring.coe_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_toSubmonoid (s : Subring R) : (s.toSubmonoid : Set R) = s
参数：s : Subring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubmonoid (s : Subring R) : (s.toSubmonoid : Set R) = s :=
  rfl
/-
**Subring.mem_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_toAddSubgroup {s : Subring R} {x : R} : x in s.toAddSubgroup ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toAddSubgroup {s : Subring R} {x : R} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**Subring.coe_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_toAddSubgroup (s : Subring R) : (s.toAddSubgroup : Set R) = s
参数：s : Subring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAddSubgroup (s : Subring R) : (s.toAddSubgroup : Set R) = s :=
  rfl

end Subring

/-- Turn a non-unital subring containing `1` into a subring. -/
/-
**NonUnitalSubring.toSubring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalSubring.toSubring (S : NonUnitalSubring R) (h1 : (1 : R) in S) : 
Subring R where __
参数：S : NonUnitalSubring R；h1 : (1 : R) in S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a non-unital subring containing `1` into a subring.
-/
def NonUnitalSubring.toSubring (S : NonUnitalSubring R) (h1 : (1 : R) ∈ S) : Subring R where
  __ := S
  one_mem' := h1
/-
**Subring.toNonUnitalSubring_toSubring** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subring.toNonUnitalSubring_toSubring (S : Subring R) : S.toNonUnitalSubrin
g.toSubring S.one_mem = S
参数：S : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.one_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R),
 1 ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Subring.toNonUnitalSubring_toSubring (S : Subring R) :
    S.toNonUnitalSubring.toSubring S.one_mem = S := by cases S; rfl
/-
**NonUnitalSubring.toSubring_toNonUnitalSubring** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NonUnitalSubring.toSubring_toNonUnitalSubring (S : NonUnitalSubring R) (h1
 : (1 : R) in S) : (NonUnitalSubring.toSubring S h1).toNonUnitalSubring = S
参数：S : NonUnitalSubring R；h1 : (1 : R) in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma NonUnitalSubring.toSubring_toNonUnitalSubring (S : NonUnitalSubring R) (h1 : (1 : R) ∈ S) :
    (NonUnitalSubring.toSubring S h1).toNonUnitalSubring = S := by cases S; rfl
