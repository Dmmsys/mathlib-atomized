/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Ring orderings

Let `R` be a commutative ring. A preordering on `R` is a subset closed under
addition and multiplication that contains all squares, but not `-1`.

The support of a preordering `P` is the set of elements `x` such that both `x` and `-x` lie in `P`.

An ordering `O` on `R` is a preordering such that
1. `O` contains either `x` or `-x` for each `x` in `R` and
2. the support of `O` is a prime ideal.

We define preorderings, supports and orderings.

A ring preordering can intuitively be viewed as a set of "non-negative" ring elements.
Indeed, an ordering `O` with support `p` induces a linear order on `R⧸p` making it
into an ordered ring, and vice versa.

## References

- [*An introduction to real algebra*, T.Y. Lam][lam_1984]

-/

@[expose] public section

/-!
#### Preorderings
-/

variable (R : Type*) [CommRing R]

/-- A preordering on a ring `R` is a subsemiring of `R` containing all squares,
but not containing `-1`. -/
@[ext]
/--
Definition of `RingPreordering` / `RingPreordering` 的定义

English:
structure RingPreordering
  parameters: extends Subsemiring R
  extends: Subsemiring R
  axioms and operations (2):
    - mem_of_isSquare'({x : R} (hx : IsSquare x)) : x in carrier  [default: by aesop]
    - neg_one_notMem' : -1 ∉ carrier  [default: by aesop]

中文:
结构 RingPreordering
  参数: extends 子半环 R
  继承: 子半环 R
  公理与运算 (2 个):
    - mem_of_isSquare'({x : R} (hx : IsSquare x)) : x in carrier  [默认: by aesop]
    - neg_one_notMem' : -1 ∉ carrier  [默认: by aesop]

Depends on / 依赖: carrier, neg_one_notMem
-/
structure RingPreordering extends Subsemiring R where
  mem_of_isSquare' {x : R} (hx : IsSquare x) : x in carrier := by aesop
  neg_one_notMem' : -1 ∉ carrier := by aesop

namespace RingPreordering

attribute [coe] toSubsemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (RingPreordering R) R
  body: P.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

中文:
实例 :
  签名: 集合状 (RingPreordering R) R
  定义体: P.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

Depends on / 依赖: P.carrier, carrier
-/
instance : SetLike (RingPreordering R) R where
  coe P := P.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (RingPreordering R)
  body: .ofSetLike (RingPreordering R) R

initialize_simps_projections RingPreordering (carrier -> coe, as_prefix coe)

中文:
实例 :
  签名: 偏序 (RingPreordering R)
  定义体: .ofSetLike (RingPreordering R) R

initialize_simps_projections RingPreordering (carrier -> coe, as_prefix coe)

Depends on / 依赖: RingPreordering, ofSetLike
-/
instance : PartialOrder (RingPreordering R) := .ofSetLike (RingPreordering R) R

initialize_simps_projections RingPreordering (carrier -> coe, as_prefix coe)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubsemiringClass (RingPreordering R) R
  body: Subsemiring.zero_mem _
  one_mem _ := Subsemiring.one_mem _
  add_mem := Subsemiring.add_mem _
  mul_mem := Subsemiring.mul_mem _

中文:
实例 :
  签名: 子半环类 (RingPreordering R) R
  定义体: Subsemiring.zero_mem _
  one_mem _ := Subsemiring.one_mem _
  add_mem := Subsemiring.add_mem _
  mul_mem := Subsemiring.mul_mem _

Depends on / 依赖: Subsemiring, Subsemiring.zero_mem, zero_mem
-/
instance : SubsemiringClass (RingPreordering R) R where
  zero_mem _ := Subsemiring.zero_mem _
  one_mem _ := Subsemiring.one_mem _
  add_mem := Subsemiring.add_mem _
  mul_mem := Subsemiring.mul_mem _

variable {R}

@[aesop unsafe 80% (rule_sets := [SetLike])]
/--
theorem `mem_of_isSquare` / 定理 `mem_of_isSquare`

English:
theorem mem_of_isSquare
  given: (P : RingPreordering R) {x : R} (hx : IsSquare x)
  statement: x in P
  proof: RingPreordering.mem_of_isSquare' _ hx

@[simp]

中文:
定理 mem_of_isSquare
  条件: (P : RingPreordering R) {x : R} (hx : IsSquare x)
  结论: x in P
  证明: RingPreordering.mem_of_isSquare' _ hx

@[simp]
-/
protected theorem mem_of_isSquare (P : RingPreordering R) {x : R} (hx : IsSquare x) : x in P :=
  RingPreordering.mem_of_isSquare' _ hx

@[simp]
/--
theorem `mul_self_mem` / 定理 `mul_self_mem`

English:
theorem mul_self_mem
  given: (P : RingPreordering R) (x : R)
  statement: x * x in P
  proof: by aesop

@[simp]

中文:
定理 mul_self_mem
  条件: (P : RingPreordering R) (x : R)
  结论: x * x in P
  证明: by aesop

@[simp]
-/
protected theorem mul_self_mem (P : RingPreordering R) (x : R) : x * x in P := by aesop

@[simp]
/--
theorem `pow_two_mem` / 定理 `pow_two_mem`

English:
theorem pow_two_mem
  given: (P : RingPreordering R) (x : R)
  statement: x ^ 2 in P
  proof: by aesop

@[aesop unsafe 20% forward (rule_sets := [SetLike])]

中文:
定理 pow_two_mem
  条件: (P : RingPreordering R) (x : R)
  结论: x ^ 2 in P
  证明: by aesop

@[aesop unsafe 20% forward (rule_sets := [SetLike])]
-/
protected theorem pow_two_mem (P : RingPreordering R) (x : R) : x ^ 2 in P := by aesop

@[aesop unsafe 20% forward (rule_sets := [SetLike])]
/--
theorem `neg_one_notMem` / 定理 `neg_one_notMem`

English:
theorem neg_one_notMem
  given: (P : RingPreordering R)
  statement: -1 ∉ P
  proof: RingPreordering.neg_one_notMem' _

中文:
定理 neg_one_notMem
  条件: (P : RingPreordering R)
  结论: -1 ∉ P
  证明: RingPreordering.neg_one_notMem' _
-/
protected theorem neg_one_notMem (P : RingPreordering R) : -1 ∉ P :=
  RingPreordering.neg_one_notMem' _

/--
theorem `toSubsemiring_injective` / 定理 `toSubsemiring_injective`

English:
theorem toSubsemiring_injective
  proof: fun A B h => by ext; rw [h]

@[simp]

中文:
定理 toSubsemiring_injective
  证明: fun A B h => by ext; rw [h]

@[simp]
-/
theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : RingPreordering R -> _) := fun A B h => by ext; rw [h]

@[simp]
/--
theorem `toSubsemiring_inj` / 定理 `toSubsemiring_inj`

English:
theorem toSubsemiring_inj
  given: {P₁ P₂ : RingPreordering R}
  proof: toSubsemiring_injective.eq_iff

@[simp]

中文:
定理 toSubsemiring_inj
  条件: {P₁ P₂ : RingPreordering R}
  证明: toSubsemiring_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toSubsemiring_injective, toSubsemiring_injective.eq_iff
-/
theorem toSubsemiring_inj {P₁ P₂ : RingPreordering R} :
    P₁.toSubsemiring = P₂.toSubsemiring ↔ P₁ = P₂ := toSubsemiring_injective.eq_iff

@[simp]
/--
theorem `mem_toSubsemiring` / 定理 `mem_toSubsemiring`

English:
theorem mem_toSubsemiring
  given: {P : RingPreordering R} {x : R}
  statement: x in P.toSubsemiring ↔ x in P
  proof: .rfl

@[simp, norm_cast]

中文:
定理 mem_toSubsemiring
  条件: {P : RingPreordering R} {x : R}
  结论: x in P.toSubsemiring ↔ x in P
  证明: .rfl

@[simp, norm_cast]
-/
theorem mem_toSubsemiring {P : RingPreordering R} {x : R} : x in P.toSubsemiring ↔ x in P := .rfl

@[simp, norm_cast]
/--
theorem `coe_toSubsemiring` / 定理 `coe_toSubsemiring`

English:
theorem coe_toSubsemiring
  given: (P : RingPreordering R)
  statement: (P.toSubsemiring : Set R) = P
  proof: rfl

@[simp]

中文:
定理 coe_toSubsemiring
  条件: (P : RingPreordering R)
  结论: (P.toSubsemiring : 集合 R) = P
  证明: rfl

@[simp]
-/
theorem coe_toSubsemiring (P : RingPreordering R) : (P.toSubsemiring : Set R) = P := rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {toSubsemiring : Subsemiring R} (mem_of_isSquare neg_one_notMem) {x : R}
  proof: .rfl

@[simp]

中文:
定理 mem_mk
  条件: {toSubsemiring : 子半环 R} (mem_of_isSquare neg_one_notMem) {x : R}
  证明: .rfl

@[simp]
-/
theorem mem_mk {toSubsemiring : Subsemiring R} (mem_of_isSquare neg_one_notMem) {x : R} :
    x in mk toSubsemiring mem_of_isSquare neg_one_notMem ↔ x in toSubsemiring := .rfl

@[simp]
/--
theorem `coe_set_mk` / 定理 `coe_set_mk`

English:
theorem coe_set_mk
  given: (toSubsemiring : Subsemiring R) (mem_of_isSquare neg_one_notMem)
  proof: rfl

中文:
定理 coe_set_mk
  条件: (toSubsemiring : 子半环 R) (mem_of_isSquare neg_one_notMem)
  证明: rfl
-/
theorem coe_set_mk (toSubsemiring : Subsemiring R) (mem_of_isSquare neg_one_notMem) :
    (mk toSubsemiring mem_of_isSquare neg_one_notMem : Set R) = toSubsemiring := rfl

section copy

variable (P : RingPreordering R) (S : Set R) (hS : S = P)

/-- Copy of a preordering with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: : RingPreordering R where
  body: S
  zero_mem' := by aesop
  add_mem' ha hb := by aesop
  one_mem' := by aesop
  mul_mem' ha hb := by aesop

中文:
定义 copy
  签名: : RingPreordering R where
  定义体: S
  zero_mem' := by aesop
  add_mem' ha hb := by aesop
  one_mem' := by aesop
  mul_mem' ha hb := by aesop
-/
protected def copy : RingPreordering R where
  carrier := S
  zero_mem' := by aesop
  add_mem' ha hb := by aesop
  one_mem' := by aesop
  mul_mem' ha hb := by aesop

attribute [norm_cast] coe_copy
/--
theorem `mem_copy` / 定理 `mem_copy`

English:
theorem mem_copy
  given: {x}
  statement: x in P.copy S hS ↔ x in S
  proof: .rfl

中文:
定理 mem_copy
  条件: {x}
  结论: x in P.copy S hS ↔ x in S
  证明: .rfl
-/
@[simp] theorem mem_copy {x} : x in P.copy S hS ↔ x in S := .rfl
/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  statement: P.copy S hS = S
  proof: rfl

中文:
定理 copy_eq
  结论: P.copy S hS = S
  证明: rfl
-/
theorem copy_eq : P.copy S hS = S := rfl

end copy

variable {P : RingPreordering R}

/-!
#### Support
-/

section supportAddSubgroup

variable (P) in
/--
Definition of `supportAddSubgroup` / `supportAddSubgroup` 的定义

English:
definition supportAddSubgroup
  signature: : AddSubgroup R where
  body: P inter -P
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop

中文:
定义 supportAddSubgroup
  签名: : 加法子群 R where
  定义体: P inter -P
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop
-/
def supportAddSubgroup : AddSubgroup R where
  carrier := P inter -P
  zero_mem' := by aesop
  add_mem' := by aesop
  neg_mem' := by aesop

/--
theorem `mem_supportAddSubgroup` / 定理 `mem_supportAddSubgroup`

English:
theorem mem_supportAddSubgroup
  given: {x}
  statement: x in P.supportAddSubgroup ↔ x in P ∧ -x in P
  proof: .rfl

中文:
定理 mem_supportAddSubgroup
  条件: {x}
  结论: x in P.supportAddSubgroup ↔ x in P ∧ -x in P
  证明: .rfl
-/
theorem mem_supportAddSubgroup {x} : x in P.supportAddSubgroup ↔ x in P ∧ -x in P := .rfl
/--
theorem `coe_supportAddSubgroup` / 定理 `coe_supportAddSubgroup`

English:
theorem coe_supportAddSubgroup
  statement: P.supportAddSubgroup = (P inter -P : Set R)
  proof: rfl

中文:
定理 coe_supportAddSubgroup
  结论: P.supportAddSubgroup = (P inter -P : 集合 R)
  证明: rfl
-/
theorem coe_supportAddSubgroup : P.supportAddSubgroup = (P inter -P : Set R) := rfl

end supportAddSubgroup

/--
Definition of `HasIdealSupport` / `HasIdealSupport` 的定义

English:
class HasIdealSupport
  parameters: (P : RingPreordering R)
  axioms and operations (1):
    - smul_mem_support((P) (x : R) {a : R} (ha : a in P.supportAddSubgroup)) : x * a in P.supportAddSubgroup

中文:
类 有IdealSupport
  参数: (P : RingPreordering R)
  公理与运算 (1 个):
    - smul_mem_support((P) (x : R) {a : R} (ha : a in P.supportAddSubgroup)) : x * a in P.supportAddSubgroup
-/
class HasIdealSupport (P : RingPreordering R) : Prop where
  smul_mem_support (P) (x : R) {a : R} (ha : a in P.supportAddSubgroup) :
    x * a in P.supportAddSubgroup

export HasIdealSupport (smul_mem_support)

/--
theorem `hasIdealSupport_iff` / 定理 `hasIdealSupport_iff`

English:
theorem hasIdealSupport_iff
  proof: by simpa [mem_supportAddSubgroup] using P.smul_mem_support
  mpr _ := ⟨by simpa [mem_supportAddSubgroup]⟩

中文:
定理 hasIdealSupport_iff
  证明: by simpa [mem_supportAddSubgroup] using P.smul_mem_support
  mpr _ := ⟨by simpa [mem_supportAddSubgroup]⟩

Depends on / 依赖: P.smul_mem_support, mem_supportAddSubgroup, smul_mem_support
-/
theorem hasIdealSupport_iff :
    P.HasIdealSupport ↔ forall x a : R, a in P -> -a in P -> x * a in P ∧ -(x * a) in P where
  mp _ := by simpa [mem_supportAddSubgroup] using P.smul_mem_support
  mpr _ := ⟨by simpa [mem_supportAddSubgroup]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasMemOrNegMem
  signature: P] : P.HasIdealSupport where
  body: match mem_or_neg_mem P x with
    | .inl hx => ⟨by simpa using mul_mem hx ha.1, by simpa using mul_mem hx ha.2⟩
    | .inr hx => ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

中文:
实例 [有MemOrNegMem
  签名: P] : P.有IdealSupport where
  定义体: match mem_or_neg_mem P x with
    | .inl hx => ⟨by simpa using mul_mem hx ha.1, by simpa using mul_mem hx ha.2⟩
    | .inr hx => ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

Depends on / 依赖: mem_or_neg_mem, mul_mem
-/
instance [HasMemOrNegMem P] : P.HasIdealSupport where
  smul_mem_support x a ha :=
    match mem_or_neg_mem P x with
    | .inl hx => ⟨by simpa using mul_mem hx ha.1, by simpa using mul_mem hx ha.2⟩
    | .inr hx => ⟨by simpa using mul_mem hx ha.2, by simpa using mul_mem hx ha.1⟩

section support

variable [P.HasIdealSupport]

variable (P) in
/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: : Ideal R where
  body: P.supportAddSubgroup
  smul_mem' := by simpa using smul_mem_support P

中文:
定义 support
  签名: : 理想 R where
  定义体: P.supportAddSubgroup
  smul_mem' := by simpa using smul_mem_support P

Depends on / 依赖: P.supportAddSubgroup, supportAddSubgroup
-/
def support : Ideal R where
  __ := P.supportAddSubgroup
  smul_mem' := by simpa using smul_mem_support P

/--
theorem `mem_support` / 定理 `mem_support`

English:
theorem mem_support
  given: {x}
  statement: x in P.support ↔ x in P ∧ -x in P
  proof: .rfl

中文:
定理 mem_support
  条件: {x}
  结论: x in P.support ↔ x in P ∧ -x in P
  证明: .rfl
-/
theorem mem_support {x} : x in P.support ↔ x in P ∧ -x in P := .rfl
/--
theorem `coe_support` / 定理 `coe_support`

English:
theorem coe_support
  statement: P.support = (P : Set R) inter -(P : Set R)
  proof: rfl

中文:
定理 coe_support
  结论: P.support = (P : 集合 R) inter -(P : 集合 R)
  证明: rfl
-/
theorem coe_support : P.support = (P : Set R) inter -(P : Set R) := rfl

/--
theorem `supportAddSubgroup_eq` / 定理 `supportAddSubgroup_eq`

English:
theorem supportAddSubgroup_eq
  statement: P.supportAddSubgroup = P.support.toAddSubgroup
  proof: rfl

中文:
定理 supportAddSubgroup_eq
  结论: P.supportAddSubgroup = P.support.toAddSubgroup
  证明: rfl
-/
@[simp] theorem supportAddSubgroup_eq : P.supportAddSubgroup = P.support.toAddSubgroup := rfl

end support

/--
Definition of `IsOrdering` / `IsOrdering` 的定义

English:
class IsOrdering
  parameters: (P : RingPreordering R)
  extends: HasMemOrNegMem P, P.support.IsPrime
  (no additional axioms)

中文:
类 是Ordering
  参数: (P : RingPreordering R)
  继承: 有MemOrNegMem P, P.support.是素
  (无附加公理)
-/
class IsOrdering (P : RingPreordering R) extends HasMemOrNegMem P, P.support.IsPrime

end RingPreordering
