/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.RingTheory.NonUnitalSubsemiring.Defs

/-!
# Bundled subsemirings

We define bundled subsemirings and some standard constructions: `subtype` and `inclusion`
ring homomorphisms.
-/

@[expose] public section

assert_not_exists RelIso

universe u v w

section AddSubmonoidWithOneClass

/--
Definition of `AddSubmonoidWithOneClass` / `AddSubmonoidWithOneClass` 的定义

English:
class AddSubmonoidWithOneClass
  parameters: (S : Type*) (R : outParam Type*) [AddMonoidWithOne R]
  extends: AddSubmonoidClass S R, OneMemClass S R
  (no additional axioms)

中文:
类 AddSubmonoidWithOneClass
  参数: (S : 类型) (R : outParam 类型) [AddMonoidWithOne R]
  继承: AddSubmonoidClass S R, OneMemClass S R
  (无附加公理)
-/
class AddSubmonoidWithOneClass (S : Type*) (R : outParam Type*) [AddMonoidWithOne R]
  [SetLike S R] : Prop extends AddSubmonoidClass S R, OneMemClass S R

variable {S R : Type*} [AddMonoidWithOne R] [SetLike S R] (s : S)

@[simp, aesop safe (rule_sets := [SetLike])]
/--
theorem `natCast_mem` / 定理 `natCast_mem`

English:
theorem natCast_mem
  given: [AddSubmonoidWithOneClass S R] (n : Nat)
  statement: (n : R) in s
  proof: by
  induction n <;> simp [zero_mem, add_mem, one_mem, *]

@[simp, aesop safe (rule_sets := [SetLike])]

中文:
定理 natCast_mem
  条件: [AddSubmonoidWithOneClass S R] (n : 自然数)
  结论: (n : R) in s
  证明: by
  induction n <;> simp [zero_mem, add_mem, one_mem, *]

@[simp, aesop safe (rule_sets := [SetLike])]

Depends on / 依赖: add_mem, one_mem, zero_mem
-/
theorem natCast_mem [AddSubmonoidWithOneClass S R] (n : Nat) : (n : R) in s := by
  induction n <;> simp [zero_mem, add_mem, one_mem, *]

@[simp, aesop safe (rule_sets := [SetLike])]
/--
lemma `ofNat_mem` / 引理 `ofNat_mem`

English:
lemma ofNat_mem
  given: [AddSubmonoidWithOneClass S R] (s : S) (n : Nat) [n.AtLeastTwo]
  proof: by
  rw [← Nat.cast_ofNat]; exact natCast_mem s n

中文:
引理 ofNat_mem
  条件: [AddSubmonoidWithOneClass S R] (s : S) (n : 自然数) [n.AtLeastTwo]
  证明: by
  rw [← Nat.cast_ofNat]; exact natCast_mem s n

Depends on / 依赖: Nat.cast_ofNat, cast_ofNat, natCast_mem
-/
lemma ofNat_mem [AddSubmonoidWithOneClass S R] (s : S) (n : Nat) [n.AtLeastTwo] :
    ofNat(n) in s := by
  rw [← Nat.cast_ofNat]; exact natCast_mem s n

instance (priority := 74) AddSubmonoidWithOneClass.toAddMonoidWithOne
    [AddSubmonoidWithOneClass S R] : AddMonoidWithOne s :=
  { AddSubmonoidClass.toAddMonoid s with
    one := ⟨_, one_mem s⟩
    natCast := fun n => ⟨n, natCast_mem s n⟩
    natCast_zero := Subtype.ext Nat.cast_zero
    natCast_succ := fun _ => Subtype.ext (Nat.cast_succ _) }

end AddSubmonoidWithOneClass

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

section SubsemiringClass

/--
Definition of `SubsemiringClass` / `SubsemiringClass` 的定义

English:
class SubsemiringClass
  parameters: (S : Type*) (R : outParam (Type u)) [NonAssocSemiring R]
  extends: SubmonoidClass S R, AddSubmonoidClass S R
  (no additional axioms)

中文:
类 SubsemiringClass
  参数: (S : 类型) (R : outParam (类型u)) [NonAssocSemiring R]
  继承: SubmonoidClass S R, AddSubmonoidClass S R
  (无附加公理)
-/
class SubsemiringClass (S : Type*) (R : outParam (Type u)) [NonAssocSemiring R]
  [SetLike S R] : Prop extends SubmonoidClass S R, AddSubmonoidClass S R

-- See note [lower instance priority]
instance (priority := 100) SubsemiringClass.addSubmonoidWithOneClass (S : Type*)
    (R : Type u) {_ : NonAssocSemiring R} [SetLike S R] [h : SubsemiringClass S R] :
    AddSubmonoidWithOneClass S R :=
  { h with }

instance (priority := 100) SubsemiringClass.nonUnitalSubsemiringClass (S : Type*)
    (R : Type u) [NonAssocSemiring R] [SetLike S R] [SubsemiringClass S R] :
    NonUnitalSubsemiringClass S R where
  mul_mem := mul_mem

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

namespace SubsemiringClass

-- Prefer subclasses of `NonAssocSemiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure -/
instance (priority := 75) toNonAssocSemiring : NonAssocSemiring s := fast_instance%
  Subtype.coe_injective.nonAssocSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

/-- A subsemiring of a `NonAssocCommSemiring` inherits a `NonAssocCommSemiring` structure -/
instance (priority := 75) toNonAssocCommSemiring {R} [NonAssocCommSemiring R] [SetLike S R]
    [SubsemiringClass S R] : NonAssocCommSemiring s := fast_instance%
  Subtype.coe_injective.nonAssocCommSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: [Nontrivial R]
  body: nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)

中文:
实例 nontrivial
  签名: [Nontrivial R]
  定义体: nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)

Depends on / 依赖: Subtype, Subtype.val, congr_arg, nontrivial_of_ne, zero_ne_one
-/
instance nontrivial [Nontrivial R] : Nontrivial s :=
  nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)

/--
Instance `noZeroDivisors` / 实例 `noZeroDivisors`

English:
instance noZeroDivisors
  signature: [NoZeroDivisors R]
  body: Subtype.coe_injective.noZeroDivisors _ rfl fun _ _ => rfl

中文:
实例 noZeroDivisors
  签名: [NoZeroDivisors R]
  定义体: Subtype.coe_injective.noZeroDivisors _ rfl fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.coe_injective.noZeroDivisors, coe_injective, noZeroDivisors
-/
instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s :=
  Subtype.coe_injective.noZeroDivisors _ rfl fun _ _ => rfl

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : s ->+* R
  body: { SubmonoidClass.subtype s, AddSubmonoidClass.subtype s with toFun := (↑) }

@[simp]

中文:
定义 subtype
  签名: : s ->+* R
  定义体: { SubmonoidClass.subtype s, AddSubmonoidClass.subtype s with toFun := (↑) }

@[simp]

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.subtype, SubmonoidClass, SubmonoidClass.subtype, subtype
-/
def subtype : s ->+* R :=
  { SubmonoidClass.subtype s, AddSubmonoidClass.subtype s with toFun := (↑) }

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: (subtype s : s -> R) = ((↑) : s -> R)
  proof: rfl

中文:
定理 coe_subtype
  结论: (subtype s : s -> R) = ((↑) : s -> R)
  证明: rfl

Depends on / 依赖: Opens.isDominant_, dense_univ, infer_instance
-/
theorem coe_subtype : (subtype s : s -> R) = ((↑) : s -> R) :=
  rfl

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
    SubsemiringClass.subtype s x = x := rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  proof: fun _ => by
  simp

中文:
引理 subtype_injective
  证明: fun _ => by
  simp
-/
lemma subtype_injective :
    Function.Injective (SubsemiringClass.subtype s) := fun _ => by
  simp

-- Prefer subclasses of `Semiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `Semiring` is a `Semiring`. -/
instance (priority := 75) toSemiring {R} [Semiring R] [SetLike S R] [SubsemiringClass S R] :
    Semiring s := fast_instance%
  Subtype.coe_injective.semiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/--
Instance `toCommSemiring` / 实例 `toCommSemiring`

English:
instance toCommSemiring
  signature: {R} [CommSemiring R] [SetLike S R] [SubsemiringClass S R]
  body: fast_instance%
  Subtype.coe_injective.commSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

中文:
实例 toCommSemiring
  签名: {R} [CommSemiring R] [SetLike S R] [SubsemiringClass S R]
  定义体: fast_instance%
  Subtype.coe_injective.commSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

Depends on / 依赖: fast_instance
-/
instance toCommSemiring {R} [CommSemiring R] [SetLike S R] [SubsemiringClass S R] :
    CommSemiring s := fast_instance%
  Subtype.coe_injective.commSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

end SubsemiringClass

end SubsemiringClass

variable [NonAssocSemiring S]

/--
Definition of `Subsemiring` / `Subsemiring` 的定义

English:
structure Subsemiring
  parameters: (R : Type u) [NonAssocSemiring R]
  extends: Submonoid R, AddSubmonoid R
  (no additional axioms)

中文:
结构 Subsemiring
  参数: (R : 类型u) [NonAssocSemiring R]
  继承: Submonoid R, AddSubmonoid R
  (无附加公理)
-/
structure Subsemiring (R : Type u) [NonAssocSemiring R] extends Submonoid R, AddSubmonoid R

/-- Reinterpret a `Subsemiring` as a `Submonoid`. -/
add_decl_doc Subsemiring.toSubmonoid

/-- Reinterpret a `Subsemiring` as an `AddSubmonoid`. -/
add_decl_doc Subsemiring.toAddSubmonoid

namespace Subsemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Subsemiring R) R
  body: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

中文:
实例 :
  签名: SetLike (Subsemiring R) R
  定义体: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (Subsemiring R) R where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Subsemiring R)
  body: .ofSetLike (Subsemiring R) R

initialize_simps_projections Subsemiring (carrier -> coe, as_prefix coe)

中文:
实例 :
  签名: PartialOrder (Subsemiring R)
  定义体: .ofSetLike (Subsemiring R) R

initialize_simps_projections Subsemiring (carrier -> coe, as_prefix coe)

Depends on / 依赖: Subsemiring, ofSetLike
-/
instance : PartialOrder (Subsemiring R) := .ofSetLike (Subsemiring R) R

initialize_simps_projections Subsemiring (carrier -> coe, as_prefix coe)

/-- The actual `Subsemiring` obtained from an element of a `SubsemiringClass`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S R : Type*} [NonAssocSemiring R] [SetLike S R] [SubsemiringClass S R]
  body: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _

中文:
定义 ofClass
  签名: {S R : 类型} [NonAssocSemiring R] [SetLike S R] [SubsemiringClass S R]
  定义体: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
-/
def ofClass {S R : Type*} [NonAssocSemiring R] [SetLike S R] [SubsemiringClass S R]
    (s : S) : Subsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _

instance (priority := 100) : CanLift (Set R) (Subsemiring R) (↑)
    (fun s => 0 in s ∧ (forall {x y}, x in s -> y in s -> x + y in s) ∧ 1 in s ∧
      forall {x y}, x in s -> y in s -> x * y in s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        one_mem' := h.2.2.1
        mul_mem' := h.2.2.2 },
      rfl ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubsemiringClass (Subsemiring R) R
  body: zero_mem'
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  one_mem {s} := Submonoid.one_mem' s.toSubmonoid
  mul_mem {s} := Subsemigroup.mul_mem' s.toSubmonoid.toSubsemigroup

中文:
实例 :
  签名: SubsemiringClass (Subsemiring R) R
  定义体: zero_mem'
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  one_mem {s} := Submonoid.one_mem' s.toSubmonoid
  mul_mem {s} := Subsemigroup.mul_mem' s.toSubmonoid.toSubsemigroup

Depends on / 依赖: zero_mem
-/
instance : SubsemiringClass (Subsemiring R) R where
  zero_mem := zero_mem'
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  one_mem {s} := Submonoid.one_mem' s.toSubmonoid
  mul_mem {s} := Subsemigroup.mul_mem' s.toSubmonoid.toSubsemigroup

/-- Turn a `Subsemiring` into a `NonUnitalSubsemiring` by forgetting that it contains `1`. -/
@[reducible]
/--
Definition of `toNonUnitalSubsemiring` / `toNonUnitalSubsemiring` 的定义

English:
definition toNonUnitalSubsemiring
  signature: (S : Subsemiring R)
  body: S

@[simp]

中文:
定义 toNonUnitalSubsemiring
  签名: (S : Subsemiring R)
  定义体: S

@[simp]
-/
def toNonUnitalSubsemiring (S : Subsemiring R) : NonUnitalSubsemiring R where __ := S

@[simp]
/--
theorem `mem_toSubmonoid` / 定理 `mem_toSubmonoid`

English:
theorem mem_toSubmonoid
  given: {s : Subsemiring R} {x : R}
  statement: x in s.toSubmonoid ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toSubmonoid
  条件: {s : Subsemiring R} {x : R}
  结论: x in s.toSubmonoid ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubmonoid {s : Subsemiring R} {x : R} : x in s.toSubmonoid ↔ x in s :=
  Iff.rfl

@[simp]
/--
lemma `mem_toNonUnitalSubsemiring` / 引理 `mem_toNonUnitalSubsemiring`

English:
lemma mem_toNonUnitalSubsemiring
  given: {S : Subsemiring R} {x : R}
  proof: .rfl

中文:
引理 mem_toNonUnitalSubsemiring
  条件: {S : Subsemiring R} {x : R}
  证明: .rfl
-/
lemma mem_toNonUnitalSubsemiring {S : Subsemiring R} {x : R} :
    x in S.toNonUnitalSubsemiring ↔ x in S := .rfl

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : Subsemiring R} {x : R}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_carrier
  条件: {s : Subsemiring R} {x : R}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : Subsemiring R} {x : R} : x in s.carrier ↔ x in s :=
  Iff.rfl

@[simp]
/--
lemma `coe_toNonUnitalSubsemiring` / 引理 `coe_toNonUnitalSubsemiring`

English:
lemma coe_toNonUnitalSubsemiring
  given: (S : Subsemiring R)
  statement: (S.toNonUnitalSubsemiring : Set R) = S
  proof: rfl

@[simp]

中文:
引理 coe_toNonUnitalSubsemiring
  条件: (S : Subsemiring R)
  结论: (S.toNonUnitalSubsemiring : Set R) = S
  证明: rfl

@[simp]
-/
lemma coe_toNonUnitalSubsemiring (S : Subsemiring R) : (S.toNonUnitalSubsemiring : Set R) = S := rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {toSubmonoid : Submonoid R} (add_mem zero_mem) {x : R}
  proof: .rfl

@[simp]

中文:
定理 mem_mk
  条件: {toSubmonoid : Submonoid R} (add_mem zero_mem) {x : R}
  证明: .rfl

@[simp]
-/
theorem mem_mk {toSubmonoid : Submonoid R} (add_mem zero_mem) {x : R} :
    x in mk toSubmonoid add_mem zero_mem ↔ x in toSubmonoid := .rfl

@[simp]
/--
theorem `coe_set_mk` / 定理 `coe_set_mk`

English:
theorem coe_set_mk
  given: {toSubmonoid : Submonoid R} (add_mem zero_mem)
  proof: rfl

中文:
定理 coe_set_mk
  条件: {toSubmonoid : Submonoid R} (add_mem zero_mem)
  证明: rfl
-/
theorem coe_set_mk {toSubmonoid : Submonoid R} (add_mem zero_mem) :
    (mk toSubmonoid add_mem zero_mem : Set R) = toSubmonoid := rfl

/-- Two subsemirings are equal if they have the same elements. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : Subsemiring R} (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

中文:
定理 ext
  条件: {S T : Subsemiring R} (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : Subsemiring R} (h : forall x, x in S ↔ x in T) : S = T :=
  SetLike.ext h

/-- Copy of a subsemiring with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps coe toSubmonoid]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : Subsemiring R) (s : Set R) (hs : s = ↑S)
  body: { S.toAddSubmonoid.copy s hs, S.toSubmonoid.copy s hs with carrier := s }

中文:
定义 copy
  签名: (S : Subsemiring R) (s : Set R) (hs : s = ↑S)
  定义体: { S.toAddSubmonoid.copy s hs, S.toSubmonoid.copy s hs with carrier := s }
-/
protected def copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : Subsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubmonoid.copy s hs with carrier := s }

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : Subsemiring R) (s : Set R) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : Subsemiring R) (s : Set R) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

/--
theorem `toSubmonoid_injective` / 定理 `toSubmonoid_injective`

English:
theorem toSubmonoid_injective
  statement: Function.Injective (toSubmonoid : Subsemiring R -> Submonoid R)

中文:
定理 toSubmonoid_injective
  结论: Function.Injective (toSubmonoid : Subsemiring R -> Submonoid R)
-/
theorem toSubmonoid_injective : Function.Injective (toSubmonoid : Subsemiring R -> Submonoid R)
  | _, _, h => ext (SetLike.ext_iff.mp h :)

/--
theorem `toAddSubmonoid_injective` / 定理 `toAddSubmonoid_injective`

English:
theorem toAddSubmonoid_injective

中文:
定理 toAddSubmonoid_injective
-/
theorem toAddSubmonoid_injective :
    Function.Injective (toAddSubmonoid : Subsemiring R -> AddSubmonoid R)
  | _, _, h => ext (SetLike.ext_iff.mp h :)

/--
lemma `toNonUnitalSubsemiring_injective` / 引理 `toNonUnitalSubsemiring_injective`

English:
lemma toNonUnitalSubsemiring_injective
  proof: fun S₁ S₂ h => SetLike.ext'_iff.2
    (show (S₁.toNonUnitalSubsemiring : Set R) = S₂ from SetLike.ext'_iff.1 h)

中文:
引理 toNonUnitalSubsemiring_injective
  证明: fun S₁ S₂ h => SetLike.ext'_iff.2
    (show (S₁.toNonUnitalSubsemiring : Set R) = S₂ from SetLike.ext'_iff.1 h)

Depends on / 依赖: SetLike, SetLike.ext, _iff, toNonUnitalSubsemiring
-/
lemma toNonUnitalSubsemiring_injective :
    Function.Injective (toNonUnitalSubsemiring : Subsemiring R -> _) :=
  fun S₁ S₂ h => SetLike.ext'_iff.2
    (show (S₁.toNonUnitalSubsemiring : Set R) = S₂ from SetLike.ext'_iff.1 h)

/--
lemma `toNonUnitalSubsemiring_inj` / 引理 `toNonUnitalSubsemiring_inj`

English:
lemma toNonUnitalSubsemiring_inj
  given: {S₁ S₂ : Subsemiring R}
  proof: toNonUnitalSubsemiring_injective.eq_iff

中文:
引理 toNonUnitalSubsemiring_inj
  条件: {S₁ S₂ : Subsemiring R}
  证明: toNonUnitalSubsemiring_injective.eq_iff

Depends on / 依赖: eq_iff, toNonUnitalSubsemiring_injective, toNonUnitalSubsemiring_injective.eq_iff
-/
lemma toNonUnitalSubsemiring_inj {S₁ S₂ : Subsemiring R} :
    S₁.toNonUnitalSubsemiring = S₂.toNonUnitalSubsemiring ↔ S₁ = S₂ :=
  toNonUnitalSubsemiring_injective.eq_iff

/--
lemma `one_mem_toNonUnitalSubsemiring` / 引理 `one_mem_toNonUnitalSubsemiring`

English:
lemma one_mem_toNonUnitalSubsemiring
  given: (S : Subsemiring R)
  statement: (1 : R) in S.toNonUnitalSubsemiring
  proof: S.one_mem

中文:
引理 one_mem_toNonUnitalSubsemiring
  条件: (S : Subsemiring R)
  结论: (1 : R) in S.toNonUnitalSubsemiring
  证明: S.one_mem

Depends on / 依赖: S.one_mem, one_mem
-/
lemma one_mem_toNonUnitalSubsemiring (S : Subsemiring R) : (1 : R) in S.toNonUnitalSubsemiring :=
  S.one_mem

/-- Construct a `Subsemiring R` from a set `s`, a submonoid `sm`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
@[simps coe]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (s : Set R) (sm : Submonoid R) (hm : ↑sm = s) (sa : AddSubmonoid R)
  body: s
  zero_mem' := by exact ha ▸ sa.zero_mem
  one_mem' := by exact hm ▸ sm.one_mem
  add_mem' {x y} := by simpa only [← ha] using! sa.add_mem
  mul_mem' {x y} := by simpa only [← hm] using! sm.mul_mem

@[simp]

中文:
定义 mk'
  签名: (s : Set R) (sm : Submonoid R) (hm : ↑sm = s) (sa : AddSubmonoid R)
  定义体: s
  zero_mem' := by exact ha ▸ sa.zero_mem
  one_mem' := by exact hm ▸ sm.one_mem
  add_mem' {x y} := by simpa only [← ha] using! sa.add_mem
  mul_mem' {x y} := by simpa only [← hm] using! sm.mul_mem

@[simp]
-/
protected def mk' (s : Set R) (sm : Submonoid R) (hm : ↑sm = s) (sa : AddSubmonoid R)
    (ha : ↑sa = s) : Subsemiring R where
  carrier := s
  zero_mem' := by exact ha ▸ sa.zero_mem
  one_mem' := by exact hm ▸ sm.one_mem
  add_mem' {x y} := by simpa only [← ha] using! sa.add_mem
  mul_mem' {x y} := by simpa only [← hm] using! sm.mul_mem

@[simp]
/--
theorem `mem_mk'` / 定理 `mem_mk'`

English:
theorem mem_mk'
  statement: {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk'
  结论: {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s)
    {x : R} : x in Subsemiring.mk' s sm hm sa ha ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `mk'_toSubmonoid` / 定理 `mk'_toSubmonoid`

English:
theorem mk'_toSubmonoid
  statement: {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
  proof: SetLike.coe_injective hm.symm

@[simp]

中文:
定理 mk'_toSubmonoid
  结论: {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
  证明: SetLike.coe_injective hm.symm

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, hm.symm
-/
theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm

@[simp]
/--
theorem `mk'_toAddSubmonoid` / 定理 `mk'_toAddSubmonoid`

English:
theorem mk'_toAddSubmonoid
  statement: {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
  proof: SetLike.coe_injective ha.symm

中文:
定理 mk'_toAddSubmonoid
  结论: {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
  证明: SetLike.coe_injective ha.symm
-/
theorem mk'_toAddSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toAddSubmonoid = sa :=
  SetLike.coe_injective ha.symm

end Subsemiring

namespace Subsemiring

variable (s : Subsemiring R)

/--
theorem `one_mem` / 定理 `one_mem`

English:
theorem one_mem
  statement: (1 : R) in s
  proof: one_mem s

中文:
定理 one_mem
  结论: (1 : R) in s
  证明: one_mem s
-/
protected theorem one_mem : (1 : R) in s :=
  one_mem s

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : R) in s
  proof: zero_mem s

中文:
定理 zero_mem
  结论: (0 : R) in s
  证明: zero_mem s
-/
protected theorem zero_mem : (0 : R) in s :=
  zero_mem s

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
Instance `toNonAssocSemiring` / 实例 `toNonAssocSemiring`

English:
instance toNonAssocSemiring
  signature: : NonAssocSemiring s
  body: SubsemiringClass.toNonAssocSemiring _

@[simp, norm_cast]

中文:
实例 toNonAssocSemiring
  签名: : NonAssocSemiring s
  定义体: SubsemiringClass.toNonAssocSemiring _

@[simp, norm_cast]

Depends on / 依赖: SubsemiringClass, SubsemiringClass.toNonAssocSemiring, toNonAssocSemiring
-/
instance toNonAssocSemiring : NonAssocSemiring s :=
  SubsemiringClass.toNonAssocSemiring _

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : s) : R) = (1 : R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_one
  结论: ((1 : s) : R) = (1 : R)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_one : ((1 : s) : R) = (1 : R) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : s) : R) = (0 : R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ((0 : s) : R) = (0 : R)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ((0 : s) : R) = (0 : R) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : s)
  statement: ((x + y : s) : R) = (x + y : R)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (x y : s)
  结论: ((x + y : s) : R) = (x + y : R)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : s)
  statement: ((x * y : s) : R) = (x * y : R)
  proof: rfl

中文:
定理 coe_mul
  条件: (x y : s)
  结论: ((x * y : s) : R) = (x * y : R)
  证明: rfl
-/
theorem coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) :=
  rfl

/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: [Nontrivial R]
  body: nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)

中文:
实例 nontrivial
  签名: [Nontrivial R]
  定义体: nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)

Depends on / 依赖: Subtype, Subtype.val, congr_arg, nontrivial_of_ne, zero_ne_one
-/
instance nontrivial [Nontrivial R] : Nontrivial s :=
  nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)

/--
theorem `pow_mem` / 定理 `pow_mem`

English:
theorem pow_mem
  statement: {R : Type*} [Semiring R] (s : Subsemiring R) {x : R} (hx : x in s)
  proof: pow_mem hx n

中文:
定理 pow_mem
  结论: {R : 类型} [Semiring R] (s : Subsemiring R) {x : R} (hx : x in s)
  证明: pow_mem hx n
-/
protected theorem pow_mem {R : Type*} [Semiring R] (s : Subsemiring R) {x : R} (hx : x in s)
    (n : Nat) : x ^ n in s :=
  pow_mem hx n

/--
Instance `noZeroDivisors` / 实例 `noZeroDivisors`

English:
instance noZeroDivisors
  signature: [NoZeroDivisors R]
  body: (eq_zero_or_eq_zero_of_mul_eq_zero <| Subtype.ext_iff.mp h).imp Subtype.ext Subtype.ext

中文:
实例 noZeroDivisors
  签名: [NoZeroDivisors R]
  定义体: (eq_zero_or_eq_zero_of_mul_eq_zero <| Subtype.ext_iff.mp h).imp Subtype.ext Subtype.ext

Depends on / 依赖: Subtype, Subtype.ext, Subtype.ext_iff.mp, eq_zero_or_eq_zero_of_mul_eq_zero, ext_iff
-/
instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s where
  eq_zero_or_eq_zero_of_mul_eq_zero {_ _} h :=
    (eq_zero_or_eq_zero_of_mul_eq_zero <| Subtype.ext_iff.mp h).imp Subtype.ext Subtype.ext

/--
Instance `toSemiring` / 实例 `toSemiring`

English:
instance toSemiring
  signature: {R} [Semiring R] (s : Subsemiring R)
  body: { s.toNonAssocSemiring, s.toSubmonoid.toMonoid with }

@[simp, norm_cast]

中文:
实例 toSemiring
  签名: {R} [Semiring R] (s : Subsemiring R)
  定义体: { s.toNonAssocSemiring, s.toSubmonoid.toMonoid with }

@[simp, norm_cast]

Depends on / 依赖: s.toNonAssocSemiring, s.toSubmonoid.toMonoid, toMonoid, toNonAssocSemiring, toSubmonoid
-/
instance toSemiring {R} [Semiring R] (s : Subsemiring R) : Semiring s :=
  { s.toNonAssocSemiring, s.toSubmonoid.toMonoid with }

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: {R} [Semiring R] (s : Subsemiring R) (x : s) (n : Nat)
  proof: rfl

中文:
定理 coe_pow
  条件: {R} [Semiring R] (s : Subsemiring R) (x : s) (n : 自然数)
  证明: rfl
-/
theorem coe_pow {R} [Semiring R] (s : Subsemiring R) (x : s) (n : Nat) :
    ((x ^ n : s) : R) = (x : R) ^ n := rfl

/--
Instance `toCommSemiring` / 实例 `toCommSemiring`

English:
instance toCommSemiring
  signature: {R} [CommSemiring R] (s : Subsemiring R)
  body: { s.toSemiring with mul_comm := fun _ _ => Subtype.ext <| mul_comm _ _ }

中文:
实例 toCommSemiring
  签名: {R} [CommSemiring R] (s : Subsemiring R)
  定义体: { s.toSemiring with mul_comm := fun _ _ => Subtype.ext <| mul_comm _ _ }

Depends on / 依赖: Subtype, Subtype.ext, mul_comm, s.toSemiring, toSemiring
-/
instance toCommSemiring {R} [CommSemiring R] (s : Subsemiring R) : CommSemiring s :=
  { s.toSemiring with mul_comm := fun _ _ => Subtype.ext <| mul_comm _ _ }

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : s ->+* R
  body: { s.toSubmonoid.subtype, s.toAddSubmonoid.subtype with toFun := (↑) }

中文:
定义 subtype
  签名: : s ->+* R
  定义体: { s.toSubmonoid.subtype, s.toAddSubmonoid.subtype with toFun := (↑) }

Depends on / 依赖: s.toAddSubmonoid.subtype, s.toSubmonoid.subtype, subtype, toAddSubmonoid, toSubmonoid
-/
def subtype : s ->+* R :=
  { s.toSubmonoid.subtype, s.toAddSubmonoid.subtype with toFun := (↑) }

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
    s.subtype x = x := rfl

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
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: ⇑s.subtype = ((↑) : s -> R)
  proof: rfl

中文:
定理 coe_subtype
  结论: ⇑s.subtype = ((↑) : s -> R)
  证明: rfl
-/
theorem coe_subtype : ⇑s.subtype = ((↑) : s -> R) :=
  rfl

/--
theorem `nsmul_mem` / 定理 `nsmul_mem`

English:
theorem nsmul_mem
  given: {x : R} (hx : x in s) (n : Nat)
  statement: n • x in s
  proof: nsmul_mem hx n

@[simp]

中文:
定理 nsmul_mem
  条件: {x : R} (hx : x in s) (n : 自然数)
  结论: n • x in s
  证明: nsmul_mem hx n

@[simp]
-/
protected theorem nsmul_mem {x : R} (hx : x in s) (n : Nat) : n • x in s :=
  nsmul_mem hx n

@[simp]
/--
theorem `coe_toSubmonoid` / 定理 `coe_toSubmonoid`

English:
theorem coe_toSubmonoid
  given: (s : Subsemiring R)
  statement: (s.toSubmonoid : Set R) = s
  proof: rfl

@[simp]

中文:
定理 coe_toSubmonoid
  条件: (s : Subsemiring R)
  结论: (s.toSubmonoid : Set R) = s
  证明: rfl

@[simp]
-/
theorem coe_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid : Set R) = s :=
  rfl

@[simp]
/--
theorem `coe_carrier_toSubmonoid` / 定理 `coe_carrier_toSubmonoid`

English:
theorem coe_carrier_toSubmonoid
  given: (s : Subsemiring R)
  statement: (s.toSubmonoid.carrier : Set R) = s
  proof: rfl

中文:
定理 coe_carrier_toSubmonoid
  条件: (s : Subsemiring R)
  结论: (s.toSubmonoid.carrier : Set R) = s
  证明: rfl
-/
theorem coe_carrier_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid.carrier : Set R) = s :=
  rfl

/--
theorem `mem_toAddSubmonoid` / 定理 `mem_toAddSubmonoid`

English:
theorem mem_toAddSubmonoid
  given: {s : Subsemiring R} {x : R}
  statement: x in s.toAddSubmonoid ↔ x in s
  proof: Iff.rfl

中文:
定理 mem_toAddSubmonoid
  条件: {s : Subsemiring R} {x : R}
  结论: x in s.toAddSubmonoid ↔ x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toAddSubmonoid {s : Subsemiring R} {x : R} : x in s.toAddSubmonoid ↔ x in s :=
  Iff.rfl

/--
theorem `coe_toAddSubmonoid` / 定理 `coe_toAddSubmonoid`

English:
theorem coe_toAddSubmonoid
  given: (s : Subsemiring R)
  statement: (s.toAddSubmonoid : Set R) = s
  proof: rfl

中文:
定理 coe_toAddSubmonoid
  条件: (s : Subsemiring R)
  结论: (s.toAddSubmonoid : Set R) = s
  证明: rfl
-/
theorem coe_toAddSubmonoid (s : Subsemiring R) : (s.toAddSubmonoid : Set R) = s :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (Subsemiring R)
  body: ⟨{ (⊤ : Submonoid R), (⊤ : AddSubmonoid R) with }⟩

@[simp]

中文:
实例 :
  签名: Top (Subsemiring R)
  定义体: ⟨{ (⊤ : Submonoid R), (⊤ : AddSubmonoid R) with }⟩

@[simp]

Depends on / 依赖: AddSubmonoid, Submonoid
-/
instance : Top (Subsemiring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubmonoid R) with }⟩

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : R)
  statement: x in (⊤ : Subsemiring R)
  proof: Set.mem_univ x

@[simp, norm_cast]

中文:
定理 mem_top
  条件: (x : R)
  结论: x in (⊤ : Subsemiring R)
  证明: Set.mem_univ x

@[simp, norm_cast]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top (x : R) : x in (⊤ : Subsemiring R) :=
  Set.mem_univ x

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : Subsemiring R) : Set R) = Set.univ
  proof: rfl

中文:
定理 coe_top
  结论: ((⊤ : Subsemiring R) : Set R) = Set.univ
  证明: rfl
-/
theorem coe_top : ((⊤ : Subsemiring R) : Set R) = Set.univ :=
  rfl

end Subsemiring

namespace Subsemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Subsemiring R)
  body: ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubmonoid ⊓ t.toAddSubmonoid with carrier := s inter t }⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Min (Subsemiring R)
  定义体: ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubmonoid ⊓ t.toAddSubmonoid with carrier := s inter t }⟩

@[simp, norm_cast]

Depends on / 依赖: carrier, s.toAddSubmonoid, s.toSubmonoid, t.toAddSubmonoid, t.toSubmonoid, toAddSubmonoid, toSubmonoid
-/
instance : Min (Subsemiring R) :=
  ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubmonoid ⊓ t.toAddSubmonoid with carrier := s inter t }⟩

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (p p' : Subsemiring R)
  statement: ((p ⊓ p' : Subsemiring R) : Set R) = (p : Set R) inter p'
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (p p' : Subsemiring R)
  结论: ((p ⊓ p' : Subsemiring R) : Set R) = (p : Set R) inter p'
  证明: rfl

@[simp]
-/
theorem coe_inf (p p' : Subsemiring R) : ((p ⊓ p' : Subsemiring R) : Set R) = (p : Set R) inter p' :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {p p' : Subsemiring R} {x : R}
  statement: x in p ⊓ p' ↔ x in p ∧ x in p'
  proof: Iff.rfl

中文:
定理 mem_inf
  条件: {p p' : Subsemiring R} {x : R}
  结论: x in p ⊓ p' ↔ x in p ∧ x in p'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {p p' : Subsemiring R} {x : R} : x in p ⊓ p' ↔ x in p ∧ x in p' :=
  Iff.rfl


end Subsemiring

namespace RingHom

variable {s : Subsemiring R} {σR : Type*} [SetLike σR R] [SubsemiringClass σR R]

open Subsemiring

/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: (f : R ->+* S) (s : σR)
  body: f.comp SubsemiringClass.subtype s

@[simp]

中文:
定义 domRestrict
  签名: (f : R ->+* S) (s : σR)
  定义体: f.comp SubsemiringClass.subtype s

@[simp]

Depends on / 依赖: SubsemiringClass, SubsemiringClass.subtype, f.comp, subtype
-/
def domRestrict (f : R ->+* S) (s : σR) : s ->+* S :=
f.comp SubsemiringClass.subtype s

@[simp]
/--
theorem `domRestrict_apply` / 定理 `domRestrict_apply`

English:
theorem domRestrict_apply
  given: (f : R ->+* S) {s : σR} (x : s)
  statement: f.domRestrict s x = f x
  proof: rfl

@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply

中文:
定理 domRestrict_apply
  条件: (f : R ->+* S) {s : σR} (x : s)
  结论: f.domRestrict s x = f x
  证明: rfl

@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
-/
theorem domRestrict_apply (f : R ->+* S) {s : σR} (x : s) : f.domRestrict s x = f x :=
  rfl

@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply

/--
Definition of `eqLocusS` / `eqLocusS` 的定义

English:
definition eqLocusS
  signature: (f g : R ->+* S)
  body: { (f : R ->* S).eqLocusM g, (f : R ->+ S).eqLocusM g with carrier := { x | f x = g x } }

@[simp]

中文:
定义 eqLocusS
  签名: (f g : R ->+* S)
  定义体: { (f : R ->* S).eqLocusM g, (f : R ->+ S).eqLocusM g with carrier := { x | f x = g x } }

@[simp]

Depends on / 依赖: carrier, eqLocusM
-/
def eqLocusS (f g : R ->+* S) : Subsemiring R :=
  { (f : R ->* S).eqLocusM g, (f : R ->+ S).eqLocusM g with carrier := { x | f x = g x } }

@[simp]
/--
theorem `mem_eqLocusS` / 定理 `mem_eqLocusS`

English:
theorem mem_eqLocusS
  given: {f g : R ->+* S} {x : R}
  statement: x in f.eqLocusS g ↔ f x = g x
  proof: Iff.rfl

@[simp]

中文:
定理 mem_eqLocusS
  条件: {f g : R ->+* S} {x : R}
  结论: x in f.eqLocusS g ↔ f x = g x
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_eqLocusS {f g : R ->+* S} {x : R} : x in f.eqLocusS g ↔ f x = g x := Iff.rfl

@[simp]
/--
theorem `eqLocusS_same` / 定理 `eqLocusS_same`

English:
theorem eqLocusS_same
  given: (f : R ->+* S)
  statement: f.eqLocusS f = ⊤
  proof: SetLike.ext fun _ => eq_self_iff_true _

中文:
定理 eqLocusS_same
  条件: (f : R ->+* S)
  结论: f.eqLocusS f = ⊤
  证明: SetLike.ext fun _ => eq_self_iff_true _

Depends on / 依赖: SetLike, SetLike.ext, eq_self_iff_true
-/
theorem eqLocusS_same (f : R ->+* S) : f.eqLocusS f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

end RingHom

/--
Definition of `NonUnitalSubsemiring.toSubsemiring` / `NonUnitalSubsemiring.toSubsemiring` 的定义

English:
definition NonUnitalSubsemiring.toSubsemiring
  signature: (S : NonUnitalSubsemiring R) (h1 : 1 in S)
  body: S
  one_mem' := h1

中文:
定义 NonUnitalSubsemiring.toSubsemiring
  签名: (S : NonUnitalSubsemiring R) (h1 : 1 in S)
  定义体: S
  one_mem' := h1
-/
def NonUnitalSubsemiring.toSubsemiring (S : NonUnitalSubsemiring R) (h1 : 1 in S) :
    Subsemiring R where
  __ := S
  one_mem' := h1

/--
lemma `Subsemiring.toNonUnitalSubsemiring_toSubsemiring` / 引理 `Subsemiring.toNonUnitalSubsemiring_toSubsemiring`

English:
lemma Subsemiring.toNonUnitalSubsemiring_toSubsemiring
  given: (S : Subsemiring R)
  proof: rfl

中文:
引理 Subsemiring.toNonUnitalSubsemiring_toSubsemiring
  条件: (S : Subsemiring R)
  证明: rfl
-/
lemma Subsemiring.toNonUnitalSubsemiring_toSubsemiring (S : Subsemiring R) :
    S.toNonUnitalSubsemiring.toSubsemiring S.one_mem = S := rfl

/--
lemma `NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring` / 引理 `NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring`

English:
lemma NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring
  given: (S : NonUnitalSubsemiring R) (h1)
  proof: rfl

中文:
引理 NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring
  条件: (S : NonUnitalSubsemiring R) (h1)
  证明: rfl
-/
lemma NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring (S : NonUnitalSubsemiring R) (h1) :
    (NonUnitalSubsemiring.toSubsemiring S h1).toNonUnitalSubsemiring = S := rfl
