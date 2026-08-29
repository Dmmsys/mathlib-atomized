/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-!
# Subfields

Let `K` be a division ring, for example a field.
This file defines the "bundled" subfield type `Subfield K`, a type
whose terms correspond to subfields of `K`. Note we do not require the "subfields" to be
commutative, so they are really sub-division rings / skew fields. This is the preferred way to talk
about subfields in mathlib. Unbundled subfields (`s : Set K` and `IsSubfield s`)
are not in this file, and they will ultimately be deprecated.

We prove that subfields are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set K` to `Subfield K`, sending a subset of `K`
to the subfield it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(K : Type u) [DivisionRing K] (L : Type u) [DivisionRing L] (f g : K →+* L)`
`(A : Subfield K) (B : Subfield L) (s : Set K)`

* `Subfield K` : the type of subfields of a division ring `K`.

## Implementation notes

A subfield is implemented as a subring which is closed under `⁻¹`.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subfield's underlying set.

## Tags
subfield, subfields
-/

@[expose] public section


universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

/--
Definition of `SubfieldClass` / `SubfieldClass` 的定义

English:
class SubfieldClass
  parameters: (S K : Type*) [DivisionRing K] [SetLike S K]
  extends: SubringClass S K, InvMemClass S K
  (no additional axioms)

中文:
类 SubfieldClass
  参数: (S K : 类型) [DivisionRing K] [SetLike S K]
  继承: SubringClass S K, InvMemClass S K
  (无附加公理)
-/
class SubfieldClass (S K : Type*) [DivisionRing K] [SetLike S K] : Prop
    extends SubringClass S K, InvMemClass S K

namespace SubfieldClass

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

-- See note [lower instance priority]
/-- A subfield contains `1`, products and inverses.

Be assured that we're not actually proving that subfields are subgroups:
`SubgroupClass` is really an abbreviation of `SubgroupWithOrWithoutZeroClass`.
-/
instance (priority := 100) toSubgroupClass : SubgroupClass S K :=
  { h with }

variable {S} {x : K}

@[simp, aesop safe (rule_sets := [SetLike])]
/--
lemma `nnratCast_mem` / 引理 `nnratCast_mem`

English:
lemma nnratCast_mem
  given: (s : S) (q : Rat>=0)
  statement: (q : K) in s
  proof: by
  simpa only [NNRat.cast_def] using div_mem (natCast_mem s q.num) (natCast_mem s q.den)

@[simp, aesop safe (rule_sets := [SetLike])]

中文:
引理 nnratCast_mem
  条件: (s : S) (q : Rat>=0)
  结论: (q : K) in s
  证明: by
  simpa only [NNRat.cast_def] using div_mem (natCast_mem s q.num) (natCast_mem s q.den)

@[simp, aesop safe (rule_sets := [SetLike])]

Depends on / 依赖: NNRat.cast_def, cast_def, div_mem, natCast_mem, q.den, q.num
-/
lemma nnratCast_mem (s : S) (q : Rat>=0) : (q : K) in s := by
  simpa only [NNRat.cast_def] using div_mem (natCast_mem s q.num) (natCast_mem s q.den)

@[simp, aesop safe (rule_sets := [SetLike])]
/--
lemma `ratCast_mem` / 引理 `ratCast_mem`

English:
lemma ratCast_mem
  given: (s : S) (q : Rat)
  statement: (q : K) in s
  proof: by
  simpa only [Rat.cast_def] using div_mem (intCast_mem s q.num) (natCast_mem s q.den)

中文:
引理 ratCast_mem
  条件: (s : S) (q : Rat)
  结论: (q : K) in s
  证明: by
  simpa only [Rat.cast_def] using div_mem (intCast_mem s q.num) (natCast_mem s q.den)

Depends on / 依赖: Rat.cast_def, cast_def, div_mem, intCast_mem, natCast_mem, q.den, q.num
-/
lemma ratCast_mem (s : S) (q : Rat) : (q : K) in s := by
  simpa only [Rat.cast_def] using div_mem (intCast_mem s q.num) (natCast_mem s q.den)

/--
Instance `instNNRatCast` / 实例 `instNNRatCast`

English:
instance instNNRatCast
  signature: (s : S)
  body: ⟨q, nnratCast_mem s q⟩

中文:
实例 instNNRatCast
  签名: (s : S)
  定义体: ⟨q, nnratCast_mem s q⟩

Depends on / 依赖: nnratCast_mem
-/
instance instNNRatCast (s : S) : NNRatCast s where nnratCast q := ⟨q, nnratCast_mem s q⟩
/--
Instance `instRatCast` / 实例 `instRatCast`

English:
instance instRatCast
  signature: (s : S)
  body: ⟨q, ratCast_mem s q⟩

中文:
实例 instRatCast
  签名: (s : S)
  定义体: ⟨q, ratCast_mem s q⟩

Depends on / 依赖: ratCast_mem
-/
instance instRatCast (s : S) : RatCast s where ratCast q := ⟨q, ratCast_mem s q⟩

/--
lemma `coe_nnratCast` / 引理 `coe_nnratCast`

English:
lemma coe_nnratCast
  given: (s : S) (q : Rat>=0)
  statement: ((q : s) : K) = q
  proof: rfl

中文:
引理 coe_nnratCast
  条件: (s : S) (q : Rat>=0)
  结论: ((q : s) : K) = q
  证明: rfl
-/
@[simp, norm_cast] lemma coe_nnratCast (s : S) (q : Rat>=0) : ((q : s) : K) = q := rfl
/--
lemma `coe_ratCast` / 引理 `coe_ratCast`

English:
lemma coe_ratCast
  given: (s : S) (x : Rat)
  statement: ((x : s) : K) = x
  proof: rfl

@[aesop 90% (rule_sets := [SetLike])]

中文:
引理 coe_ratCast
  条件: (s : S) (x : Rat)
  结论: ((x : s) : K) = x
  证明: rfl

@[aesop 90% (rule_sets := [SetLike])]
-/
@[simp, norm_cast] lemma coe_ratCast (s : S) (x : Rat) : ((x : s) : K) = x := rfl

@[aesop 90% (rule_sets := [SetLike])]
/--
lemma `nnqsmul_mem` / 引理 `nnqsmul_mem`

English:
lemma nnqsmul_mem
  given: (s : S) (q : Rat>=0) (hx : x in s)
  statement: q • x in s
  proof: by
  simpa only [NNRat.smul_def] using mul_mem (nnratCast_mem _ _) hx

@[aesop 90% (rule_sets := [SetLike])]

中文:
引理 nnqsmul_mem
  条件: (s : S) (q : Rat>=0) (hx : x in s)
  结论: q • x in s
  证明: by
  simpa only [NNRat.smul_def] using mul_mem (nnratCast_mem _ _) hx

@[aesop 90% (rule_sets := [SetLike])]

Depends on / 依赖: NNRat.smul_def, mul_mem, nnratCast_mem, smul_def
-/
lemma nnqsmul_mem (s : S) (q : Rat>=0) (hx : x in s) : q • x in s := by
  simpa only [NNRat.smul_def] using mul_mem (nnratCast_mem _ _) hx

@[aesop 90% (rule_sets := [SetLike])]
/--
lemma `qsmul_mem` / 引理 `qsmul_mem`

English:
lemma qsmul_mem
  given: (s : S) (q : Rat) (hx : x in s)
  statement: q • x in s
  proof: by
  simpa only [Rat.smul_def] using mul_mem (ratCast_mem _ _) hx

@[simp, aesop safe (rule_sets := [SetLike])]

中文:
引理 qsmul_mem
  条件: (s : S) (q : Rat) (hx : x in s)
  结论: q • x in s
  证明: by
  simpa only [Rat.smul_def] using mul_mem (ratCast_mem _ _) hx

@[simp, aesop safe (rule_sets := [SetLike])]

Depends on / 依赖: Rat.smul_def, mul_mem, ratCast_mem, smul_def
-/
lemma qsmul_mem (s : S) (q : Rat) (hx : x in s) : q • x in s := by
  simpa only [Rat.smul_def] using mul_mem (ratCast_mem _ _) hx

@[simp, aesop safe (rule_sets := [SetLike])]
/--
lemma `ofScientific_mem` / 引理 `ofScientific_mem`

English:
lemma ofScientific_mem
  given: (s : S) {b : Bool} {n m : Nat}
  proof: SubfieldClass.nnratCast_mem s (OfScientific.ofScientific n b m)

中文:
引理 ofScientific_mem
  条件: (s : S) {b : 布尔} {n m : 自然数}
  证明: SubfieldClass.nnratCast_mem s (OfScientific.ofScientific n b m)

Depends on / 依赖: OfScientific, OfScientific.ofScientific, SubfieldClass, SubfieldClass.nnratCast_mem, nnratCast_mem, ofScientific
-/
lemma ofScientific_mem (s : S) {b : Bool} {n m : Nat} :
    (OfScientific.ofScientific n b m : K) in s :=
  SubfieldClass.nnratCast_mem s (OfScientific.ofScientific n b m)

/--
Instance `instSMulNNRat` / 实例 `instSMulNNRat`

English:
instance instSMulNNRat
  signature: (s : S)
  body: ⟨q • x, nnqsmul_mem s q x.2⟩

中文:
实例 instSMulNNRat
  签名: (s : S)
  定义体: ⟨q • x, nnqsmul_mem s q x.2⟩

Depends on / 依赖: nnqsmul_mem
-/
instance instSMulNNRat (s : S) : SMul Rat>=0 s where smul q x := ⟨q • x, nnqsmul_mem s q x.2⟩
/--
Instance `instSMulRat` / 实例 `instSMulRat`

English:
instance instSMulRat
  signature: (s : S)
  body: ⟨q • x, qsmul_mem s q x.2⟩

中文:
实例 instSMulRat
  签名: (s : S)
  定义体: ⟨q • x, qsmul_mem s q x.2⟩

Depends on / 依赖: qsmul_mem
-/
instance instSMulRat (s : S) : SMul Rat s where smul q x := ⟨q • x, qsmul_mem s q x.2⟩

/--
lemma `coe_nnqsmul` / 引理 `coe_nnqsmul`

English:
lemma coe_nnqsmul
  given: (s : S) (q : Rat>=0) (x : s)
  statement: ↑(q • x) = q • (x : K)
  proof: rfl

中文:
引理 coe_nnqsmul
  条件: (s : S) (q : Rat>=0) (x : s)
  结论: ↑(q • x) = q • (x : K)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_nnqsmul (s : S) (q : Rat>=0) (x : s) : ↑(q • x) = q • (x : K) := rfl
/--
lemma `coe_qsmul` / 引理 `coe_qsmul`

English:
lemma coe_qsmul
  given: (s : S) (q : Rat) (x : s)
  statement: ↑(q • x) = q • (x : K)
  proof: rfl

中文:
引理 coe_qsmul
  条件: (s : S) (q : Rat) (x : s)
  结论: ↑(q • x) = q • (x : K)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_qsmul (s : S) (q : Rat) (x : s) : ↑(q • x) = q • (x : K) := rfl

/-- A subfield inherits a division ring structure -/
instance (priority := 75) toDivisionRing (s : S) : DivisionRing s := fast_instance%
  Subtype.coe_injective.divisionRing ((↑) : s -> K)
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (coe_nnqsmul _) (coe_qsmul _) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

-- Prefer subclasses of `Field` over subclasses of `SubfieldClass`.
/-- A subfield of a field inherits a field structure -/
instance (priority := 75) toField {K} [Field K] [SetLike S K] [SubfieldClass S K] (s : S) :
    Field s := fast_instance%
  Subtype.coe_injective.field ((↑) : s -> K)
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (coe_nnqsmul _) (coe_qsmul _) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

end SubfieldClass

/-- `Subfield R` is the type of subfields of `R`. A subfield of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
@[stacks 09FD "second part"]
/--
Definition of `Subfield` / `Subfield` 的定义

English:
structure Subfield
  parameters: (K : Type u) [DivisionRing K]
  extends: Subring K
  axioms and operations (1):
    - inv_mem' : forall x in carrier, x⁻¹ in carrier

中文:
结构 Subfield
  参数: (K : 类型u) [DivisionRing K]
  继承: Subring K
  公理与运算 (1 个):
    - inv_mem' : 对任意 x in carrier, x⁻¹ in carrier
-/
structure Subfield (K : Type u) [DivisionRing K] extends Subring K where
  /-- A subfield is closed under multiplicative inverses. -/
  inv_mem' : forall x in carrier, x⁻¹ in carrier

/-- Reinterpret a `Subfield` as a `Subring`. -/
add_decl_doc Subfield.toSubring

namespace Subfield

/-- The underlying `AddSubgroup` of a subfield. -/
@[reducible]
/--
Definition of `toAddSubgroup` / `toAddSubgroup` 的定义

English:
definition toAddSubgroup
  signature: (s : Subfield K)
  body: { s.toSubring.toAddSubgroup with }

中文:
定义 toAddSubgroup
  签名: (s : Subfield K)
  定义体: { s.toSubring.toAddSubgroup with }

Depends on / 依赖: s.toSubring.toAddSubgroup, toAddSubgroup, toSubring
-/
def toAddSubgroup (s : Subfield K) : AddSubgroup K :=
  { s.toSubring.toAddSubgroup with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Subfield K) K
  body: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

中文:
实例 :
  签名: SetLike (Subfield K) K
  定义体: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (Subfield K) K where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Subfield K)
  body: .ofSetLike (Subfield K) K

中文:
实例 :
  签名: PartialOrder (Subfield K)
  定义体: .ofSetLike (Subfield K) K

Depends on / 依赖: Subfield, ofSetLike
-/
instance : PartialOrder (Subfield K) := .ofSetLike (Subfield K) K

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubfieldClass (Subfield K) K
  body: s.add_mem'
  zero_mem s := s.zero_mem'
  neg_mem {s} := s.neg_mem'
  mul_mem {s} := s.mul_mem'
  one_mem s := s.one_mem'
  inv_mem {s} := s.inv_mem' _

中文:
实例 :
  签名: SubfieldClass (Subfield K) K
  定义体: s.add_mem'
  zero_mem s := s.zero_mem'
  neg_mem {s} := s.neg_mem'
  mul_mem {s} := s.mul_mem'
  one_mem s := s.one_mem'
  inv_mem {s} := s.inv_mem' _

Depends on / 依赖: add_mem, s.add_mem
-/
instance : SubfieldClass (Subfield K) K where
  add_mem {s} := s.add_mem'
  zero_mem s := s.zero_mem'
  neg_mem {s} := s.neg_mem'
  mul_mem {s} := s.mul_mem'
  one_mem s := s.one_mem'
  inv_mem {s} := s.inv_mem' _

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : Subfield K} {x : K}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_carrier
  条件: {s : Subfield K} {x : K}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : Subfield K} {x : K} : x in s.carrier ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {S : Subring K} {x : K} (h)
  statement: x in (⟨S, h⟩ : Subfield K) ↔ x in S
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk
  条件: {S : Subring K} {x : K} (h)
  结论: x in (⟨S, h⟩ : Subfield K) ↔ x in S
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {S : Subring K} {x : K} (h) : x in (⟨S, h⟩ : Subfield K) ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_set_mk` / 定理 `coe_set_mk`

English:
theorem coe_set_mk
  given: (S : Subring K) (h)
  statement: ((⟨S, h⟩ : Subfield K) : Set K) = S
  proof: rfl

@[simp]

中文:
定理 coe_set_mk
  条件: (S : Subring K) (h)
  结论: ((⟨S, h⟩ : Subfield K) : Set K) = S
  证明: rfl

@[simp]
-/
theorem coe_set_mk (S : Subring K) (h) : ((⟨S, h⟩ : Subfield K) : Set K) = S :=
  rfl

@[simp]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {S S' : Subring K} (h h')
  statement: (⟨S, h⟩ : Subfield K) <= (⟨S', h'⟩ : Subfield K) ↔
  proof: Iff.rfl

中文:
定理 mk_le_mk
  条件: {S S' : Subring K} (h h')
  结论: (⟨S, h⟩ : Subfield K) <= (⟨S', h'⟩ : Subfield K) ↔
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mk_le_mk {S S' : Subring K} (h h') : (⟨S, h⟩ : Subfield K) <= (⟨S', h'⟩ : Subfield K) ↔
    S <= S' :=
  Iff.rfl

/-- Two subfields are equal if they have the same elements. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : Subfield K} (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

中文:
定理 ext
  条件: {S T : Subfield K} (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : Subfield K} (h : forall x, x in S ↔ x in T) : S = T :=
  SetLike.ext h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : Subfield K) (s : Set K) (hs : s = ↑S)
  body: { S.toSubring.copy s hs with
    carrier := s
    inv_mem' := hs.symm ▸ S.inv_mem' }

@[simp, norm_cast]

中文:
定义 copy
  签名: (S : Subfield K) (s : Set K) (hs : s = ↑S)
  定义体: { S.toSubring.copy s hs with
    carrier := s
    inv_mem' := hs.symm ▸ S.inv_mem' }

@[simp, norm_cast]
-/
protected def copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : Subfield K :=
  { S.toSubring.copy s hs with
    carrier := s
    inv_mem' := hs.symm ▸ S.inv_mem' }

@[simp, norm_cast]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (S : Subfield K) (s : Set K) (hs : s = ↑S)
  statement: (S.copy s hs : Set K) = s
  proof: rfl

中文:
定理 coe_copy
  条件: (S : Subfield K) (s : Set K) (hs : s = ↑S)
  结论: (S.copy s hs : Set K) = s
  证明: rfl
-/
theorem coe_copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : (S.copy s hs : Set K) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : Subfield K) (s : Set K) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

@[simp]

中文:
定理 copy_eq
  条件: (S : Subfield K) (s : Set K) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : Subfield K) (s : Set K) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

@[simp]
/--
theorem `coe_toSubring` / 定理 `coe_toSubring`

English:
theorem coe_toSubring
  given: (s : Subfield K)
  statement: (s.toSubring : Set K) = s
  proof: rfl

@[simp]

中文:
定理 coe_toSubring
  条件: (s : Subfield K)
  结论: (s.toSubring : Set K) = s
  证明: rfl

@[simp]
-/
theorem coe_toSubring (s : Subfield K) : (s.toSubring : Set K) = s :=
  rfl

@[simp]
/--
theorem `mem_toSubring` / 定理 `mem_toSubring`

English:
theorem mem_toSubring
  given: (s : Subfield K) (x : K)
  statement: x in s.toSubring ↔ x in s
  proof: Iff.rfl

中文:
定理 mem_toSubring
  条件: (s : Subfield K) (x : K)
  结论: x in s.toSubring ↔ x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubring (s : Subfield K) (x : K) : x in s.toSubring ↔ x in s :=
  Iff.rfl

end Subfield

/--
Definition of `Subring.toSubfield` / `Subring.toSubfield` 的定义

English:
definition Subring.toSubfield
  signature: (s : Subring K) (hinv : forall x in s, x⁻¹ in s)
  body: { s with inv_mem' := hinv }

中文:
定义 Subring.toSubfield
  签名: (s : Subring K) (hinv : 对任意 x in s, x⁻¹ in s)
  定义体: { s with inv_mem' := hinv }

Depends on / 依赖: inv_mem
-/
def Subring.toSubfield (s : Subring K) (hinv : forall x in s, x⁻¹ in s) : Subfield K :=
  { s with inv_mem' := hinv }

namespace Subfield

variable (s t : Subfield K)

section DerivedFromSubfieldClass

/--
theorem `one_mem` / 定理 `one_mem`

English:
theorem one_mem
  statement: (1 : K) in s
  proof: one_mem s

中文:
定理 one_mem
  结论: (1 : K) in s
  证明: one_mem s

Depends on / 依赖: equivShrink, nnratCast, symm.nnratCast
-/
protected theorem one_mem : (1 : K) in s :=
  one_mem s

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : K) in s
  proof: zero_mem s

中文:
定理 zero_mem
  结论: (0 : K) in s
  证明: zero_mem s
-/
protected theorem zero_mem : (0 : K) in s :=
  zero_mem s

/--
theorem `mul_mem` / 定理 `mul_mem`

English:
theorem mul_mem
  given: {x y : K}
  statement: x in s -> y in s -> x * y in s
  proof: mul_mem

中文:
定理 mul_mem
  条件: {x y : K}
  结论: x in s -> y in s -> x * y in s
  证明: mul_mem
-/
protected theorem mul_mem {x y : K} : x in s -> y in s -> x * y in s :=
  mul_mem

/--
theorem `add_mem` / 定理 `add_mem`

English:
theorem add_mem
  given: {x y : K}
  statement: x in s -> y in s -> x + y in s
  proof: add_mem

中文:
定理 add_mem
  条件: {x y : K}
  结论: x in s -> y in s -> x + y in s
  证明: add_mem
-/
protected theorem add_mem {x y : K} : x in s -> y in s -> x + y in s :=
  add_mem

/--
theorem `neg_mem` / 定理 `neg_mem`

English:
theorem neg_mem
  given: {x : K}
  statement: x in s -> -x in s
  proof: neg_mem

中文:
定理 neg_mem
  条件: {x : K}
  结论: x in s -> -x in s
  证明: neg_mem
-/
protected theorem neg_mem {x : K} : x in s -> -x in s :=
  neg_mem

/--
theorem `sub_mem` / 定理 `sub_mem`

English:
theorem sub_mem
  given: {x y : K}
  statement: x in s -> y in s -> x - y in s
  proof: sub_mem

中文:
定理 sub_mem
  条件: {x y : K}
  结论: x in s -> y in s -> x - y in s
  证明: sub_mem
-/
protected theorem sub_mem {x y : K} : x in s -> y in s -> x - y in s :=
  sub_mem

/--
theorem `inv_mem` / 定理 `inv_mem`

English:
theorem inv_mem
  given: {x : K}
  statement: x in s -> x⁻¹ in s
  proof: inv_mem

中文:
定理 inv_mem
  条件: {x : K}
  结论: x in s -> x⁻¹ in s
  证明: inv_mem
-/
protected theorem inv_mem {x : K} : x in s -> x⁻¹ in s :=
  inv_mem

/--
theorem `div_mem` / 定理 `div_mem`

English:
theorem div_mem
  given: {x y : K}
  statement: x in s -> y in s -> x / y in s
  proof: div_mem

中文:
定理 div_mem
  条件: {x y : K}
  结论: x in s -> y in s -> x / y in s
  证明: div_mem
-/
protected theorem div_mem {x y : K} : x in s -> y in s -> x / y in s :=
  div_mem

/--
theorem `pow_mem` / 定理 `pow_mem`

English:
theorem pow_mem
  given: {x : K} (hx : x in s) (n : Nat)
  statement: x ^ n in s
  proof: pow_mem hx n

中文:
定理 pow_mem
  条件: {x : K} (hx : x in s) (n : 自然数)
  结论: x ^ n in s
  证明: pow_mem hx n
-/
protected theorem pow_mem {x : K} (hx : x in s) (n : Nat) : x ^ n in s :=
  pow_mem hx n

/--
theorem `zsmul_mem` / 定理 `zsmul_mem`

English:
theorem zsmul_mem
  given: {x : K} (hx : x in s) (n : Int)
  statement: n • x in s
  proof: zsmul_mem hx n

中文:
定理 zsmul_mem
  条件: {x : K} (hx : x in s) (n : 整数)
  结论: n • x in s
  证明: zsmul_mem hx n
-/
protected theorem zsmul_mem {x : K} (hx : x in s) (n : Int) : n • x in s :=
  zsmul_mem hx n

/--
theorem `intCast_mem` / 定理 `intCast_mem`

English:
theorem intCast_mem
  given: (n : Int)
  statement: (n : K) in s
  proof: intCast_mem s n

中文:
定理 intCast_mem
  条件: (n : 整数)
  结论: (n : K) in s
  证明: intCast_mem s n
-/
protected theorem intCast_mem (n : Int) : (n : K) in s := intCast_mem s n

/--
theorem `zpow_mem` / 定理 `zpow_mem`

English:
theorem zpow_mem
  given: {x : K} (hx : x in s) (n : Int)
  statement: x ^ n in s
  proof: zpow_mem hx n

中文:
定理 zpow_mem
  条件: {x : K} (hx : x in s) (n : 整数)
  结论: x ^ n in s
  证明: zpow_mem hx n
-/
protected theorem zpow_mem {x : K} (hx : x in s) (n : Int) : x ^ n in s := zpow_mem hx n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring s
  body: s.toSubring.toRing

中文:
实例 :
  签名: Ring s
  定义体: s.toSubring.toRing

Depends on / 依赖: s.toSubring.toRing, toRing, toSubring
-/
instance : Ring s :=
  s.toSubring.toRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div s
  body: ⟨fun x y => ⟨x / y, s.div_mem x.2 y.2⟩⟩

中文:
实例 :
  签名: Div s
  定义体: ⟨fun x y => ⟨x / y, s.div_mem x.2 y.2⟩⟩

Depends on / 依赖: div_mem, s.div_mem
-/
instance : Div s :=
  ⟨fun x y => ⟨x / y, s.div_mem x.2 y.2⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv s
  body: ⟨fun x => ⟨x⁻¹, s.inv_mem x.2⟩⟩

中文:
实例 :
  签名: Inv s
  定义体: ⟨fun x => ⟨x⁻¹, s.inv_mem x.2⟩⟩

Depends on / 依赖: inv_mem, s.inv_mem
-/
instance : Inv s :=
  ⟨fun x => ⟨x⁻¹, s.inv_mem x.2⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow s Int
  body: ⟨fun x z => ⟨x ^ z, s.zpow_mem x.2 z⟩⟩

中文:
实例 :
  签名: Pow s 整数
  定义体: ⟨fun x z => ⟨x ^ z, s.zpow_mem x.2 z⟩⟩

Depends on / 依赖: s.zpow_mem, zpow_mem
-/
instance : Pow s Int :=
  ⟨fun x z => ⟨x ^ z, s.zpow_mem x.2 z⟩⟩

/--
Instance `toDivisionRing` / 实例 `toDivisionRing`

English:
instance toDivisionRing
  signature: (s : Subfield K)
  body: SubfieldClass.toDivisionRing s

中文:
实例 toDivisionRing
  签名: (s : Subfield K)
  定义体: SubfieldClass.toDivisionRing s

Depends on / 依赖: SubfieldClass, SubfieldClass.toDivisionRing, toDivisionRing
-/
instance toDivisionRing (s : Subfield K) : DivisionRing s := SubfieldClass.toDivisionRing s

/--
Instance `toField` / 实例 `toField`

English:
instance toField
  signature: {K} [Field K] (s : Subfield K)
  body: SubfieldClass.toField s

@[simp, norm_cast]

中文:
实例 toField
  签名: {K} [Field K] (s : Subfield K)
  定义体: SubfieldClass.toField s

@[simp, norm_cast]

Depends on / 依赖: SubfieldClass, SubfieldClass.toField, toField
-/
instance toField {K} [Field K] (s : Subfield K) : Field s := SubfieldClass.toField s

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : s)
  statement: (↑(x + y) : K) = ↑x + ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (x y : s)
  结论: (↑(x + y) : K) = ↑x + ↑y
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (x y : s) : (↑(x + y) : K) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (x y : s)
  statement: (↑(x - y) : K) = ↑x - ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sub
  条件: (x y : s)
  结论: (↑(x - y) : K) = ↑x - ↑y
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sub (x y : s) : (↑(x - y) : K) = ↑x - ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (x : s)
  statement: (↑(-x) : K) = -↑x
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_neg
  条件: (x : s)
  结论: (↑(-x) : K) = -↑x
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_neg (x : s) : (↑(-x) : K) = -↑x :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : s)
  statement: (↑(x * y) : K) = ↑x * ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (x y : s)
  结论: (↑(x * y) : K) = ↑x * ↑y
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mul (x y : s) : (↑(x * y) : K) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (x y : s)
  statement: (↑(x / y) : K) = ↑x / ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_div
  条件: (x y : s)
  结论: (↑(x / y) : K) = ↑x / ↑y
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_div (x y : s) : (↑(x / y) : K) = ↑x / ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (x : s)
  statement: (↑x⁻¹ : K) = (↑x)⁻¹
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_inv
  条件: (x : s)
  结论: (↑x⁻¹ : K) = (↑x)⁻¹
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_inv (x : s) : (↑x⁻¹ : K) = (↑x)⁻¹ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : s) : K) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ((0 : s) : K) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ((0 : s) : K) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : s) : K) = 1
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : s) : K) = 1
  证明: rfl
-/
theorem coe_one : ((1 : s) : K) = 1 :=
  rfl

end DerivedFromSubfieldClass

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (s : Subfield K)
  body: { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]

中文:
定义 subtype
  签名: (s : Subfield K)
  定义体: { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]

Depends on / 依赖: s.toAddSubgroup.subtype, s.toSubmonoid.subtype, subtype, toAddSubgroup, toSubmonoid
-/
def subtype (s : Subfield K) : s ->+* K :=
  { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: {s : Subfield K} (x : s)
  proof: rfl

中文:
引理 subtype_apply
  条件: {s : Subfield K} (x : s)
  证明: rfl
-/
lemma subtype_apply {s : Subfield K} (x : s) :
    s.subtype x = x := rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  given: (s : Subfield K)
  proof: Subtype.coe_injective

@[simp]

中文:
引理 subtype_injective
  条件: (s : Subfield K)
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective (s : Subfield K) :
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: ⇑(s.subtype) = ((↑) : s -> K)
  proof: rfl

中文:
定理 coe_subtype
  结论: ⇑(s.subtype) = ((↑) : s -> K)
  证明: rfl
-/
theorem coe_subtype : ⇑(s.subtype) = ((↑) : s -> K) :=
  rfl

variable (K) in
/--
theorem `toSubring_subtype_eq_subtype` / 定理 `toSubring_subtype_eq_subtype`

English:
theorem toSubring_subtype_eq_subtype
  given: (S : Subfield K)
  proof: rfl

中文:
定理 toSubring_subtype_eq_subtype
  条件: (S : Subfield K)
  证明: rfl
-/
theorem toSubring_subtype_eq_subtype (S : Subfield K) :
    S.toSubring.subtype = S.subtype :=
  rfl



/--
theorem `mem_toSubmonoid` / 定理 `mem_toSubmonoid`

English:
theorem mem_toSubmonoid
  given: {s : Subfield K} {x : K}
  statement: x in s.toSubmonoid ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toSubmonoid
  条件: {s : Subfield K} {x : K}
  结论: x in s.toSubmonoid ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubmonoid {s : Subfield K} {x : K} : x in s.toSubmonoid ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `coe_toSubmonoid` / 定理 `coe_toSubmonoid`

English:
theorem coe_toSubmonoid
  statement: (s.toSubmonoid : Set K) = s
  proof: rfl

中文:
定理 coe_toSubmonoid
  结论: (s.toSubmonoid : Set K) = s
  证明: rfl
-/
theorem coe_toSubmonoid : (s.toSubmonoid : Set K) = s :=
  rfl

/--
theorem `mem_toAddSubgroup` / 定理 `mem_toAddSubgroup`

English:
theorem mem_toAddSubgroup
  given: {s : Subfield K} {x : K}
  statement: x in s.toAddSubgroup ↔ x in s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toAddSubgroup
  条件: {s : Subfield K} {x : K}
  结论: x in s.toAddSubgroup ↔ x in s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toAddSubgroup {s : Subfield K} {x : K} : x in s.toAddSubgroup ↔ x in s :=
  Iff.rfl

@[simp]
/--
theorem `coe_toAddSubgroup` / 定理 `coe_toAddSubgroup`

English:
theorem coe_toAddSubgroup
  statement: (s.toAddSubgroup : Set K) = s
  proof: rfl

中文:
定理 coe_toAddSubgroup
  结论: (s.toAddSubgroup : Set K) = s
  证明: rfl
-/
theorem coe_toAddSubgroup : (s.toAddSubgroup : Set K) = s :=
  rfl

end Subfield
