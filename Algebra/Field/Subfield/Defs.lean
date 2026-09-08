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

/-- `SubfieldClass S K` states `S` is a type of subsets `s ⊆ K` closed under field operations. -/
/-
**SubfieldClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_1) → (K : Type u_2) → [DivisionRing K] → [SetLike S K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SubfieldClass S K` states `S` is a type of subsets `s ⊆ K` closed under field o
perations.
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
/-
**SubfieldClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubfieldClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subfield contains `1`, products and inverses.

Be assured that we're not actually proving that subfields are subgroups:
`SubgroupClass` is really an abbreviation of `SubgroupWithOrWithoutZeroClass`.
-/
instance (priority := 100) toSubgroupClass : SubgroupClass S K :=
  { h with }

variable {S} {x : K}

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**SubfieldClass.nnratCast_mem** 是 Mathlib 中的一个引理，位于命名空间 `SubfieldClass`。
形式化陈述：nnratCast_mem (s : S) (q : Rat>=0) : (q : K) in s
参数：s : S；q : Rat>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `div_mem`：div_mem {x y : M} (hx : x in H) (hy : y in H) : x / y in H
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `natCast_mem`：natCast_mem [AddSubmonoidWithOneClass S R] (n : Nat) : (n :
 R) in s
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
-/
lemma nnratCast_mem (s : S) (q : ℚ≥0) : (q : K) ∈ s := by
  simpa only [NNRat.cast_def] using div_mem (natCast_mem s q.num) (natCast_mem s q.den)

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**SubfieldClass.ratCast_mem** 是 Mathlib 中的一个引理，位于命名空间 `SubfieldClass`。
形式化陈述：ratCast_mem (s : S) (q : Rat) : (q : K) in s
参数：s : S；q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `div_mem`：div_mem {x y : M} (hx : x in H) (hy : y in H) : x / y in H
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `intCast_mem`：intCast_mem (n : Int) : (n : R) in s
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `natCast_mem`：natCast_mem [AddSubmonoidWithOneClass S R] (n : Nat) : (n :
 R) in s
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
-/
lemma ratCast_mem (s : S) (q : ℚ) : (q : K) ∈ s := by
  simpa only [Rat.cast_def] using div_mem (intCast_mem s q.num) (natCast_mem s q.den)
/-
**SubfieldClass.instNNRatCast** 是 Mathlib 中的一个实例，位于命名空间 `SubfieldClass`。
形式化陈述：instNNRatCast (s : S) : NNRatCast s where nnratCast q
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SubfieldClass.nnratCast_mem`：nnratCast_mem (s : S) (q : Rat>=0) : (q : K
) in s
-/
instance instNNRatCast (s : S) : NNRatCast s where nnratCast q := ⟨q, nnratCast_mem s q⟩
/-
**SubfieldClass.instRatCast** 是 Mathlib 中的一个实例，位于命名空间 `SubfieldClass`。
形式化陈述：instRatCast (s : S) : RatCast s where ratCast q
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SubfieldClass.ratCast_mem`：ratCast_mem (s : S) (q : Rat) : (q : K) in s
-/
instance instRatCast (s : S) : RatCast s where ratCast q := ⟨q, ratCast_mem s q⟩
/-
**SubfieldClass.coe_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `SubfieldClass`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] {S : Type u_1} [inst_1 : SetLike S 
K] [h : SubfieldClass S K] (s : S) (q : ℚ≥0),   ↑↑q = ↑q
参数：s : S；q : ℚ≥0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_nnratCast (s : S) (q : ℚ≥0) : ((q : s) : K) = q := rfl
/-
**SubfieldClass.coe_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `SubfieldClass`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] {S : Type u_1} [inst_1 : SetLike S 
K] [h : SubfieldClass S K] (s : S) (x : ℚ),   ↑↑x = ↑x
参数：s : S；x : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_ratCast (s : S) (x : ℚ) : ((x : s) : K) = x := rfl

@[aesop 90% (rule_sets := [SetLike])]
/-
**SubfieldClass.nnqsmul_mem** 是 Mathlib 中的一个引理，位于命名空间 `SubfieldClass`。
形式化陈述：nnqsmul_mem (s : S) (q : Rat>=0) (hx : x in s) : q • x in s
参数：s : S；q : Rat>=0；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.smul_def`：smul_def (q : Rat>=0) (a : K) : q • a = q * a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用引理 `SubfieldClass.nnratCast_mem`：nnratCast_mem (s : S) (q : Rat>=0) : (q : K
) in s
-/
lemma nnqsmul_mem (s : S) (q : ℚ≥0) (hx : x ∈ s) : q • x ∈ s := by
  simpa only [NNRat.smul_def] using mul_mem (nnratCast_mem _ _) hx

@[aesop 90% (rule_sets := [SetLike])]
/-
**SubfieldClass.qsmul_mem** 是 Mathlib 中的一个引理，位于命名空间 `SubfieldClass`。
形式化陈述：qsmul_mem (s : S) (q : Rat) (hx : x in s) : q • x in s
参数：s : S；q : Rat；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.smul_def`：smul_def (a : Rat) (x : K) : a • x = ↑a * x
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用引理 `SubfieldClass.ratCast_mem`：ratCast_mem (s : S) (q : Rat) : (q : K) in s
-/
lemma qsmul_mem (s : S) (q : ℚ) (hx : x ∈ s) : q • x ∈ s := by
  simpa only [Rat.smul_def] using mul_mem (ratCast_mem _ _) hx

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**SubfieldClass.ofScientific_mem** 是 Mathlib 中的一个引理，位于命名空间 `SubfieldClass`。
形式化陈述：ofScientific_mem (s : S) {b : Bool} {n m : Nat} : (OfScientific.ofScientif
ic n b m : K) in s
参数：s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SubfieldClass.nnratCast_mem`：nnratCast_mem (s : S) (q : Rat>=0) : (q : K
) in s
-/
lemma ofScientific_mem (s : S) {b : Bool} {n m : ℕ} :
    (OfScientific.ofScientific n b m : K) ∈ s :=
  SubfieldClass.nnratCast_mem s (OfScientific.ofScientific n b m)
/-
**SubfieldClass.instSMulNNRat** 是 Mathlib 中的一个实例，位于命名空间 `SubfieldClass`。
形式化陈述：instSMulNNRat (s : S) : SMul Rat>=0 s where smul q x
参数：s : S。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulNNRat (s : S) : SMul ℚ≥0 s where smul q x := ⟨q • x, nnqsmul_mem s q x.2⟩
/-
**SubfieldClass.instSMulRat** 是 Mathlib 中的一个实例，位于命名空间 `SubfieldClass`。
形式化陈述：instSMulRat (s : S) : SMul Rat s where smul q x
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulRat (s : S) : SMul ℚ s where smul q x := ⟨q • x, qsmul_mem s q x.2⟩
/-
**SubfieldClass.coe_nnqsmul** 是 Mathlib 中的一个定理，位于命名空间 `SubfieldClass`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] {S : Type u_1} [inst_1 : SetLike S 
K] [h : SubfieldClass S K] (s : S) (q : ℚ≥0)   (x : ↥s), ↑(q • x) = q • ↑x
参数：s : S；q : ℚ≥0；x : ↥s；q • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_nnqsmul (s : S) (q : ℚ≥0) (x : s) : ↑(q • x) = q • (x : K) := rfl
/-
**SubfieldClass.coe_qsmul** 是 Mathlib 中的一个定理，位于命名空间 `SubfieldClass`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] {S : Type u_1} [inst_1 : SetLike S 
K] [h : SubfieldClass S K] (s : S) (q : ℚ)   (x : ↥s), ↑(q • x) = q • ↑x
参数：s : S；q : ℚ；x : ↥s；q • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_qsmul (s : S) (q : ℚ) (x : s) : ↑(q • x) = q • (x : K) := rfl

/-- A subfield inherits a division ring structure -/
/-
**SubfieldClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubfieldClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subfield inherits a division ring structure
-/
instance (priority := 75) toDivisionRing (s : S) : DivisionRing s := fast_instance%
  Subtype.coe_injective.divisionRing ((↑) : s → K)
    rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (coe_nnqsmul _) (coe_qsmul _) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

-- Prefer subclasses of `Field` over subclasses of `SubfieldClass`.
/-- A subfield of a field inherits a field structure -/
/-
**SubfieldClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubfieldClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subfield of a field inherits a field structure
-/
instance (priority := 75) toField {K} [Field K] [SetLike S K] [SubfieldClass S K] (s : S) :
    Field s := fast_instance%
  Subtype.coe_injective.field ((↑) : s → K)
    rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (coe_nnqsmul _) (coe_qsmul _) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

end SubfieldClass

/-- `Subfield R` is the type of subfields of `R`. A subfield of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
@[stacks 09FD "second part"]
/-
**Subfield** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u) → [DivisionRing K] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subfield R` is the type of subfields of `R`. A subfield of `R` is a subset `s` 
that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it 
shares the
  same 0 and 1 as R.
-/
structure Subfield (K : Type u) [DivisionRing K] extends Subring K where
  /-- A subfield is closed under multiplicative inverses. -/
  inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier

/-- Reinterpret a `Subfield` as a `Subring`. -/
add_decl_doc Subfield.toSubring

namespace Subfield

/-- The underlying `AddSubgroup` of a subfield. -/
@[reducible]
/-
**Subfield.toAddSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：toAddSubgroup (s : Subfield K) : AddSubgroup K
参数：s : Subfield K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying `AddSubgroup` of a subfield.
-/
def toAddSubgroup (s : Subfield K) : AddSubgroup K :=
  { s.toSubring.toAddSubgroup with }
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Subfield K) K where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Subfield K) := .ofSetLike (Subfield K) K
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubfieldClass (Subfield K) K where
  add_mem {s} := s.add_mem'
  zero_mem s := s.zero_mem'
  neg_mem {s} := s.neg_mem'
  mul_mem {s} := s.mul_mem'
  one_mem s := s.one_mem'
  inv_mem {s} := s.inv_mem' _
/-
**Subfield.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_carrier {s : Subfield K} {x : K} : x in s.carrier ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : Subfield K} {x : K} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**Subfield.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_mk {S : Subring K} {x : K} (h) : x in (⟨S, h⟩ : Subfield K) ↔ x in S
参数：h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {S : Subring K} {x : K} (h) : x ∈ (⟨S, h⟩ : Subfield K) ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**Subfield.coe_set_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_set_mk (S : Subring K) (h) : ((⟨S, h⟩ : Subfield K) : Set K) = S
参数：S : Subring K；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_set_mk (S : Subring K) (h) : ((⟨S, h⟩ : Subfield K) : Set K) = S :=
  rfl

@[simp]
/-
**Subfield.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mk_le_mk {S S' : Subring K} (h h') : (⟨S, h⟩ : Subfield K) <= (⟨S', h'⟩ : 
Subfield K) ↔ S <= S'
参数：h h'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk {S S' : Subring K} (h h') : (⟨S, h⟩ : Subfield K) ≤ (⟨S', h'⟩ : Subfield K) ↔
    S ≤ S' :=
  Iff.rfl

/-- Two subfields are equal if they have the same elements. -/
@[ext]
/-
**Subfield.ext** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：ext {S T : Subfield K} (h : forall x, x in S ↔ x in T) : S = T
参数：h : forall x, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two subfields are equal if they have the same elements.
-/
theorem ext {S T : Subfield K} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subfield with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
/-
**Subfield.copy** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：{K : Type u} → [inst : DivisionRing K] → (S : Subfield K) → (s : Set K) → 
s = ↑S → Subfield K
参数：S : Subfield K；s : Set K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a subfield with a new `carrier` equal to the old one. Useful to fix defi
nitional
equalities.
-/
protected def copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : Subfield K :=
  { S.toSubring.copy s hs with
    carrier := s
    inv_mem' := hs.symm ▸ S.inv_mem' }

@[simp, norm_cast]
/-
**Subfield.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : (S.copy s hs : Set K
) = s
参数：S : Subfield K；s : Set K；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : (S.copy s hs : Set K) = s :=
  rfl
/-
**Subfield.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：copy_eq (S : Subfield K) (s : Set K) (hs : s = ↑S) : S.copy s hs = S
参数：S : Subfield K；s : Set K；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : Subfield K) (s : Set K) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

@[simp]
/-
**Subfield.coe_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_toSubring (s : Subfield K) : (s.toSubring : Set K) = s
参数：s : Subfield K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubring (s : Subfield K) : (s.toSubring : Set K) = s :=
  rfl

@[simp]
/-
**Subfield.mem_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_toSubring (s : Subfield K) (x : K) : x in s.toSubring ↔ x in s
参数：s : Subfield K；x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubring (s : Subfield K) (x : K) : x ∈ s.toSubring ↔ x ∈ s :=
  Iff.rfl

end Subfield

/-- A `Subring` containing inverses is a `Subfield`. -/
/-
**Subring.toSubfield** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subring.toSubfield (s : Subring K) (hinv : forall x in s, x⁻¹ in s) : Subf
ield K
参数：s : Subring K；hinv : forall x in s, x⁻¹ in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Subring` containing inverses is a `Subfield`.
-/
def Subring.toSubfield (s : Subring K) (hinv : ∀ x ∈ s, x⁻¹ ∈ s) : Subfield K :=
  { s with inv_mem' := hinv }

namespace Subfield

variable (s t : Subfield K)

section DerivedFromSubfieldClass

/-- A subfield contains the field's 1. -/
/-
**Subfield.one_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K), 1 ∈ s
参数：s : Subfield K。
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
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
A subfield contains the field's 1.
-/
protected theorem one_mem : (1 : K) ∈ s :=
  one_mem s

/-- A subfield contains the field's 0. -/
/-
**Subfield.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K), 0 ∈ s
参数：s : Subfield K。
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
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
A subfield contains the field's 0.
-/
protected theorem zero_mem : (0 : K) ∈ s :=
  zero_mem s

/-- A subfield is closed under multiplication. -/
/-
**Subfield.mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {x y : K}, x ∈ s →
 y ∈ s → x * y ∈ s
参数：s : Subfield K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
A subfield is closed under multiplication.
-/
protected theorem mul_mem {x y : K} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A subfield is closed under addition. -/
/-
**Subfield.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {x y : K}, x ∈ s →
 y ∈ s → x + y ∈ s
参数：s : Subfield K。
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
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
A subfield is closed under addition.
-/
protected theorem add_mem {x y : K} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A subfield is closed under negation. -/
/-
**Subfield.neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {x : K}, x ∈ s → -
x ∈ s
参数：s : Subfield K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
A subfield is closed under negation.
-/
protected theorem neg_mem {x : K} : x ∈ s → -x ∈ s :=
  neg_mem

/-- A subfield is closed under subtraction. -/
/-
**Subfield.sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {x y : K}, x ∈ s →
 y ∈ s → x - y ∈ s
参数：s : Subfield K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
A subfield is closed under subtraction.
-/
protected theorem sub_mem {x y : K} : x ∈ s → y ∈ s → x - y ∈ s :=
  sub_mem

/-- A subfield is closed under inverses. -/
/-
**Subfield.inv_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {x : K}, x ∈ s → x
⁻¹ ∈ s
参数：s : Subfield K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubfieldClass.toInvMemClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Div
isionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   InvMemClass S 
K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
A subfield is closed under inverses.
-/
protected theorem inv_mem {x : K} : x ∈ s → x⁻¹ ∈ s :=
  inv_mem

/-- A subfield is closed under division. -/
/-
**Subfield.div_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {x y : K}, x ∈ s →
 y ∈ s → x / y ∈ s
参数：s : Subfield K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_mem`：div_mem {x y : M} (hx : x in H) (hy : y in H) : x / y in H
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
A subfield is closed under division.
-/
protected theorem div_mem {x y : K} : x ∈ s → y ∈ s → x / y ∈ s :=
  div_mem
/-
**Subfield.pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {x : K}, x ∈ s → ∀
 (n : ℕ), x ^ n ∈ s
参数：s : Subfield K；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
protected theorem pow_mem {x : K} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n
/-
**Subfield.zsmul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {x : K}, x ∈ s → ∀
 (n : ℤ), n • x ∈ s
参数：s : Subfield K；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zsmul_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst
_1 : SetLike S M] [hSM : AddSubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n …
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
protected theorem zsmul_mem {x : K} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n
/-
**Subfield.intCast_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) (n : ℤ), ↑n ∈ s
参数：s : Subfield K；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intCast_mem`：intCast_mem (n : Int) : (n : R) in s
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
protected theorem intCast_mem (n : ℤ) : (n : K) ∈ s := intCast_mem s n
/-
**Subfield.zpow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {x : K}, x ∈ s → ∀
 (n : ℤ), x ^ n ∈ s
参数：s : Subfield K；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zpow_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : DivInvMonoid M] [inst_
1 : SetLike S M] [hSM : SubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n : ℤ…
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
protected theorem zpow_mem {x : K} (hx : x ∈ s) (n : ℤ) : x ^ n ∈ s := zpow_mem hx n
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ring s :=
  s.toSubring.toRing
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div s :=
  ⟨fun x y => ⟨x / y, s.div_mem x.2 y.2⟩⟩
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv s :=
  ⟨fun x => ⟨x⁻¹, s.inv_mem x.2⟩⟩
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow s ℤ :=
  ⟨fun x z => ⟨x ^ z, s.zpow_mem x.2 z⟩⟩
/-
**Subfield.toDivisionRing** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
形式化陈述：toDivisionRing (s : Subfield K) : DivisionRing s
参数：s : Subfield K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
instance toDivisionRing (s : Subfield K) : DivisionRing s := SubfieldClass.toDivisionRing s
/-
**Subfield.toField** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
形式化陈述：toField {K} [Field K] (s : Subfield K) : Field s
参数：s : Subfield K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toField {K} [Field K] (s : Subfield K) : Field s := SubfieldClass.toField s

@[simp, norm_cast]
/-
**Subfield.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_add (x y : s) : (↑(x + y) : K) = ↑x + ↑y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (x y : s) : (↑(x + y) : K) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
/-
**Subfield.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_sub (x y : s) : (↑(x - y) : K) = ↑x - ↑y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
theorem coe_sub (x y : s) : (↑(x - y) : K) = ↑x - ↑y :=
  rfl

@[simp, norm_cast]
/-
**Subfield.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_neg (x : s) : (↑(-x) : K) = -↑x
参数：x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
theorem coe_neg (x : s) : (↑(-x) : K) = -↑x :=
  rfl

@[simp, norm_cast]
/-
**Subfield.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_mul (x y : s) : (↑(x * y) : K) = ↑x * ↑y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : s) : (↑(x * y) : K) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
/-
**Subfield.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_div (x y : s) : (↑(x / y) : K) = ↑x / ↑y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div (x y : s) : (↑(x / y) : K) = ↑x / ↑y :=
  rfl

@[simp, norm_cast]
/-
**Subfield.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_inv (x : s) : (↑x⁻¹ : K) = (↑x)⁻¹
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv (x : s) : (↑x⁻¹ : K) = (↑x)⁻¹ :=
  rfl

@[simp, norm_cast]
/-
**Subfield.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_zero : ((0 : s) : K) = 0
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
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
theorem coe_zero : ((0 : s) : K) = 0 :=
  rfl

@[simp, norm_cast]
/-
**Subfield.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_one : ((1 : s) : K) = 1
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
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
theorem coe_one : ((1 : s) : K) = 1 :=
  rfl

end DerivedFromSubfieldClass

/-- The embedding from a subfield of the field `K` to `K`. -/
/-
**Subfield.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：subtype (s : Subfield K) : s ->+* K
参数：s : Subfield K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from a subfield of the field `K` to `K`.
-/
def subtype (s : Subfield K) : s →+* K :=
  { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]
/-
**Subfield.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `Subfield`。
形式化陈述：subtype_apply {s : Subfield K} (x : s) : s.subtype x = x
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply {s : Subfield K} (x : s) :
    s.subtype x = x := rfl
/-
**Subfield.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `Subfield`。
形式化陈述：subtype_injective (s : Subfield K) : Function.Injective s.subtype
参数：s : Subfield K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective (s : Subfield K) :
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[simp]
/-
**Subfield.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_subtype : ⇑(s.subtype) = ((↑) : s -> K)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : ⇑(s.subtype) = ((↑) : s → K) :=
  rfl

variable (K) in
/-
**Subfield.toSubring_subtype_eq_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：toSubring_subtype_eq_subtype (S : Subfield K) : S.toSubring.subtype = S.su
btype
参数：S : Subfield K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem toSubring_subtype_eq_subtype (S : Subfield K) :
    S.toSubring.subtype = S.subtype :=
  rfl

/-! ### Partial order -/


/-
**Subfield.mem_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_toSubmonoid {s : Subfield K} {x : K} : x in s.toSubmonoid ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Partial order
-/
theorem mem_toSubmonoid {s : Subfield K} {x : K} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**Subfield.coe_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_toSubmonoid : (s.toSubmonoid : Set K) = s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubmonoid : (s.toSubmonoid : Set K) = s :=
  rfl
/-
**Subfield.mem_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_toAddSubgroup {s : Subfield K} {x : K} : x in s.toAddSubgroup ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toAddSubgroup {s : Subfield K} {x : K} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**Subfield.coe_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_toAddSubgroup : (s.toAddSubgroup : Set K) = s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAddSubgroup : (s.toAddSubgroup : Set K) = s :=
  rfl

end Subfield

