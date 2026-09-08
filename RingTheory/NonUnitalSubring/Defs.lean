/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.RingTheory.NonUnitalSubsemiring.Defs
public import Mathlib.Tactic.FastInstance

/-!
# `NonUnitalSubring`s

Let `R` be a non-unital ring. This file defines the "bundled" non-unital subring type
`NonUnitalSubring R`, a type whose terms correspond to non-unital subrings of `R`.
This is the preferred way to talk about non-unital subrings in mathlib.

## Main definitions

Notation used here:

`(R : Type u) [NonUnitalRing R] (S : Type u) [NonUnitalRing S] (f g : R →ₙ+* S)`
`(A : NonUnitalSubring R) (B : NonUnitalSubring S) (s : Set R)`

* `NonUnitalSubring R` : the type of non-unital subrings of a ring `R`.

## Implementation notes

A non-unital subring is implemented as a `NonUnitalSubsemiring` which is also an
additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a non-unital subring's underlying set.

## Tags
non-unital subring
-/

@[expose] public section

assert_not_exists RelIso

universe u v w

section Basic

variable {R : Type u} {S : Type v} [NonUnitalNonAssocRing R]

section NonUnitalSubringClass

/-- `NonUnitalSubringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup. -/
/-
**NonUnitalSubringClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_1) → (R : Type u) → [NonUnitalNonAssocRing R] → [SetLike S R] 
→ Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalSubringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup.
-/
class NonUnitalSubringClass (S : Type*) (R : Type u) [NonUnitalNonAssocRing R] [SetLike S R] : Prop
  extends NonUnitalSubsemiringClass S R, NegMemClass S R where

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NonUnitalSubringClass.addSubgroupClass (S : Type*) (R : Type u)
    [SetLike S R] [NonUnitalNonAssocRing R] [h : NonUnitalSubringClass S R] :
    AddSubgroupClass S R :=
  { h with }

variable [SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S)

namespace NonUnitalSubringClass

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
/-
**NonUnitalSubringClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subring of a non-unital ring inherits a non-unital ring structure
-/
instance (priority := 75) toNonUnitalNonAssocRing : NonUnitalNonAssocRing s := fast_instance%
  Subtype.val_injective.nonUnitalNonAssocRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
/-
**NonUnitalSubringClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subring of a non-unital ring inherits a non-unital ring structure
-/
instance (priority := 75) toNonUnitalRing {R : Type*} [NonUnitalRing R] [SetLike S R]
    [NonUnitalSubringClass S R] (s : S) : NonUnitalRing s := fast_instance%
  Subtype.val_injective.nonUnitalRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a `NonUnitalNonAssocCommRing` is a `NonUnitalNonAssocCommRing`. -/
/-
**NonUnitalSubringClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subring of a `NonUnitalNonAssocCommRing` is a `NonUnitalNonAssocCom
mRing`.
-/
instance (priority := 75) toNonUnitalNonAssocCommRing {R} [NonUnitalNonAssocCommRing R]
    [SetLike S R] [NonUnitalSubringClass S R] (s : S) :
    NonUnitalNonAssocCommRing s := fast_instance%
  Subtype.val_injective.nonUnitalNonAssocCommRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `NonUnitalRing` over subclasses of `NonUnitalSubringClass`.
/-- A non-unital subring of a `NonUnitalCommRing` is a `NonUnitalCommRing`. -/
/-
**NonUnitalSubringClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subring of a `NonUnitalCommRing` is a `NonUnitalCommRing`.
-/
instance (priority := 75) toNonUnitalCommRing {R} [NonUnitalCommRing R] [SetLike S R]
    [NonUnitalSubringClass S R] : NonUnitalCommRing s := fast_instance%
  Subtype.val_injective.nonUnitalCommRing _ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-- The natural non-unital ring hom from a non-unital subring of a non-unital ring `R` to `R`. -/
/-
**NonUnitalSubringClass.subtype** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubringClass
`。
形式化陈述：subtype (s : S) : s ->ₙ+* R
参数：s : S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [i
nst : SetLike S R] [inst_1 : NonUnitalNonAssocRing R] [h : NonUnitalSubringClass
 S R],   AddSubgroupClass S …

--- 原说明 ---
The natural non-unital ring hom from a non-unital subring of a non-unital ring `
R` to `R`.
-/
def subtype (s : S) : s →ₙ+* R :=
  { NonUnitalSubsemiringClass.subtype s,
    AddSubgroupClass.subtype s with
    toFun := Subtype.val }

variable {s} in
@[simp]
/-
**NonUnitalSubringClass.subtype_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubrin
gClass`。
形式化陈述：subtype_apply (x : s) : subtype s x = x
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_apply (x : s) : subtype s x = x :=
  rfl
/-
**NonUnitalSubringClass.subtype_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bringClass`。
形式化陈述：subtype_injective : Function.Injective (subtype s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem subtype_injective : Function.Injective (subtype s) :=
  Subtype.coe_injective

@[simp]
/-
**NonUnitalSubringClass.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubringC
lass`。
形式化陈述：coe_subtype : (subtype s : s -> R) = Subtype.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : (subtype s : s → R) = Subtype.val :=
  rfl

end NonUnitalSubringClass

end NonUnitalSubringClass

/-- `NonUnitalSubring R` is the type of non-unital subrings of `R`. A non-unital subring of `R`
is a subset `s` that is a multiplicative subsemigroup and an additive subgroup. Note in particular
that it shares the same 0 as R. -/
/-
**NonUnitalSubring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [NonUnitalNonAssocRing R] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalSubring R` is the type of non-unital subrings of `R`. A non-unital sub
ring of `R`
is a subset `s` that is a multiplicative subsemigroup and an additive subgroup. 
Note in particular
that it shares the same 0 as R.
-/
structure NonUnitalSubring (R : Type u) [NonUnitalNonAssocRing R] extends
  NonUnitalSubsemiring R, AddSubgroup R

/-- Reinterpret a `NonUnitalSubring` as a `NonUnitalSubsemiring`. -/
add_decl_doc NonUnitalSubring.toNonUnitalSubsemiring

/-- Reinterpret a `NonUnitalSubring` as an `AddSubgroup`. -/
add_decl_doc NonUnitalSubring.toAddSubgroup

namespace NonUnitalSubring

/-- The underlying submonoid of a `NonUnitalSubring`. -/
@[reducible]
/-
**NonUnitalSubring.toSubsemigroup** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：toSubsemigroup (s : NonUnitalSubring R) : Subsemigroup R
参数：s : NonUnitalSubring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying submonoid of a `NonUnitalSubring`.
-/
def toSubsemigroup (s : NonUnitalSubring R) : Subsemigroup R :=
  { s.toNonUnitalSubsemiring.toSubsemigroup with carrier := s.carrier }
/-
**NonUnitalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (NonUnitalSubring R) R where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h
/-
**NonUnitalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (NonUnitalSubring R) := .ofSetLike (NonUnitalSubring R) R

/-- The actual `NonUnitalSubring` obtained from an element of a `NonUnitalSubringClass`. -/
@[simps]
/-
**NonUnitalSubring.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：ofClass {S R : Type*} [NonUnitalNonAssocRing R] [SetLike S R] [NonUnitalSu
bringClass S R] (s : S) : NonUnitalSubring R where carrier
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The actual `NonUnitalSubring` obtained from an element of a `NonUnitalSubringCla
ss`.
-/
def ofClass {S R : Type*} [NonUnitalNonAssocRing R] [SetLike S R] [NonUnitalSubringClass S R]
    (s : S) : NonUnitalSubring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  neg_mem' := neg_mem
/-
**NonUnitalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set R) (NonUnitalSubring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧
      (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧ ∀ {x}, x ∈ s → -x ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        mul_mem' := h.2.2.1
        neg_mem' := h.2.2.2 },
      rfl ⟩
/-
**NonUnitalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonUnitalSubringClass (NonUnitalSubring R) R where
  zero_mem s := s.zero_mem'
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  neg_mem {s} := s.neg_mem'
/-
**NonUnitalSubring.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_carrier {s : NonUnitalSubring R} {x : R} : x in s.toNonUnitalSubsemiri
ng ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : NonUnitalSubring R} {x : R} : x ∈ s.toNonUnitalSubsemiring ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubring.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_mk {S : NonUnitalSubsemiring R} {x : R} (h) : x in (⟨S, h⟩ : NonUnital
Subring R) ↔ x in S
参数：h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {S : NonUnitalSubsemiring R} {x : R} (h) :
    x ∈ (⟨S, h⟩ : NonUnitalSubring R) ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubring.coe_set_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_set_mk (S : NonUnitalSubsemiring R) (h) : ((⟨S, h⟩ : NonUnitalSubring 
R) : Set R) = S
参数：S : NonUnitalSubsemiring R；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_set_mk (S : NonUnitalSubsemiring R) (h) :
    ((⟨S, h⟩ : NonUnitalSubring R) : Set R) = S :=
  rfl

@[simp]
/-
**NonUnitalSubring.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mk_le_mk {S S' : NonUnitalSubsemiring R} (h h') : (⟨S, h⟩ : NonUnitalSubri
ng R) <= (⟨S', h'⟩ : NonUnitalSubring R) ↔ S <= S'
参数：h h'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk {S S' : NonUnitalSubsemiring R} (h h') :
    (⟨S, h⟩ : NonUnitalSubring R) ≤ (⟨S', h'⟩ : NonUnitalSubring R) ↔ S ≤ S' :=
  Iff.rfl

/-- Two non-unital subrings are equal if they have the same elements. -/
@[ext]
/-
**NonUnitalSubring.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：ext {S T : NonUnitalSubring R} (h : forall x, x in S ↔ x in T) : S = T
参数：h : forall x, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two non-unital subrings are equal if they have the same elements.
-/
theorem ext {S T : NonUnitalSubring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a non-unital subring with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
/-
**NonUnitalSubring.copy** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：{R : Type u} → [inst : NonUnitalNonAssocRing R] → (S : NonUnitalSubring R)
 → (s : Set R) → s = ↑S → NonUnitalSubring R
参数：S : NonUnitalSubring R；s : Set R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a non-unital subring with a new `carrier` equal to the old one. Useful t
o fix
definitional equalities.
-/
protected def copy (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : NonUnitalSubring R :=
  { S.toNonUnitalSubsemiring.copy s hs with
    carrier := s
    neg_mem' := hs.symm ▸ S.neg_mem' }

@[simp]
/-
**NonUnitalSubring.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_copy (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs
 : Set R) = s
参数：S : NonUnitalSubring R；s : Set R；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl
/-
**NonUnitalSubring.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：copy_eq (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : S.copy s hs =
 S
参数：S : NonUnitalSubring R；s : Set R；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : NonUnitalSubring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
/-
**NonUnitalSubring.toNonUnitalSubsemiring_injective** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalSubring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R], Function.Injective NonUni
talSubring.toNonUnitalSubsemiring
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.ext`：ext {S T : NonUnitalSubring R} (h : forall x, x in
 S ↔ x in T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem toNonUnitalSubsemiring_injective :
    Function.Injective (toNonUnitalSubsemiring : NonUnitalSubring R → NonUnitalSubsemiring R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h :)

@[gcongr, mono]
/-
**NonUnitalSubring.toNonUnitalSubsemiring_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `
NonUnitalSubring`。
形式化陈述：toNonUnitalSubsemiring_strictMono : StrictMono (toNonUnitalSubsemiring : N
onUnitalSubring R -> NonUnitalSubsemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonUnitalSubsemiring_strictMono :
    StrictMono (toNonUnitalSubsemiring : NonUnitalSubring R → NonUnitalSubsemiring R) := fun _ _ =>
  id

@[gcongr, mono]
/-
**NonUnitalSubring.toNonUnitalSubsemiring_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talSubring`。
形式化陈述：toNonUnitalSubsemiring_mono : Monotone (toNonUnitalSubsemiring : NonUnital
Subring R -> NonUnitalSubsemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `NonUnitalSubring.toNonUnitalSubsemiring_strictMono`：toNonUnitalSubsemiri
ng_strictMono : StrictMono (toNonUnitalSubsemiring : NonUnitalSubring R -> NonUn
italSubsemiring R)
-/
theorem toNonUnitalSubsemiring_mono :
    Monotone (toNonUnitalSubsemiring : NonUnitalSubring R → NonUnitalSubsemiring R) :=
  toNonUnitalSubsemiring_strictMono.monotone
/-
**NonUnitalSubring.toAddSubgroup_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
ubring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R], Function.Injective NonUni
talSubring.toAddSubgroup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.ext`：ext {S T : NonUnitalSubring R} (h : forall x, x in
 S ↔ x in T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem toAddSubgroup_injective :
    Function.Injective (toAddSubgroup : NonUnitalSubring R → AddSubgroup R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h :)

@[gcongr, mono]
/-
**NonUnitalSubring.toAddSubgroup_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
Subring`。
形式化陈述：toAddSubgroup_strictMono : StrictMono (toAddSubgroup : NonUnitalSubring R 
-> AddSubgroup R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddSubgroup_strictMono :
    StrictMono (toAddSubgroup : NonUnitalSubring R → AddSubgroup R) := fun _ _ => id

@[gcongr, mono]
/-
**NonUnitalSubring.toAddSubgroup_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubrin
g`。
形式化陈述：toAddSubgroup_mono : Monotone (toAddSubgroup : NonUnitalSubring R -> AddSu
bgroup R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `NonUnitalSubring.toAddSubgroup_strictMono`：toAddSubgroup_strictMono : St
rictMono (toAddSubgroup : NonUnitalSubring R -> AddSubgroup R)
-/
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : NonUnitalSubring R → AddSubgroup R) :=
  toAddSubgroup_strictMono.monotone
/-
**NonUnitalSubring.toSubsemigroup_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
Subring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R], Function.Injective NonUni
talSubring.toSubsemigroup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.ext`：ext {S T : NonUnitalSubring R} (h : forall x, x in
 S ↔ x in T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem toSubsemigroup_injective :
    Function.Injective (toSubsemigroup : NonUnitalSubring R → Subsemigroup R)
  | _r, _s, h => ext (SetLike.ext_iff.mp h :)

@[gcongr, mono]
/-
**NonUnitalSubring.toSubsemigroup_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lSubring`。
形式化陈述：toSubsemigroup_strictMono : StrictMono (toSubsemigroup : NonUnitalSubring 
R -> Subsemigroup R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubsemigroup_strictMono :
    StrictMono (toSubsemigroup : NonUnitalSubring R → Subsemigroup R) := fun _ _ => id

@[gcongr, mono]
/-
**NonUnitalSubring.toSubsemigroup_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubri
ng`。
形式化陈述：toSubsemigroup_mono : Monotone (toSubsemigroup : NonUnitalSubring R -> Sub
semigroup R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `NonUnitalSubring.toSubsemigroup_strictMono`：toSubsemigroup_strictMono : 
StrictMono (toSubsemigroup : NonUnitalSubring R -> Subsemigroup R)
-/
theorem toSubsemigroup_mono : Monotone (toSubsemigroup : NonUnitalSubring R → Subsemigroup R) :=
  toSubsemigroup_strictMono.monotone

/-- Construct a `NonUnitalSubring R` from a set `s`, a subsemigroup `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
/-
**NonUnitalSubring.mk'** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mk'_toSubsemigroup {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : 
AddSubgroup R} (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha).toSubsemigr
oup = sm
参数：hm : ↑sm = s；ha : ↑sa = s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `NonUnitalSubring R` from a set `s`, a subsemigroup `sm`, and an add
itive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`.
-/
protected def mk' (s : Set R) (sm : Subsemigroup R) (sa : AddSubgroup R) (hm : ↑sm = s)
    (ha : ↑sa = s) : NonUnitalSubring R :=
  { sm.copy s hm.symm, sa.copy s ha.symm with }

@[simp]
/-
**NonUnitalSubring.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_mk' {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup
 R} (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha : Set R) = s
参数：hm : ↑sm = s；ha : ↑sa = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.mk'`：mk'_toSubsemigroup {s : Set R} {sm : Subsemigroup 
R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s) : (NonUnitalSubring.mk' s 
sm sa hm h…
-/
theorem coe_mk' {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha : Set R) = s :=
  rfl

@[simp]
/-
**NonUnitalSubring.mem_mk'** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_mk' {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup
 R} (ha : ↑sa = s) {x : R} : x in NonUnitalSubring.mk' s sm sa hm ha ↔ x in s
参数：hm : ↑sm = s；ha : ↑sa = s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `NonUnitalSubring.mk'`：mk'_toSubsemigroup {s : Set R} {sm : Subsemigroup 
R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s) : (NonUnitalSubring.mk' s 
sm sa hm h…
-/
theorem mem_mk' {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
    {x : R} : x ∈ NonUnitalSubring.mk' s sm sa hm ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubring.mk'_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubrin
g`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R] {s : Set R} {sm : Subsemig
roup R} (hm : ↑sm = s) {sa : AddSubgroup R}   (ha : ↑sa = s), (NonUnitalSubring.
mk' s sm sa hm ha).toSubsemigroup = sm
参数：hm : ↑sm = s；ha : ↑sa = s；NonUnitalSubring.mk' s sm sa hm ha。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalSubring.mk'`：mk'_toSubsemigroup {s : Set R} {sm : Subsemigroup 
R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s) : (NonUnitalSubring.mk' s 
sm sa hm h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mk'_toSubsemigroup {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha).toSubsemigroup = sm :=
  SetLike.coe_injective hm.symm

@[simp]
/-
**NonUnitalSubring.mk'_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring
`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R] {s : Set R} {sm : Subsemig
roup R} (hm : ↑sm = s) {sa : AddSubgroup R}   (ha : ↑sa = s), (NonUnitalSubring.
mk' s sm sa hm ha).toAddSubgroup = sa
参数：hm : ↑sm = s；ha : ↑sa = s；NonUnitalSubring.mk' s sm sa hm ha。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalSubring.mk'`：mk'_toSubsemigroup {s : Set R} {sm : Subsemigroup 
R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s) : (NonUnitalSubring.mk' s 
sm sa hm h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mk'_toAddSubgroup {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (NonUnitalSubring.mk' s sm sa hm ha).toAddSubgroup = sa :=
  SetLike.coe_injective ha.symm

end NonUnitalSubring

namespace NonUnitalSubring

variable (s : NonUnitalSubring R)

/-- A non-unital subring contains the ring's 0. -/
/-
**NonUnitalSubring.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R] (s : NonUnitalSubring R), 
0 ∈ s
参数：s : NonUnitalSubring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
A non-unital subring contains the ring's 0.
-/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem _

/-- A non-unital subring is closed under multiplication. -/
/-
**NonUnitalSubring.mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R] (s : NonUnitalSubring R) {
x y : R}, x ∈ s → y ∈ s → x * y ∈ s
参数：s : NonUnitalSubring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
A non-unital subring is closed under multiplication.
-/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A non-unital subring is closed under addition. -/
/-
**NonUnitalSubring.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R] (s : NonUnitalSubring R) {
x y : R}, x ∈ s → y ∈ s → x + y ∈ s
参数：s : NonUnitalSubring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
A non-unital subring is closed under addition.
-/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A non-unital subring is closed under negation. -/
/-
**NonUnitalSubring.neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R] (s : NonUnitalSubring R) {
x : R}, x ∈ s → -x ∈ s
参数：s : NonUnitalSubring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
A non-unital subring is closed under negation.
-/
protected theorem neg_mem {x : R} : x ∈ s → -x ∈ s :=
  neg_mem

/-- A non-unital subring is closed under subtraction -/
/-
**NonUnitalSubring.sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R] (s : NonUnitalSubring R) {
x y : R}, x ∈ s → y ∈ s → x - y ∈ s
参数：s : NonUnitalSubring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `NonUnitalSubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [i
nst : SetLike S R] [inst_1 : NonUnitalNonAssocRing R] [h : NonUnitalSubringClass
 S R],   AddSubgroupClass S …
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
A non-unital subring is closed under subtraction
-/
protected theorem sub_mem {x y : R} (hx : x ∈ s) (hy : y ∈ s) : x - y ∈ s :=
  sub_mem hx hy

/-- A non-unital subring of a non-unital ring inherits a non-unital ring structure -/
/-
**NonUnitalSubring.toNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubring`。
形式化陈述：toNonUnitalRing {R : Type*} [NonUnitalRing R] (s : NonUnitalSubring R) : N
onUnitalRing s
参数：s : NonUnitalSubring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subring of a non-unital ring inherits a non-unital ring structure
-/
instance toNonUnitalRing {R : Type*} [NonUnitalRing R] (s : NonUnitalSubring R) :
    NonUnitalRing s :=
  NonUnitalSubringClass.toNonUnitalRing s
/-
**NonUnitalSubring.zsmul_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R] (s : NonUnitalSubring R) {
x : R}, x ∈ s → ∀ (n : ℤ), n • x ∈ s
参数：s : NonUnitalSubring R；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zsmul_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst
_1 : SetLike S M] [hSM : AddSubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n …
· 使用定理 `NonUnitalSubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [i
nst : SetLike S R] [inst_1 : NonUnitalNonAssocRing R] [h : NonUnitalSubringClass
 S R],   AddSubgroupClass S …
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
-/
protected theorem zsmul_mem {x : R} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n

@[simp, norm_cast]
/-
**NonUnitalSubring.val_add** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：val_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
-/
theorem val_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
/-
**NonUnitalSubring.val_neg** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：val_neg (x : s) : (↑(-x) : R) = -↑x
参数：x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
-/
theorem val_neg (x : s) : (↑(-x) : R) = -↑x :=
  rfl

@[simp, norm_cast]
/-
**NonUnitalSubring.val_mul** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：val_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y
参数：x y : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
-/
theorem val_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
/-
**NonUnitalSubring.val_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：val_zero : ((0 : s) : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
-/
theorem val_zero : ((0 : s) : R) = 0 :=
  rfl
/-
**NonUnitalSubring.coe_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 := by
  simp

/-- A non-unital subring of a `NonUnitalCommRing` is a `NonUnitalCommRing`. -/
/-
**NonUnitalSubring.toNonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubri
ng`。
形式化陈述：toNonUnitalCommRing {R} [NonUnitalCommRing R] (s : NonUnitalSubring R) : N
onUnitalCommRing s
参数：s : NonUnitalSubring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital subring of a `NonUnitalCommRing` is a `NonUnitalCommRing`.
-/
instance toNonUnitalCommRing {R} [NonUnitalCommRing R] (s : NonUnitalSubring R) :
    NonUnitalCommRing s :=
  NonUnitalSubringClass.toNonUnitalCommRing s

/-! ## Partial order -/


/-
**NonUnitalSubring.mem_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubrin
g`。
形式化陈述：mem_toSubsemigroup {s : NonUnitalSubring R} {x : R} : x in s.toSubsemigrou
p ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
## Partial order
-/
theorem mem_toSubsemigroup {s : NonUnitalSubring R} {x : R} : x ∈ s.toSubsemigroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubring.coe_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubrin
g`。
形式化陈述：coe_toSubsemigroup (s : NonUnitalSubring R) : (s.toSubsemigroup : Set R) =
 s
参数：s : NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubsemigroup (s : NonUnitalSubring R) : (s.toSubsemigroup : Set R) = s :=
  rfl
/-
**NonUnitalSubring.mem_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring
`。
形式化陈述：mem_toAddSubgroup {s : NonUnitalSubring R} {x : R} : x in s.toAddSubgroup 
↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toAddSubgroup {s : NonUnitalSubring R} {x : R} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubring.coe_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring
`。
形式化陈述：coe_toAddSubgroup (s : NonUnitalSubring R) : (s.toAddSubgroup : Set R) = s
参数：s : NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAddSubgroup (s : NonUnitalSubring R) : (s.toAddSubgroup : Set R) = s :=
  rfl

@[simp]
/-
**NonUnitalSubring.mem_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alSubring`。
形式化陈述：mem_toNonUnitalSubsemiring {s : NonUnitalSubring R} {x : R} : x in s.toNon
UnitalSubsemiring ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toNonUnitalSubsemiring {s : NonUnitalSubring R} {x : R} :
    x ∈ s.toNonUnitalSubsemiring ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubring.coe_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alSubring`。
形式化陈述：coe_toNonUnitalSubsemiring (s : NonUnitalSubring R) : (s.toNonUnitalSubsem
iring : Set R) = s
参数：s : NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalSubsemiring (s : NonUnitalSubring R) :
    (s.toNonUnitalSubsemiring : Set R) = s :=
  rfl

end NonUnitalSubring

end Basic

section Hom

namespace NonUnitalSubring

variable {R : Type u} [NonUnitalNonAssocRing R]

open NonUnitalRingHom

/-- The ring homomorphism associated to an inclusion of `NonUnitalSubring`s. -/
/-
**NonUnitalSubring.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：inclusion {S T : NonUnitalSubring R} (h : S <= T) : S ->ₙ+* T
参数：h : S <= T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
The ring homomorphism associated to an inclusion of `NonUnitalSubring`s.
-/
def inclusion {S T : NonUnitalSubring R} (h : S ≤ T) : S →ₙ+* T :=
  NonUnitalRingHom.codRestrict (NonUnitalSubringClass.subtype S) _ fun x => h x.2

end NonUnitalSubring

end Hom

