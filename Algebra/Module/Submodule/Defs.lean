/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Group.Submonoid.Basic

/-!

# Submodules of a module

In this file we define

* `Submodule R M` : a subset of a `Module` `M` that contains zero and is closed with respect to
  addition and scalar multiplication.

* `Subspace k M` : an abbreviation for `Submodule` assuming that `k` is a `Field`.

## Tags

submodule, subspace, linear map
-/

@[expose] public section

assert_not_exists DivisionRing

open Function

universe u'' u' u v w

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
/-
**Submodule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → (M : Type v) → [inst : Semiring R] → [inst_1 : AddCommMonoi
d M] → [_root_.Module R M] → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module.
-/
structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Type v
    extends AddSubmonoid M, SubMulAction R M

/-- Reinterpret a `Submodule` as an `AddSubmonoid`. -/
add_decl_doc Submodule.toAddSubmonoid

/-- Reinterpret a `Submodule` as a `SubMulAction`. -/
add_decl_doc Submodule.toSubMulAction

namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-
**Submodule.setLike** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：setLike : SetLike (Submodule R M) M where coe s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance setLike : SetLike (Submodule R M) M where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Submodule R M) := .ofSetLike (Submodule R M) M

initialize_simps_projections Submodule (carrier → coe, as_prefix coe)
/-
**Submodule.carrier_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M]
 [inst_2 : _root_.Module R M]   (s : Submodule R M), s.carrier = ↑s
参数：s : Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma carrier_eq_coe (s : Submodule R M) : s.carrier = s := rfl

/-- The actual `Submodule` obtained from an element of a `SMulMemClass` and `AddSubmonoidClass`. -/
@[simps]
/-
**Submodule.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：ofClass {S R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [SetLi
ke S M] [AddSubmonoidClass S M] [SMulMemClass S R M] (s : S) : Submodule R M whe
re carrier
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The actual `Submodule` obtained from an element of a `SMulMemClass` and `AddSubm
onoidClass`.
-/
def ofClass {S R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [SetLike S M]
    [AddSubmonoidClass S M] [SMulMemClass S R M] (s : S) : Submodule R M where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' := SMulMemClass.smul_mem

/-- Construct a submodule from closure under two-element linear combinations.
I.e., a nonempty set closed under two-element linear combinations is a submodule. -/
@[simps]
/-
**Submodule.ofLinearComb** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：ofLinearComb (C : Set M) (nonempty : C.Nonempty) (linearComb : forall x in
 C, forall y in C, forall a b : R, a • x + b • y in C) : Submodule R M where car
rier
参数：C : Set M；nonempty : C.Nonempty；linearComb : forall x in C, forall y in C, fo
rall a b : R, a • x + b • y in C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a submodule from closure under two-element linear combinations.
I.e., a nonempty set closed under two-element linear combinations is a submodule
.
-/
def ofLinearComb (C : Set M) (nonempty : C.Nonempty)
    (linearComb : ∀ x ∈ C, ∀ y ∈ C, ∀ a b : R, a • x + b • y ∈ C) :
    Submodule R M where
  carrier := C
  zero_mem' := by
    obtain ⟨x, hx⟩ := nonempty
    simpa [zero_smul, add_zero] using linearComb x hx x hx 0 0
  add_mem' {x y} hx hy := by simpa [one_smul] using linearComb x hx y hy 1 1
  smul_mem' c x hx := by simpa using linearComb x hx x hx c 0
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set M) (Submodule R M) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ ∀ (r : R) {x}, x ∈ s → r • x ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        smul_mem' := h.2.2 },
      rfl ⟩
/-
**Submodule.addSubmonoidClass** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：addSubmonoidClass : AddSubmonoidClass (Submodule R M) M where zero_mem _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubsemigroup.add_mem'`：∀ {M : Type u_3} [inst : Add M] (self : AddSub
semigroup M) {a b : M},   a ∈ self.carrier → b ∈ self.carrier → a + b ∈ self.car
rier
· 使用定理 `AddSubmonoid.zero_mem'`：∀ {M : Type u_3} [inst : AddZeroClass M] (self :
 AddSubmonoid M), 0 ∈ self.carrier
-/
instance addSubmonoidClass : AddSubmonoidClass (Submodule R M) M where
  zero_mem _ := AddSubmonoid.zero_mem' _
  add_mem := AddSubsemigroup.add_mem' _
/-
**Submodule.smulMemClass** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：smulMemClass : SMulMemClass (Submodule R M) R M where smul_mem {s} c _ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.smul_mem'`：∀ {R : Type u} {M : Type v} [inst : SMul R M] (s
elf : SubMulAction R M) (c : R) {x : M},   x ∈ self.carrier → c • x ∈ self.carri
er
-/
instance smulMemClass : SMulMemClass (Submodule R M) R M where
  smul_mem {s} c _ h := SubMulAction.smul_mem' s.toSubMulAction c h

@[simp]
/-
**Submodule.mem_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_toAddSubmonoid (p : Submodule R M) (x : M) : x in p.toAddSubmonoid ↔ x
 in p
参数：p : Submodule R M；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toAddSubmonoid (p : Submodule R M) (x : M) : x ∈ p.toAddSubmonoid ↔ x ∈ p :=
  Iff.rfl

variable {p q : Submodule R M}

@[simp]
/-
**Submodule.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_mk {S : AddSubmonoid M} {x : M} (h) : x in (⟨S, h⟩ : Submodule R M) ↔ 
x in S
参数：h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {S : AddSubmonoid M} {x : M} (h) : x ∈ (⟨S, h⟩ : Submodule R M) ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**Submodule.coe_set_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_set_mk (S : AddSubmonoid M) (h) : ((⟨S, h⟩ : Submodule R M) : Set M) =
 S
参数：S : AddSubmonoid M；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_set_mk (S : AddSubmonoid M) (h) : ((⟨S, h⟩ : Submodule R M) : Set M) = S :=
  rfl
/-
**Submodule.eta** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M]
 [inst_2 : _root_.Module R M]   {p : Submodule R M} (h : ∀ (c : R) {x : M}, x ∈ 
p.carrier → c • x ∈ p.carrier),   { toAddSubmonoid := p.toAddSubmonoid, smul_mem
' := h } = p
参数：h : ∀ (c : R) {x : M}, x ∈ p.carrier → c • x ∈ p.carrier。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem eta (h) : ({ p with smul_mem' := h } : Submodule R M) = p :=
  rfl

@[simp]
/-
**Submodule.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mk_le_mk {S S' : AddSubmonoid M} (h h') : (⟨S, h⟩ : Submodule R M) <= (⟨S'
, h'⟩ : Submodule R M) ↔ S <= S'
参数：h h'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk {S S' : AddSubmonoid M} (h h') :
    (⟨S, h⟩ : Submodule R M) ≤ (⟨S', h'⟩ : Submodule R M) ↔ S ≤ S' :=
  Iff.rfl

@[ext]
/-
**Submodule.ext** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ext (h : forall x, x in p ↔ x in q) : p = q
参数：h : forall x, x in p ↔ x in q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h

/-- Copy of a submodule with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps]
/-
**Submodule.copy** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : Semiring R] →       [inst_1 : 
AddCommMonoid M] →         [inst_2 : _root_.Module R M] → (p : Submodule R M) → 
(s : Set M) → s = ↑p → Submodule R M
参数：p : Submodule R M；s : Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a submodule with a new `carrier` equal to the old one. Useful to fix def
initional
equalities.
-/
protected def copy (p : Submodule R M) (s : Set M) (hs : s = ↑p) : Submodule R M where
  carrier := s
  zero_mem' := by simp [hs]
  add_mem' := hs.symm ▸ p.add_mem'
  smul_mem' := by simpa [hs] using p.smul_mem'
/-
**Submodule.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：copy_eq (S : Submodule R M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S
参数：S : Submodule R M；s : Set M；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : Submodule R M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
/-
**Submodule.toAddSubmonoid_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAddSubmonoid_injective : Injective (toAddSubmonoid : Submodule R M -> Ad
dSubmonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem toAddSubmonoid_injective : Injective (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  fun p q h => SetLike.ext'_iff.2 (show (p.toAddSubmonoid : Set M) = q from SetLike.ext'_iff.1 h)

@[simp]
/-
**Submodule.toAddSubmonoid_inj** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAddSubmonoid_inj : p.toAddSubmonoid = q.toAddSubmonoid ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.toAddSubmonoid_injective`：toAddSubmonoid_injective : Injective
 (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
-/
theorem toAddSubmonoid_inj : p.toAddSubmonoid = q.toAddSubmonoid ↔ p = q :=
  toAddSubmonoid_injective.eq_iff

@[simp]
/-
**Submodule.coe_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_toAddSubmonoid (p : Submodule R M) : (p.toAddSubmonoid : Set M) = p
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAddSubmonoid (p : Submodule R M) : (p.toAddSubmonoid : Set M) = p :=
  rfl
/-
**Submodule.toSubMulAction_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toSubMulAction_injective : Injective (toSubMulAction : Submodule R M -> Su
bMulAction R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem toSubMulAction_injective : Injective (toSubMulAction : Submodule R M → SubMulAction R M) :=
  fun p q h => SetLike.ext'_iff.2 (show (p.toSubMulAction : Set M) = q from SetLike.ext'_iff.1 h)
/-
**Submodule.toSubMulAction_inj** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toSubMulAction_inj : p.toSubMulAction = q.toSubMulAction ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.toSubMulAction_injective`：toSubMulAction_injective : Injective
 (toSubMulAction : Submodule R M -> SubMulAction R M)
-/
theorem toSubMulAction_inj : p.toSubMulAction = q.toSubMulAction ↔ p = q :=
  toSubMulAction_injective.eq_iff

@[simp]
/-
**Submodule.coe_toSubMulAction** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_toSubMulAction (p : Submodule R M) : (p.toSubMulAction : Set M) = p
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubMulAction (p : Submodule R M) : (p.toSubMulAction : Set M) = p :=
  rfl

/-- `Submodule R M` almost never has decidable equality.
Given an element `m ≠ 0` in `M`, `Submodule R M` has decidable equality iff
all propositions are decidable. We add a global instance that `Submodule R M` has decidable
equality, coming from the choice axiom, so that we don't have to provide
`[DecidableEq (Submodule R M)]` arguments in lemma statements. -/
/-
**Submodule.decidableEq** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：decidableEq : DecidableEq (Submodule R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Submodule R M` almost never has decidable equality.
Given an element `m ≠ 0` in `M`, `Submodule R M` has decidable equality iff
all propositions are decidable. We add a global instance that `Submodule R M` ha
s decidable
equality, coming from the choice axiom, so that we don't have to provide
`[DecidableEq (Submodule R M)]` arguments in lemma statements.
-/
noncomputable instance decidableEq : DecidableEq (Submodule R M) := Classical.typeDecidableEq _

end Submodule

namespace SMulMemClass

variable [Semiring R] [AddCommMonoid M] [Module R M] {A : Type*} [SetLike A M]
  [AddSubmonoidClass A M] [SMulMemClass A R M] (S' : A)

-- Prefer subclasses of `Module` over `SMulMemClass`.
/-- A submodule of a `Module` is a `Module`. -/
/-
**SMulMemClass.** 是 Mathlib 中的一个实例，位于命名空间 `SMulMemClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule of a `Module` is a `Module`.
-/
instance (priority := 75) toModule : Module R S' := fast_instance%
  Subtype.coe_injective.module R (AddSubmonoidClass.subtype S') (SetLike.val_smul S')

/-- This can't be an instance because Lean wouldn't know how to find `R`, but we can still use
this to manually derive `Module` on specific types. -/
@[instance_reducible]
/-
**SMulMemClass.toModule'** 是 Mathlib 中的一个定义，位于命名空间 `SMulMemClass`。
形式化陈述：toModule' (S R' R A : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [M
odule R A] [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A] [SetLi
ke S A] [AddSubmonoidClass S A] [SMulMemClass S R A] (s : S) : Module R' s
参数：S R' R A : Type*；s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This can't be an instance because Lean wouldn't know how to find `R`, but we can
 still use
this to manually derive `Module` on specific types.
-/
def toModule' (S R' R A : Type*) [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SetLike S A] [AddSubmonoidClass S A] [SMulMemClass S R A] (s : S) :
    Module R' s :=
  haveI : SMulMemClass S R' A := SMulMemClass.ofIsScalarTower S R' R A
  SMulMemClass.toModule s

end SMulMemClass

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}
variable {p q : Submodule R M}
variable {r : R} {x y : M}
variable (p)

/-
**Submodule.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_carrier : x in p.carrier ↔ x in (p : Set M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier : x ∈ p.carrier ↔ x ∈ (p : Set M) :=
  Iff.rfl
/-
**Submodule.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M]
 {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈ p
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
protected theorem zero_mem : (0 : M) ∈ p :=
  zero_mem _
/-
**Submodule.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M]
 {module_M : _root_.Module R M}   (p : Submodule R M) {x y : M}, x ∈ p → y ∈ p →
 x + y ∈ p
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
-/
protected theorem add_mem (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p :=
  add_mem h₁ h₂
/-
**Submodule.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_mem (r : R) (h : x in p) : r • x in p
参数：r : R；h : x in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem'`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (self : Submodule R M) (c
 : R) {x …
-/
theorem smul_mem (r : R) (h : x ∈ p) : r • x ∈ p :=
  p.smul_mem' r h
/-
**Submodule.smul_of_tower_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_of_tower_mem [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (h :
 x in p) : r • x in p
参数：r : S；h : x in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.smul_of_tower_mem`：smul_of_tower_mem (s : S) {x : M} (h : x
 in p) : s • x in p
-/
theorem smul_of_tower_mem [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (h : x ∈ p) :
    r • x ∈ p :=
  p.toSubMulAction.smul_of_tower_mem r h

@[simp]
/-
**Submodule.smul_mem_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_mem_iff' [Group G] [MulAction G M] [SMul G R] [IsScalarTower G R M] (
g : G) : g • x in p ↔ x in p
参数：g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.smul_mem_iff'`：smul_mem_iff' {G} [Group G] [SMul G R] [MulA
ction G M] [IsScalarTower G R M] (g : G) {x : M} : g • x in p ↔ x in p
-/
theorem smul_mem_iff' [Group G] [MulAction G M] [SMul G R] [IsScalarTower G R M] (g : G) :
    g • x ∈ p ↔ x ∈ p :=
  p.toSubMulAction.smul_mem_iff' g

@[simp]
/-
**Submodule.smul_mem_iff''** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：smul_mem_iff'' [Invertible r] : r • x in p ↔ x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `invOf_smul_smul`：∀ {α : Type u_5} {β : Type u_6} [inst : Monoid α] [inst
_1 : MulAction α β] (c : α) (x : β) [inst_2 : Invertible c],   ⅟c • c • x = x
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
lemma smul_mem_iff'' [Invertible r] :
    r • x ∈ p ↔ x ∈ p := by
  refine ⟨fun h ↦ ?_, p.smul_mem r⟩
  rw [← invOf_smul_smul r x]
  exact p.smul_mem _ h
/-
**Submodule.smul_mem_iff_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：smul_mem_iff_of_isUnit (hr : IsUnit r) : r • x in p ↔ x in p
参数：hr : IsUnit r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.smul_mem_iff''`：smul_mem_iff'' [Invertible r] : r • x in p ↔ x
 in p
-/
lemma smul_mem_iff_of_isUnit (hr : IsUnit r) :
    r • x ∈ p ↔ x ∈ p :=
  let _ : Invertible r := hr.invertible
  smul_mem_iff'' p
/-
**Submodule.add** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：add : Add p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance add : Add p :=
  ⟨fun x y => ⟨x.1 + y.1, add_mem x.2 y.2⟩⟩
/-
**Submodule.zero** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：zero : Zero p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance zero : Zero p :=
  ⟨⟨0, zero_mem _⟩⟩
/-
**Submodule.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：inhabited : Inhabited p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited p :=
  ⟨0⟩
/-
**Submodule.smul** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：smul [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S p :=
  ⟨fun c x => ⟨c • x.1, smul_of_tower_mem _ c x.2⟩⟩
/-
**Submodule.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：isScalarTower [SMul S R] [SMul S M] [IsScalarTower S R M] : IsScalarTower 
S R p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isScalarTower [SMul S R] [SMul S M] [IsScalarTower S R M] : IsScalarTower S R p :=
  p.toSubMulAction.isScalarTower
/-
**Submodule.isScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：isScalarTower' {S' : Type*} [SMul S R] [SMul S M] [SMul S' R] [SMul S' M] 
[SMul S S'] [IsScalarTower S' R M] [IsScalarTower S S' M] [IsScalarTower S R M] 
: IsScalarTower S S' p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isScalarTower' {S' : Type*} [SMul S R] [SMul S M] [SMul S' R] [SMul S' M] [SMul S S']
    [IsScalarTower S' R M] [IsScalarTower S S' M] [IsScalarTower S R M] : IsScalarTower S S' p :=
  p.toSubMulAction.isScalarTower'
/-
**Submodule.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M]
 {module_M : _root_.Module R M}   (p : Submodule R M), (↑p).Nonempty
参数：p : Submodule R M；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
protected theorem nonempty : (p : Set M).Nonempty :=
  ⟨0, p.zero_mem⟩

@[simp]
/-
**Submodule.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mk_eq_zero {x} (h : x in p) : (⟨x, h⟩ : p) = 0 ↔ x = 0
参数：h : x in p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem mk_eq_zero {x} (h : x ∈ p) : (⟨x, h⟩ : p) = 0 ↔ x = 0 :=
  Subtype.ext_iff

variable {p}

@[norm_cast]
/-
**Submodule.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_eq_coe`：coe_eq_coe {x y : p} : (x : B) = y ↔ x = y
-/
theorem coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0 :=
  (SetLike.coe_eq_coe : (x : M) = (0 : p) ↔ x = 0)

@[simp, norm_cast]
/-
**Submodule.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y
参数：x y : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
/-
**Submodule.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_zero : ((0 : p) : M) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : p) : M) = 0 :=
  rfl

@[norm_cast]
/-
**Submodule.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • (x : M)
参数：r : R；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • (x : M) :=
  rfl

@[simp, norm_cast]
/-
**Submodule.coe_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_smul_of_tower [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (x :
 p) : ((r • x : p) : M) = r • (x : M)
参数：r : S；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul_of_tower [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (x : p) :
    ((r • x : p) : M) = r • (x : M) :=
  rfl

@[norm_cast]
/-
**Submodule.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_mk (x : M) (hx : x in p) : ((⟨x, hx⟩ : p) : M) = x
参数：x : M；hx : x in p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x :=
  rfl
/-
**Submodule.coe_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_mem (x : p) : (x : M) in p
参数：x : p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_mem (x : p) : (x : M) ∈ p :=
  x.2

variable (p)
/-
**Submodule.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：addCommMonoid : AddCommMonoid p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid p := AddSubmonoidClass.toAddCommMonoid p
/-
**Submodule.module'** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] : Modul
e S p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    Module S p := fast_instance%
  { (show MulAction S p from p.toSubMulAction.mulAction') with
    smul_zero := fun a => by ext; simp
    zero_smul := fun a => by ext; simp
    add_smul := fun a b x => by ext; simp [add_smul]
    smul_add := fun a x y => by ext; simp [smul_add] }
/-
**Submodule.module** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：module : Module R p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module : Module R p :=
  p.module'

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M]
variable {module_M : Module R M}
variable (p p' : Submodule R M)
variable {r : R} {x y : M}

/-
**Submodule.addSubgroupClass** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：addSubgroupClass [Module R M] : AddSubgroupClass (Submodule R M) M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.neg_mem`：neg_mem (hx : x in p) : -x in p
-/
instance addSubgroupClass [Module R M] : AddSubgroupClass (Submodule R M) M :=
  { Submodule.addSubmonoidClass with neg_mem := fun p {_} => p.toSubMulAction.neg_mem }
/-
**Submodule.neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 : AddCommGroup M] {mod
ule_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x ∈ p → -x ∈ p
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
-/
protected theorem neg_mem (hx : x ∈ p) : -x ∈ p :=
  neg_mem hx

/-- Reinterpret a submodule as an additive subgroup. -/
@[reducible]
/-
**Submodule.toAddSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：toAddSubgroup : AddSubgroup M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …

--- 原说明 ---
Reinterpret a submodule as an additive subgroup.
-/
def toAddSubgroup : AddSubgroup M :=
  { p.toAddSubmonoid with neg_mem' := fun {_} => p.neg_mem }

@[simp]
/-
**Submodule.coe_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_toAddSubgroup : (p.toAddSubgroup : Set M) = p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAddSubgroup : (p.toAddSubgroup : Set M) = p :=
  rfl
/-
**Submodule.mem_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_toAddSubgroup : x in p.toAddSubgroup ↔ x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toAddSubgroup : x ∈ p.toAddSubgroup ↔ x ∈ p :=
  Iff.rfl
/-
**Submodule.toAddSubgroup_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 : AddCommGroup M] {mod
ule_M : _root_.Module R M},   Function.Injective Submodule.toAddSubgroup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem toAddSubgroup_injective : Injective (toAddSubgroup : Submodule R M → AddSubgroup M)
  | _, _, h => SetLike.ext (SetLike.ext_iff.1 h :)
/-
**Submodule.toAddSubgroup_inj** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAddSubgroup_inj : p.toAddSubgroup = p'.toAddSubgroup ↔ p = p'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.toAddSubgroup_injective`：∀ {R : Type u} {M : Type v} [inst : R
ing R] [inst_1 : AddCommGroup M] {module_M : _root_.Module R M},   Function.Inje
ctive Submodule.toAddSu…
-/
theorem toAddSubgroup_inj : p.toAddSubgroup = p'.toAddSubgroup ↔ p = p' :=
  toAddSubgroup_injective.eq_iff
/-
**Submodule.sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 : AddCommGroup M] {mod
ule_M : _root_.Module R M} (p : Submodule R M)   {x y : M}, x ∈ p → y ∈ p → x - 
y ∈ p
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
-/
protected theorem sub_mem : x ∈ p → y ∈ p → x - y ∈ p :=
  sub_mem
/-
**Submodule.neg_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 : AddCommGroup M] {mod
ule_M : _root_.Module R M} (p : Submodule R M)   {x : M}, -x ∈ p ↔ x ∈ p
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
-/
protected theorem neg_mem_iff : -x ∈ p ↔ x ∈ p :=
  neg_mem_iff
/-
**Submodule.add_mem_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 : AddCommGroup M] {mod
ule_M : _root_.Module R M} (p : Submodule R M)   {x y : M}, y ∈ p → (x + y ∈ p ↔
 x ∈ p)
参数：p : Submodule R M；x + y ∈ p ↔ x ∈ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_mem_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] {S : Type u_4
} {H : S} [inst_1 : SetLike S G] [AddSubgroupClass S G] {x y : G},   x ∈ H → (y 
+ x ∈ H ↔ …
-/
protected theorem add_mem_iff_left : y ∈ p → (x + y ∈ p ↔ x ∈ p) :=
  add_mem_cancel_right
/-
**Submodule.add_mem_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 : AddCommGroup M] {mod
ule_M : _root_.Module R M} (p : Submodule R M)   {x y : M}, x ∈ p → (x + y ∈ p ↔
 y ∈ p)
参数：p : Submodule R M；x + y ∈ p ↔ y ∈ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_mem_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] {S : Type u_4}
 {H : S} [inst_1 : SetLike S G] [AddSubgroupClass S G] {x y : G},   x ∈ H → (x +
 y ∈ H ↔ …
-/
protected theorem add_mem_iff_right : x ∈ p → (x + y ∈ p ↔ y ∈ p) :=
  add_mem_cancel_left
/-
**Submodule.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 : AddCommGroup M] {mod
ule_M : _root_.Module R M} (p : Submodule R M)   (x : ↥p), ↑(-x) = -↑x
参数：p : Submodule R M；x : ↥p；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NegMemClass.coe_neg`：∀ {G : Type u_1} [inst : AddGroup G] {S : Type u_4}
 {H : S} [inst_1 : SetLike S G] [inst_2 : AddSubgroupClass S G]   (x : ↥H), ↑(-x
) = -↑x
-/
protected theorem coe_neg (x : p) : ((-x : p) : M) = -x :=
  NegMemClass.coe_neg _
/-
**Submodule.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 : AddCommGroup M] {mod
ule_M : _root_.Module R M} (p : Submodule R M)   (x y : ↥p), ↑(x - y) = ↑x - ↑y
参数：p : Submodule R M；x y : ↥p；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.coe_sub`：∀ {G : Type u_1} [inst : AddGroup G] {S : Type
 u_4} {H : S} [inst_1 : SetLike S G] [inst_2 : AddSubgroupClass S G]   (x y : ↥H
), ↑(x - y) = …
-/
protected theorem coe_sub (x y : p) : (↑(x - y) : M) = ↑x - ↑y :=
  AddSubgroupClass.coe_sub _ _
/-
**Submodule.sub_mem_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sub_mem_iff_left (hy : y in p) : x - y in p ↔ x in p
参数：hy : y in p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Submodule.add_mem_iff_left`：∀ {R : Type u} {M : Type v} [inst : Ring R] 
[inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {
x y : M}, y ∈ p …
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_mem_iff_left (hy : y ∈ p) : x - y ∈ p ↔ x ∈ p := by
  rw [sub_eq_add_neg, p.add_mem_iff_left (p.neg_mem hy)]
/-
**Submodule.sub_mem_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sub_mem_iff_right (hx : x in p) : x - y in p ↔ y in p
参数：hx : x in p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Submodule.add_mem_iff_right`：∀ {R : Type u} {M : Type v} [inst : Ring R]
 [inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   
{x y : M}, x ∈ p …
· 使用定理 `Submodule.neg_mem_iff`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst
_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M
}, -x ∈ p ↔…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_mem_iff_right (hx : x ∈ p) : x - y ∈ p ↔ y ∈ p := by
  rw [sub_eq_add_neg, p.add_mem_iff_right hx, p.neg_mem_iff]
/-
**Submodule.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：addCommGroup : AddCommGroup p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup : AddCommGroup p := AddSubgroupClass.toAddCommGroup p

end AddCommGroup

end Submodule

namespace SubmoduleClass

/-
**SubmoduleClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubmoduleClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) module' {T : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
    [Module R M] [SMul S R] [Module S M] [IsScalarTower S R M] [SetLike T M] [AddSubmonoidClass T M]
    [SMulMemClass T R M] (t : T) : Module S t where
  one_smul _ := by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_smul]
  smul_zero _ := by ext; simp
  zero_smul _ := by ext; simp
  add_smul _ _ _ := by ext; simp [add_smul]
  smul_add _ _ _ := by ext; simp [smul_add]
/-
**SubmoduleClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubmoduleClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) module [Semiring R] [AddCommMonoid M] [Module R M] [SetLike S M]
    [AddSubmonoidClass S M] [SMulMemClass S R M] (s : S) : Module R s :=
  module' s

end SubmoduleClass

