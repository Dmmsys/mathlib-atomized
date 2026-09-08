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

/-- `AddSubmonoidWithOneClass S R` says `S` is a type of subsets `s ≤ R` that contain `0`, `1`,
and are closed under `(+)` -/
/-
**AddSubmonoidWithOneClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_1) → (R : outParam (Type u_2)) → [AddMonoidWithOne R] → [SetLi
ke S R] → Prop
参数：Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddSubmonoidWithOneClass S R` says `S` is a type of subsets `s ≤ R` that contai
n `0`, `1`,
and are closed under `(+)`
-/
class AddSubmonoidWithOneClass (S : Type*) (R : outParam Type*) [AddMonoidWithOne R]
  [SetLike S R] : Prop extends AddSubmonoidClass S R, OneMemClass S R

variable {S R : Type*} [AddMonoidWithOne R] [SetLike S R] (s : S)

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**natCast_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：natCast_mem [AddSubmonoidWithOneClass S R] (n : Nat) : (n : R) in s
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubmonoidWithOneClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outP
aram (Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : Ad
dSubmonoidWithOneClass S R], AddSu…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
-/
theorem natCast_mem [AddSubmonoidWithOneClass S R] (n : ℕ) : (n : R) ∈ s := by
  induction n <;> simp [zero_mem, add_mem, one_mem, *]

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**ofNat_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ofNat_mem [AddSubmonoidWithOneClass S R] (s : S) (n : Nat) [n.AtLeastTwo] 
: ofNat(n) in s
参数：s : S；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_ofNat`：∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.
AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `natCast_mem`：natCast_mem [AddSubmonoidWithOneClass S R] (n : Nat) : (n :
 R) in s
-/
lemma ofNat_mem [AddSubmonoidWithOneClass S R] (s : S) (n : ℕ) [n.AtLeastTwo] :
    ofNat(n) ∈ s := by
  rw [← Nat.cast_ofNat]; exact natCast_mem s n
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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

/-- `SubsemiringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative and an additive submonoid. -/
/-
**SubsemiringClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_1) → (R : outParam (Type u)) → [NonAssocSemiring R] → [SetLike
 S R] → Prop
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SubsemiringClass S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative and an additive submonoid.
-/
class SubsemiringClass (S : Type*) (R : outParam (Type u)) [NonAssocSemiring R]
  [SetLike S R] : Prop extends SubmonoidClass S R, AddSubmonoidClass S R

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SubsemiringClass.addSubmonoidWithOneClass (S : Type*)
    (R : Type u) {_ : NonAssocSemiring R} [SetLike S R] [h : SubsemiringClass S R] :
    AddSubmonoidWithOneClass S R :=
  { h with }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SubsemiringClass.nonUnitalSubsemiringClass (S : Type*)
    (R : Type u) [NonAssocSemiring R] [SetLike S R] [SubsemiringClass S R] :
    NonUnitalSubsemiringClass S R where
  mul_mem := mul_mem

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

namespace SubsemiringClass

-- Prefer subclasses of `NonAssocSemiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure -/
/-
**SubsemiringClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubsemiringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure
-/
instance (priority := 75) toNonAssocSemiring : NonAssocSemiring s := fast_instance%
  Subtype.coe_injective.nonAssocSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

/-- A subsemiring of a `NonAssocCommSemiring` inherits a `NonAssocCommSemiring` structure -/
/-
**SubsemiringClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubsemiringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subsemiring of a `NonAssocCommSemiring` inherits a `NonAssocCommSemiring` stru
cture
-/
instance (priority := 75) toNonAssocCommSemiring {R} [NonAssocCommSemiring R] [SetLike S R]
    [SubsemiringClass S R] : NonAssocCommSemiring s := fast_instance%
  Subtype.coe_injective.nonAssocCommSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl
/-
**SubsemiringClass.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `SubsemiringClass`。
形式化陈述：nontrivial [Nontrivial R] : Nontrivial s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance nontrivial [Nontrivial R] : Nontrivial s :=
  nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)
/-
**SubsemiringClass.noZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `SubsemiringClass`。
形式化陈述：noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.noZeroDivisors`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [i
nst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M
₀ → M₀'),   Function.In…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s :=
  Subtype.coe_injective.noZeroDivisors _ rfl fun _ _ => rfl

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
/-
**SubsemiringClass.subtype** 是 Mathlib 中的一个定义，位于命名空间 `SubsemiringClass`。
形式化陈述：subtype : s ->+* R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…

--- 原说明 ---
The natural ring hom from a subsemiring of semiring `R` to `R`.
-/
def subtype : s →+* R :=
  { SubmonoidClass.subtype s, AddSubmonoidClass.subtype s with toFun := (↑) }

@[simp]
/-
**SubsemiringClass.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `SubsemiringClass`。
形式化陈述：coe_subtype : (subtype s : s -> R) = ((↑) : s -> R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : (subtype s : s → R) = ((↑) : s → R) :=
  rfl

variable {s} in
@[simp]
/-
**SubsemiringClass.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `SubsemiringClass`。
形式化陈述：subtype_apply (x : s) : SubsemiringClass.subtype s x = x
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply (x : s) :
    SubsemiringClass.subtype s x = x := rfl
/-
**SubsemiringClass.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `SubsemiringClass
`。
形式化陈述：subtype_injective : Function.Injective (SubsemiringClass.subtype s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma subtype_injective :
    Function.Injective (SubsemiringClass.subtype s) := fun _ ↦ by
  simp

-- Prefer subclasses of `Semiring` over subclasses of `SubsemiringClass`.
/-- A subsemiring of a `Semiring` is a `Semiring`. -/
/-
**SubsemiringClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubsemiringClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subsemiring of a `Semiring` is a `Semiring`.
-/
instance (priority := 75) toSemiring {R} [Semiring R] [SetLike S R] [SubsemiringClass S R] :
    Semiring s := fast_instance%
  Subtype.coe_injective.semiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/-- A subsemiring of a `CommSemiring` is a `CommSemiring`. -/
/-
**SubsemiringClass.toCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `SubsemiringClass`。
形式化陈述：toCommSemiring {R} [CommSemiring R] [SetLike S R] [SubsemiringClass S R] :
 CommSemiring s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subsemiring of a `CommSemiring` is a `CommSemiring`.
-/
instance toCommSemiring {R} [CommSemiring R] [SetLike S R] [SubsemiringClass S R] :
    CommSemiring s := fast_instance%
  Subtype.coe_injective.commSemiring Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

end SubsemiringClass

end SubsemiringClass

variable [NonAssocSemiring S]

/-- A subsemiring of a semiring `R` is a subset `s` that is both a multiplicative and an additive
submonoid. -/
/-
**Subsemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [NonAssocSemiring R] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subsemiring of a semiring `R` is a subset `s` that is both a multiplicative an
d an additive
submonoid.
-/
structure Subsemiring (R : Type u) [NonAssocSemiring R] extends Submonoid R, AddSubmonoid R

/-- Reinterpret a `Subsemiring` as a `Submonoid`. -/
add_decl_doc Subsemiring.toSubmonoid

/-- Reinterpret a `Subsemiring` as an `AddSubmonoid`. -/
add_decl_doc Subsemiring.toAddSubmonoid

namespace Subsemiring

/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Subsemiring R) R where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Subsemiring R) := .ofSetLike (Subsemiring R) R

initialize_simps_projections Subsemiring (carrier → coe, as_prefix coe)

/-- The actual `Subsemiring` obtained from an element of a `SubsemiringClass`. -/
@[simps]
/-
**Subsemiring.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：ofClass {S R : Type*} [NonAssocSemiring R] [SetLike S R] [SubsemiringClass
 S R] (s : S) : Subsemiring R where carrier
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The actual `Subsemiring` obtained from an element of a `SubsemiringClass`.
-/
def ofClass {S R : Type*} [NonAssocSemiring R] [SetLike S R] [SubsemiringClass S R]
    (s : S) : Subsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set R) (Subsemiring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ 1 ∈ s ∧
      ∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        one_mem' := h.2.2.1
        mul_mem' := h.2.2.2 },
      rfl ⟩
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubsemiringClass (Subsemiring R) R where
  zero_mem := zero_mem'
  add_mem {s} := AddSubsemigroup.add_mem' s.toAddSubmonoid.toAddSubsemigroup
  one_mem {s} := Submonoid.one_mem' s.toSubmonoid
  mul_mem {s} := Subsemigroup.mul_mem' s.toSubmonoid.toSubsemigroup

/-- Turn a `Subsemiring` into a `NonUnitalSubsemiring` by forgetting that it contains `1`. -/
@[reducible]
/-
**Subsemiring.toNonUnitalSubsemiring** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：toNonUnitalSubsemiring (S : Subsemiring R) : NonUnitalSubsemiring R where 
__
参数：S : Subsemiring R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.add_mem'`：∀ {R : Type u} [inst : NonAssocSemiring R] (self :
 Subsemiring R) {a b : R},   a ∈ self.carrier → b ∈ self.carrier → a + b ∈ self.
carrier
· 使用定理 `Subsemiring.zero_mem'`：∀ {R : Type u} [inst : NonAssocSemiring R] (self 
: Subsemiring R), 0 ∈ self.carrier

--- 原说明 ---
Turn a `Subsemiring` into a `NonUnitalSubsemiring` by forgetting that it contain
s `1`.
-/
def toNonUnitalSubsemiring (S : Subsemiring R) : NonUnitalSubsemiring R where __ := S

@[simp]
/-
**Subsemiring.mem_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_toSubmonoid {s : Subsemiring R} {x : R} : x in s.toSubmonoid ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubmonoid {s : Subsemiring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**Subsemiring.mem_toNonUnitalSubsemiring** 是 Mathlib 中的一个引理，位于命名空间 `Subsemiring`
。
形式化陈述：mem_toNonUnitalSubsemiring {S : Subsemiring R} {x : R} : x in S.toNonUnita
lSubsemiring ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_toNonUnitalSubsemiring {S : Subsemiring R} {x : R} :
    x ∈ S.toNonUnitalSubsemiring ↔ x ∈ S := .rfl
/-
**Subsemiring.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_carrier {s : Subsemiring R} {x : R} : x in s.carrier ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : Subsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**Subsemiring.coe_toNonUnitalSubsemiring** 是 Mathlib 中的一个引理，位于命名空间 `Subsemiring`
。
形式化陈述：coe_toNonUnitalSubsemiring (S : Subsemiring R) : (S.toNonUnitalSubsemiring
 : Set R) = S
参数：S : Subsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toNonUnitalSubsemiring (S : Subsemiring R) : (S.toNonUnitalSubsemiring : Set R) = S := rfl

@[simp]
/-
**Subsemiring.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_mk {toSubmonoid : Submonoid R} (add_mem zero_mem) {x : R} : x in mk to
Submonoid add_mem zero_mem ↔ x in toSubmonoid
参数：add_mem zero_mem。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {toSubmonoid : Submonoid R} (add_mem zero_mem) {x : R} :
    x ∈ mk toSubmonoid add_mem zero_mem ↔ x ∈ toSubmonoid := .rfl

@[simp]
/-
**Subsemiring.coe_set_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_set_mk {toSubmonoid : Submonoid R} (add_mem zero_mem) : (mk toSubmonoi
d add_mem zero_mem : Set R) = toSubmonoid
参数：add_mem zero_mem。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_set_mk {toSubmonoid : Submonoid R} (add_mem zero_mem) :
    (mk toSubmonoid add_mem zero_mem : Set R) = toSubmonoid := rfl

/-- Two subsemirings are equal if they have the same elements. -/
@[ext]
/-
**Subsemiring.ext** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：ext {S T : Subsemiring R} (h : forall x, x in S ↔ x in T) : S = T
参数：h : forall x, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two subsemirings are equal if they have the same elements.
-/
theorem ext {S T : Subsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subsemiring with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps coe toSubmonoid]
/-
**Subsemiring.copy** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：{R : Type u} → [inst : NonAssocSemiring R] → (S : Subsemiring R) → (s : Se
t R) → s = ↑S → Subsemiring R
参数：S : Subsemiring R；s : Set R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a subsemiring with a new `carrier` equal to the old one. Useful to fix d
efinitional
equalities.
-/
protected def copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : Subsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubmonoid.copy s hs with carrier := s }
/-
**Subsemiring.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：copy_eq (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S
参数：S : Subsemiring R；s : Set R；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
/-
**Subsemiring.toSubmonoid_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R], Function.Injective Subsemiring
.toSubmonoid
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.ext`：ext {S T : Subsemiring R} (h : forall x, x in S ↔ x in 
T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem toSubmonoid_injective : Function.Injective (toSubmonoid : Subsemiring R → Submonoid R)
  | _, _, h => ext (SetLike.ext_iff.mp h :)
/-
**Subsemiring.toAddSubmonoid_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R], Function.Injective Subsemiring
.toAddSubmonoid
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.ext`：ext {S T : Subsemiring R} (h : forall x, x in S ↔ x in 
T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem toAddSubmonoid_injective :
    Function.Injective (toAddSubmonoid : Subsemiring R → AddSubmonoid R)
  | _, _, h => ext (SetLike.ext_iff.mp h :)
/-
**Subsemiring.toNonUnitalSubsemiring_injective** 是 Mathlib 中的一个引理，位于命名空间 `Subsem
iring`。
形式化陈述：toNonUnitalSubsemiring_injective : Function.Injective (toNonUnitalSubsemir
ing : Subsemiring R -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma toNonUnitalSubsemiring_injective :
    Function.Injective (toNonUnitalSubsemiring : Subsemiring R → _) :=
  fun S₁ S₂ h => SetLike.ext'_iff.2
    (show (S₁.toNonUnitalSubsemiring : Set R) = S₂ from SetLike.ext'_iff.1 h)
/-
**Subsemiring.toNonUnitalSubsemiring_inj** 是 Mathlib 中的一个引理，位于命名空间 `Subsemiring`
。
形式化陈述：toNonUnitalSubsemiring_inj {S₁ S₂ : Subsemiring R} : S₁.toNonUnitalSubsemi
ring = S₂.toNonUnitalSubsemiring ↔ S₁ = S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Subsemiring.toNonUnitalSubsemiring_injective`：toNonUnitalSubsemiring_inj
ective : Function.Injective (toNonUnitalSubsemiring : Subsemiring R -> _)
-/
lemma toNonUnitalSubsemiring_inj {S₁ S₂ : Subsemiring R} :
    S₁.toNonUnitalSubsemiring = S₂.toNonUnitalSubsemiring ↔ S₁ = S₂ :=
  toNonUnitalSubsemiring_injective.eq_iff
/-
**Subsemiring.one_mem_toNonUnitalSubsemiring** 是 Mathlib 中的一个引理，位于命名空间 `Subsemir
ing`。
形式化陈述：one_mem_toNonUnitalSubsemiring (S : Subsemiring R) : (1 : R) in S.toNonUni
talSubsemiring
参数：S : Subsemiring R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
-/
lemma one_mem_toNonUnitalSubsemiring (S : Subsemiring R) : (1 : R) ∈ S.toNonUnitalSubsemiring :=
  S.one_mem

/-- Construct a `Subsemiring R` from a set `s`, a submonoid `sm`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
@[simps coe]
/-
**Subsemiring.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSub
monoid R} (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toSubmonoid = sm
参数：hm : ↑sm = s；ha : ↑sa = s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `Subsemiring R` from a set `s`, a submonoid `sm`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`.
-/
protected def mk' (s : Set R) (sm : Submonoid R) (hm : ↑sm = s) (sa : AddSubmonoid R)
    (ha : ↑sa = s) : Subsemiring R where
  carrier := s
  zero_mem' := by exact ha ▸ sa.zero_mem
  one_mem' := by exact hm ▸ sm.one_mem
  add_mem' {x y} := by simpa only [← ha] using! sa.add_mem
  mul_mem' {x y} := by simpa only [← hm] using! sm.mul_mem

@[simp]
/-
**Subsemiring.mem_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R
} (ha : ↑sa = s) {x : R} : x in Subsemiring.mk' s sm hm sa ha ↔ x in s
参数：hm : ↑sm = s；ha : ↑sa = s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Subsemiring.mk'`：mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑s
m = s) {sa : AddSubmonoid R} (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).to
Submo…
-/
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s)
    {x : R} : x ∈ Subsemiring.mk' s sm hm sa ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
/-
**Subsemiring.mk'_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R] {s : Set R} {sm : Submonoid R} 
(hm : ↑sm = s) {sa : AddSubmonoid R}   (ha : ↑sa = s), (Subsemiring.mk' s sm hm 
sa ha).toSubmonoid = sm
参数：hm : ↑sm = s；ha : ↑sa = s；Subsemiring.mk' s sm hm sa ha。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Subsemiring.mk'`：mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑s
m = s) {sa : AddSubmonoid R} (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).to
Submo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm

@[simp]
/-
**Subsemiring.mk'_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R] {s : Set R} {sm : Submonoid R} 
(hm : ↑sm = s) {sa : AddSubmonoid R}   (ha : ↑sa = s), (Subsemiring.mk' s sm hm 
sa ha).toAddSubmonoid = sa
参数：hm : ↑sm = s；ha : ↑sa = s；Subsemiring.mk' s sm hm sa ha。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Subsemiring.mk'`：mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑s
m = s) {sa : AddSubmonoid R} (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).to
Submo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mk'_toAddSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toAddSubmonoid = sa :=
  SetLike.coe_injective ha.symm

end Subsemiring

namespace Subsemiring

variable (s : Subsemiring R)

/-- A subsemiring contains the semiring's 1. -/
/-
**Subsemiring.one_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Subsemiring R), 1 ∈ s
参数：s : Subsemiring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
A subsemiring contains the semiring's 1.
-/
protected theorem one_mem : (1 : R) ∈ s :=
  one_mem s

/-- A subsemiring contains the semiring's 0. -/
/-
**Subsemiring.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Subsemiring R), 0 ∈ s
参数：s : Subsemiring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
A subsemiring contains the semiring's 0.
-/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem s

/-- A subsemiring is closed under multiplication. -/
/-
**Subsemiring.mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Subsemiring R) {x y : R}, 
x ∈ s → y ∈ s → x * y ∈ s
参数：s : Subsemiring R。
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
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
A subsemiring is closed under multiplication.
-/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A subsemiring is closed under addition. -/
/-
**Subsemiring.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Subsemiring R) {x y : R}, 
x ∈ s → y ∈ s → x + y ∈ s
参数：s : Subsemiring R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
A subsemiring is closed under addition.
-/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure -/
/-
**Subsemiring.toNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：toNonAssocSemiring : NonAssocSemiring s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
A subsemiring of a `NonAssocSemiring` inherits a `NonAssocSemiring` structure
-/
instance toNonAssocSemiring : NonAssocSemiring s :=
  SubsemiringClass.toNonAssocSemiring _

@[simp, norm_cast]
/-
**Subsemiring.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_one : ((1 : s) : R) = (1 : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
-/
theorem coe_one : ((1 : s) : R) = (1 : R) :=
  rfl

@[simp, norm_cast]
/-
**Subsemiring.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_zero : ((0 : s) : R) = (0 : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
-/
theorem coe_zero : ((0 : s) : R) = (0 : R) :=
  rfl

@[simp, norm_cast]
/-
**Subsemiring.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_add (x y : s) : ((x + y : s) : R) = (x + y : R)
参数：x y : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) :=
  rfl

@[simp, norm_cast]
/-
**Subsemiring.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R)
参数：x y : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) :=
  rfl
/-
**Subsemiring.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：nontrivial [Nontrivial R] : Nontrivial s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance nontrivial [Nontrivial R] : Nontrivial s :=
  nontrivial_of_ne 0 1 fun H => zero_ne_one (congr_arg Subtype.val H)
/-
**Subsemiring.pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (s : Subsemiring R) {x : R}, x ∈ s → 
∀ (n : ℕ), x ^ n ∈ s
参数：s : Subsemiring R；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
-/
protected theorem pow_mem {R : Type*} [Semiring R] (s : Subsemiring R) {x : R} (hx : x ∈ s)
    (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n
/-
**Subsemiring.noZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s where eq_zero_or_eq_z
ero_of_mul_eq_zero {_ _} h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
instance noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors s where
  eq_zero_or_eq_zero_of_mul_eq_zero {_ _} h :=
    (eq_zero_or_eq_zero_of_mul_eq_zero <| Subtype.ext_iff.mp h).imp Subtype.ext Subtype.ext

/-- A subsemiring of a `Semiring` is a `Semiring`. -/
/-
**Subsemiring.toSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：toSemiring {R} [Semiring R] (s : Subsemiring R) : Semiring s
参数：s : Subsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subsemiring of a `Semiring` is a `Semiring`.
-/
instance toSemiring {R} [Semiring R] (s : Subsemiring R) : Semiring s :=
  { s.toNonAssocSemiring, s.toSubmonoid.toMonoid with }

@[simp, norm_cast]
/-
**Subsemiring.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_pow {R} [Semiring R] (s : Subsemiring R) (x : s) (n : Nat) : ((x ^ n :
 s) : R) = (x : R) ^ n
参数：s : Subsemiring R；x : s；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
-/
theorem coe_pow {R} [Semiring R] (s : Subsemiring R) (x : s) (n : ℕ) :
    ((x ^ n : s) : R) = (x : R) ^ n := rfl

/-- A subsemiring of a `CommSemiring` is a `CommSemiring`. -/
/-
**Subsemiring.toCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：toCommSemiring {R} [CommSemiring R] (s : Subsemiring R) : CommSemiring s
参数：s : Subsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subsemiring of a `CommSemiring` is a `CommSemiring`.
-/
instance toCommSemiring {R} [CommSemiring R] (s : Subsemiring R) : CommSemiring s :=
  { s.toSemiring with mul_comm := fun _ _ => Subtype.ext <| mul_comm _ _ }

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
/-
**Subsemiring.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：subtype : s ->+* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural ring hom from a subsemiring of semiring `R` to `R`.
-/
def subtype : s →+* R :=
  { s.toSubmonoid.subtype, s.toAddSubmonoid.subtype with toFun := (↑) }

variable {s} in
@[simp]
/-
**Subsemiring.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `Subsemiring`。
形式化陈述：subtype_apply (x : s) : s.subtype x = x
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply (x : s) :
    s.subtype x = x := rfl
/-
**Subsemiring.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `Subsemiring`。
形式化陈述：subtype_injective : Function.Injective s.subtype
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective :
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[simp]
/-
**Subsemiring.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_subtype : ⇑s.subtype = ((↑) : s -> R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : ⇑s.subtype = ((↑) : s → R) :=
  rfl
/-
**Subsemiring.nsmul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Subsemiring R) {x : R}, x 
∈ s → ∀ (n : ℕ), n • x ∈ s
参数：s : Subsemiring R；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : AddMonoid M] [inst_1 
: SetLike A M] [AddSubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), n …
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
-/
protected theorem nsmul_mem {x : R} (hx : x ∈ s) (n : ℕ) : n • x ∈ s :=
  nsmul_mem hx n

@[simp]
/-
**Subsemiring.coe_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid : Set R) = s
参数：s : Subsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid : Set R) = s :=
  rfl

@[simp]
/-
**Subsemiring.coe_carrier_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_carrier_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid.carrier : Set
 R) = s
参数：s : Subsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_carrier_toSubmonoid (s : Subsemiring R) : (s.toSubmonoid.carrier : Set R) = s :=
  rfl
/-
**Subsemiring.mem_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_toAddSubmonoid {s : Subsemiring R} {x : R} : x in s.toAddSubmonoid ↔ x
 in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toAddSubmonoid {s : Subsemiring R} {x : R} : x ∈ s.toAddSubmonoid ↔ x ∈ s :=
  Iff.rfl
/-
**Subsemiring.coe_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_toAddSubmonoid (s : Subsemiring R) : (s.toAddSubmonoid : Set R) = s
参数：s : Subsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAddSubmonoid (s : Subsemiring R) : (s.toAddSubmonoid : Set R) = s :=
  rfl

/-- The subsemiring `R` of the semiring `R`. -/
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subsemiring `R` of the semiring `R`.
-/
instance : Top (Subsemiring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubmonoid R) with }⟩

@[simp]
/-
**Subsemiring.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_top (x : R) : x in (⊤ : Subsemiring R)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top (x : R) : x ∈ (⊤ : Subsemiring R) :=
  Set.mem_univ x

@[simp, norm_cast]
/-
**Subsemiring.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_top : ((⊤ : Subsemiring R) : Set R) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : Subsemiring R) : Set R) = Set.univ :=
  rfl

end Subsemiring

namespace Subsemiring

/-- The inf of two subsemirings is their intersection. -/
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of two subsemirings is their intersection.
-/
instance : Min (Subsemiring R) :=
  ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubmonoid ⊓ t.toAddSubmonoid with carrier := s ∩ t }⟩

@[simp, norm_cast]
/-
**Subsemiring.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_inf (p p' : Subsemiring R) : ((p ⊓ p' : Subsemiring R) : Set R) = (p :
 Set R) inter p'
参数：p p' : Subsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (p p' : Subsemiring R) : ((p ⊓ p' : Subsemiring R) : Set R) = (p : Set R) ∩ p' :=
  rfl

@[simp]
/-
**Subsemiring.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_inf {p p' : Subsemiring R} {x : R} : x in p ⊓ p' ↔ x in p ∧ x in p'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {p p' : Subsemiring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl


end Subsemiring

namespace RingHom

variable {s : Subsemiring R} {σR : Type*} [SetLike σR R] [SubsemiringClass σR R]

open Subsemiring

/-- Restriction of a ring homomorphism to a subsemiring of the domain. -/
/-
**RingHom.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：domRestrict (f : R ->+* S) (s : σR) : s ->+* S
参数：f : R ->+* S；s : σR。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a ring homomorphism to a subsemiring of the domain.
-/
def domRestrict (f : R →+* S) (s : σR) : s →+* S :=
  f.comp <| SubsemiringClass.subtype s

@[simp]
/-
**RingHom.domRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：domRestrict_apply (f : R ->+* S) {s : σR} (x : s) : f.domRestrict s x = f 
x
参数：f : R ->+* S；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_apply (f : R →+* S) {s : σR} (x : s) : f.domRestrict s x = f x :=
  rfl

@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply

/-- The subsemiring of elements `x : R` such that `f x = g x` -/
/-
**RingHom.eqLocusS** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：eqLocusS (f g : R ->+* S) : Subsemiring R
参数：f g : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subsemiring of elements `x : R` such that `f x = g x`
-/
def eqLocusS (f g : R →+* S) : Subsemiring R :=
  { (f : R →* S).eqLocusM g, (f : R →+ S).eqLocusM g with carrier := { x | f x = g x } }

@[simp]
/-
**RingHom.mem_eqLocusS** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mem_eqLocusS {f g : R ->+* S} {x : R} : x in f.eqLocusS g ↔ f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_eqLocusS {f g : R →+* S} {x : R} : x ∈ f.eqLocusS g ↔ f x = g x := Iff.rfl

@[simp]
/-
**RingHom.eqLocusS_same** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eqLocusS_same (f : R ->+* S) : f.eqLocusS f = ⊤
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
-/
theorem eqLocusS_same (f : R →+* S) : f.eqLocusS f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

end RingHom

/-- Turn a non-unital subsemiring containing `1` into a subsemiring. -/
/-
**NonUnitalSubsemiring.toSubsemiring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalSubsemiring.toSubsemiring (S : NonUnitalSubsemiring R) (h1 : 1 in
 S) : Subsemiring R where __
参数：S : NonUnitalSubsemiring R；h1 : 1 in S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a non-unital subsemiring containing `1` into a subsemiring.
-/
def NonUnitalSubsemiring.toSubsemiring (S : NonUnitalSubsemiring R) (h1 : 1 ∈ S) :
    Subsemiring R where
  __ := S
  one_mem' := h1
/-
**Subsemiring.toNonUnitalSubsemiring_toSubsemiring** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subsemiring.toNonUnitalSubsemiring_toSubsemiring (S : Subsemiring R) : S.t
oNonUnitalSubsemiring.toSubsemiring S.one_mem = S
参数：S : Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.one_mem`：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Sub
semiring R), 1 ∈ s
-/
lemma Subsemiring.toNonUnitalSubsemiring_toSubsemiring (S : Subsemiring R) :
    S.toNonUnitalSubsemiring.toSubsemiring S.one_mem = S := rfl
/-
**NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring (S : NonUnitalSu
bsemiring R) (h1) : (NonUnitalSubsemiring.toSubsemiring S h1).toNonUnitalSubsemi
ring = S
参数：S : NonUnitalSubsemiring R；h1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma NonUnitalSubsemiring.toSubsemiring_toNonUnitalSubsemiring (S : NonUnitalSubsemiring R) (h1) :
    (NonUnitalSubsemiring.toSubsemiring S h1).toNonUnitalSubsemiring = S := rfl
