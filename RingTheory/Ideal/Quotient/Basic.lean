/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro, Anne Baanen
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Finite
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Congruence.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic.FinCases

/-!
# Ideal quotients

This file defines ideal quotients as a special case of submodule quotients and proves some basic
results about these quotients.

See `RingCon.Quotient` for quotients of (possibly non-commutative) semirings.

## Main definitions

- `Ideal.Quotient.Ring`: the quotient of a ring `R` by a two-sided ideal `I : Ideal R`

-/

@[expose] public section

open Set

variable {ι ι' R S : Type*} [Ring R] (I J : Ideal R) {a b : R}

namespace Ideal.Quotient

@[simp]
/-
**Ideal.Quotient.mk_span_range** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Quotient`。
形式化陈述：mk_span_range (f : ι -> R) [(span (range f)).IsTwoSided] (i : ι) : mk (spa
n (.range f)) (f i) = 0
参数：f : ι -> R；span (range f)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
-/
lemma mk_span_range (f : ι → R) [(span (range f)).IsTwoSided] (i : ι) :
    mk (span (.range f)) (f i) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

variable {I} {x y : R}
/-
**Ideal.Quotient.zero_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：zero_eq_one_iff : (0 : R ⧸ I) = 1 ↔ I = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
-/
theorem zero_eq_one_iff : (0 : R ⧸ I) = 1 ↔ I = ⊤ :=
  eq_comm.trans <| (Submodule.Quotient.mk_eq_zero _).trans (eq_top_iff_one _).symm
/-
**Ideal.Quotient.zero_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：zero_ne_one_iff : (0 : R ⧸ I) != 1 ↔ I != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.Quotient.zero_eq_one_iff`：zero_eq_one_iff : (0 : R ⧸ I) = 1 ↔ I = 
⊤
-/
theorem zero_ne_one_iff : (0 : R ⧸ I) ≠ 1 ↔ I ≠ ⊤ :=
  not_congr zero_eq_one_iff
/-
**Ideal.Quotient.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ {R : Type u_3} [inst : Ring R] {I : Ideal R}, Subsingleton (R ⧸ I) ↔ I =
 ⊤
参数：R ⧸ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.Quotient.subsingleton_iff`：∀ {R : Type u_1} {M : Type u_2} [in
st : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submo
dule R M}, Subsingleton (…
-/
protected lemma subsingleton_iff : Subsingleton (R ⧸ I) ↔ I = ⊤ :=
  Submodule.Quotient.subsingleton_iff
/-
**Ideal.Quotient.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ {R : Type u_3} [inst : Ring R] {I : Ideal R}, Nontrivial (R ⧸ I) ↔ I ≠ ⊤
参数：R ⧸ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.Quotient.nontrivial_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, Nontrivial (M …
-/
protected lemma nontrivial_iff : Nontrivial (R ⧸ I) ↔ I ≠ ⊤ :=
  Submodule.Quotient.nontrivial_iff
/-
**Ideal.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (R ⧸ (⊤ : Ideal R)) :=
  ⟨⟨0⟩, by rintro ⟨x⟩; exact Quotient.eq_zero_iff_mem.mpr Submodule.mem_top⟩

variable [I.IsTwoSided]

-- this instance is harder to find than the one via `Algebra α (R ⧸ I)`, so use a lower priority
/-
**Ideal.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isScalarTower_right {α} [SMul α R] [IsScalarTower α R R] :
    IsScalarTower α (R ⧸ I) (R ⧸ I) :=
  (Quotient.ringCon I).isScalarTower_right
/-
**Ideal.Quotient.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
形式化陈述：smulCommClass {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass α R R] :
 SMulCommClass α (R ⧸ I) (R ⧸ I)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass α R R] :
    SMulCommClass α (R ⧸ I) (R ⧸ I) :=
  (Quotient.ringCon I).smulCommClass
/-
**Ideal.Quotient.smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
形式化陈述：smulCommClass' {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass R α R] 
: SMulCommClass (R ⧸ I) α (R ⧸ I)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass' {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass R α R] :
    SMulCommClass (R ⧸ I) α (R ⧸ I) :=
  (Quotient.ringCon I).smulCommClass'
/-
**Ideal.Quotient.eq_zero_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：eq_zero_iff_dvd {R} [CommRing R] (x y : R) : Ideal.Quotient.mk (Ideal.span
 ({x} : Set R)) y = 0 ↔ x ∣ y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_zero_iff_dvd {R} [CommRing R] (x y : R) :
    Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y = 0 ↔ x ∣ y := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

@[simp]
/-
**Ideal.Quotient.mk_singleton_self** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Quotient`。
形式化陈述：mk_singleton_self (x : R) [(Ideal.span {x}).IsTwoSided] : mk (Ideal.span {
x}) x = 0
参数：x : R；Ideal.span {x}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Ideal.mem_span_singleton_self`：mem_span_singleton_self (x : α) : x in sp
an ({x} : Set α)
-/
lemma mk_singleton_self (x : R) [(Ideal.span {x}).IsTwoSided] : mk (Ideal.span {x}) x = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (mem_span_singleton_self _)

variable (I)
/-
**Ideal.Quotient.noZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
形式化陈述：noZeroDivisors [hI : I.IsPrime] : NoZeroDivisors (R ⧸ I) where eq_zero_or_
eq_zero_of_mul_eq_zero {a b}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} 
{s₂ : Setoid β} {p : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q₂ 
: Quotient s…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
instance noZeroDivisors [hI : I.IsPrime] : NoZeroDivisors (R ⧸ I) where
    eq_zero_or_eq_zero_of_mul_eq_zero {a b} := Quotient.inductionOn₂' a b fun {_ _} hab =>
      (hI.mem_or_mem (eq_zero_iff_mem.1 hab)).elim (Or.inl ∘ eq_zero_iff_mem.2)
        (Or.inr ∘ eq_zero_iff_mem.2)
/-
**Ideal.Quotient.isDomain** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
形式化陈述：isDomain [hI : I.IsPrime] : IsDomain (R ⧸ I)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.nontrivial_iff`：∀ {R : Type u_3} [inst : Ring R] {I : Ide
al R}, Nontrivial (R ⧸ I) ↔ I ≠ ⊤
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
-/
instance isDomain [hI : I.IsPrime] : IsDomain (R ⧸ I) :=
  let _ := Quotient.nontrivial_iff.mpr hI.1
  NoZeroDivisors.to_isDomain _
/-
**Ideal.Quotient.isDomain_iff_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：isDomain_iff_prime : IsDomain (R ⧸ I) ↔ I.IsPrime
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.Quotient.zero_ne_one_iff`：zero_ne_one_iff : (0 : R ⧸ I) != 1 ↔ I !
= ⊤
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
-/
theorem isDomain_iff_prime : IsDomain (R ⧸ I) ↔ I.IsPrime := by
  refine ⟨fun H => ⟨zero_ne_one_iff.1 ?_, fun {x y} h => ?_⟩, fun h => inferInstance⟩
  · have : Nontrivial (R ⧸ I) := ⟨H.2.1⟩
    exact zero_ne_one
  · simp only [← eq_zero_iff_mem, (mk I).map_mul] at h ⊢
    have := @IsDomain.to_noZeroDivisors (R ⧸ I) _ H
    exact eq_zero_or_eq_zero_of_mul_eq_zero h

set_option backward.isDefEq.respectTransparency false in
variable {I} in
/-
**Ideal.Quotient.exists_inv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：exists_inv [hI : I.IsMaximal] : forall {a : R ⧸ I}, a != 0 -> exists b : R
 ⧸ I, a * b = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_right_inv_of_exists_left_inv`：exists_right_inv_of_exists_left_inv
 {α} [MonoidWithZero α] (h : forall a : α, a != 0 -> exists b : α, b * a = 1) {a
 : α} (ha : a != 0) : exi…
· 使用定理 `Ideal.IsMaximal.exists_inv`：∀ {α : Type u} [inst : Semiring α] {I : Idea
l α}, I.IsMaximal → ∀ {x : α}, x ∉ I → ∃ y, ∃ i ∈ I, y * x + i = 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
-/
theorem exists_inv [hI : I.IsMaximal] :
    ∀ {a : R ⧸ I}, a ≠ 0 → ∃ b : R ⧸ I, a * b = 1 := by
  apply exists_right_inv_of_exists_left_inv
  rintro ⟨a⟩ h
  rcases hI.exists_inv (mt eq_zero_iff_mem.2 h) with ⟨b, c, hc, abc⟩
  refine ⟨mk _ b, Quot.sound ?_⟩
  simp only [Submodule.quotientRel_def]
  rw [← eq_sub_iff_add_eq'] at abc
  rwa [abc, ← neg_mem_iff (G := R) (H := I), neg_sub] at hc

open scoped Classical in
/-- The quotient by a maximal ideal is a group with zero. This is a `def` rather than `instance`,
since users will have computable inverses in some applications.

See note [reducible non-instances]. -/
/-
**Ideal.Quotient.groupWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：{R : Type u_3} → [inst : Ring R] → (I : Ideal R) → [I.IsTwoSided] → [hI : 
I.IsMaximal] → GroupWithZero (R ⧸ I)
参数：I : Ideal R；R ⧸ I。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.exists_inv`：exists_inv [hI : I.IsMaximal] : forall {a : R
 ⧸ I}, a != 0 -> exists b : R ⧸ I, a * b = 1

--- 原说明 ---
The quotient by a maximal ideal is a group with zero. This is a `def` rather tha
n `instance`,
since users will have computable inverses in some applications.

See note [reducible non-instances].
-/
protected noncomputable abbrev groupWithZero [hI : I.IsMaximal] :
    GroupWithZero (R ⧸ I) := fast_instance%
  { inv := fun a => if ha : a = 0 then 0 else Classical.choose (exists_inv ha)
    mul_inv_cancel := fun a (ha : a ≠ 0) =>
      show a * dite _ _ _ = _ by rw [dif_neg ha]; exact Classical.choose_spec (exists_inv ha)
    inv_zero := dif_pos rfl
    __ := Quotient.nontrivial_iff.mpr hI.out.1 }

/-- The quotient by a two-sided ideal that is maximal as a left ideal is a division ring.
This is a `def` rather than `instance`, since users
will have computable inverses (and `qsmul`, `ratCast`) in some applications.

See note [reducible non-instances]. -/
/-
**Ideal.Quotient.divisionRing** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：{R : Type u_3} → [inst : Ring R] → (I : Ideal R) → [I.IsTwoSided] → [I.IsM
aximal] → DivisionRing (R ⧸ I)
参数：I : Ideal R；R ⧸ I。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.exists_inv`：exists_inv [hI : I.IsMaximal] : forall {a : R
 ⧸ I}, a != 0 -> exists b : R ⧸ I, a * b = 1

--- 原说明 ---
The quotient by a two-sided ideal that is maximal as a left ideal is a division 
ring.
This is a `def` rather than `instance`, since users
will have computable inverses (and `qsmul`, `ratCast`) in some applications.

See note [reducible non-instances].
-/
protected noncomputable abbrev divisionRing [I.IsMaximal] : DivisionRing (R ⧸ I) := fast_instance%
  { __ := ring _
    __ := Quotient.groupWithZero _
    nnqsmul := _
    nnqsmul_def _ _ := rfl
    qsmul := _
    qsmul_def _ _ := rfl }

/-- The quotient of a commutative ring by a maximal ideal is a field.
This is a `def` rather than `instance`, since users
will have computable inverses (and `qsmul`, `ratCast`) in some applications.

See note [reducible non-instances]. -/
/-
**Ideal.Quotient.field** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：{R : Type u_5} → [inst : CommRing R] → (I : Ideal R) → [I.IsMaximal] → Fie
ld (R ⧸ I)
参数：I : Ideal R；R ⧸ I。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The quotient of a commutative ring by a maximal ideal is a field.
This is a `def` rather than `instance`, since users
will have computable inverses (and `qsmul`, `ratCast`) in some applications.

See note [reducible non-instances].
-/
protected noncomputable abbrev field {R} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    Field (R ⧸ I) := fast_instance%
  { __ := commRing _
    __ := Quotient.divisionRing I }

/-- If the quotient by an ideal is a field, then the ideal is maximal. -/
/-
**Ideal.Quotient.maximal_of_isField** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：maximal_of_isField {R} [CommRing R] (I : Ideal R) (hqf : IsField (R ⧸ I)) 
: I.IsMaximal
参数：I : Ideal R；hqf : IsField (R ⧸ I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isMaximal_iff`：isMaximal_iff {I : Ideal α} : I.IsMaximal ↔ (1 : α)
 ∉ I ∧ forall (J : Ideal α) (x), I <= J -> x ∉ I -> x in J -> (1 : α) in J
· 使用定理 `IsField.exists_pair_ne`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∃ x y, x ≠ y
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsField.mul_inv_cancel`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I

--- 原说明 ---
If the quotient by an ideal is a field, then the ideal is maximal.
-/
theorem maximal_of_isField {R} [CommRing R] (I : Ideal R) (hqf : IsField (R ⧸ I)) :
    I.IsMaximal := by
  apply Ideal.isMaximal_iff.2
  constructor
  · intro h
    rcases hqf.exists_pair_ne with ⟨⟨x⟩, ⟨y⟩, hxy⟩
    exact hxy (Ideal.Quotient.eq.2 (mul_one (x - y) ▸ I.mul_mem_left _ h))
  · intro J x hIJ hxnI hxJ
    rcases hqf.mul_inv_cancel (mt Ideal.Quotient.eq_zero_iff_mem.1 hxnI) with ⟨⟨y⟩, hy⟩
    rw [← zero_add (1 : R), ← sub_self (x * y), sub_add]
    exact J.sub_mem (J.mul_mem_right _ hxJ) (hIJ (Ideal.Quotient.eq.1 hy))

/-- The quotient of a ring by an ideal is a field iff the ideal is maximal. -/
/-
**Ideal.Quotient.maximal_ideal_iff_isField_quotient** 是 Mathlib 中的一个定理，位于命名空间 `I
deal.Quotient`。
形式化陈述：maximal_ideal_iff_isField_quotient {R} [CommRing R] (I : Ideal R) : I.IsMa
ximal ↔ IsField (R ⧸ I)
参数：I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R
· 使用定理 `Ideal.Quotient.maximal_of_isField`：maximal_of_isField {R} [CommRing R] (
I : Ideal R) (hqf : IsField (R ⧸ I)) : I.IsMaximal

--- 原说明 ---
The quotient of a ring by an ideal is a field iff the ideal is maximal.
-/
theorem maximal_ideal_iff_isField_quotient {R} [CommRing R] (I : Ideal R) :
    I.IsMaximal ↔ IsField (R ⧸ I) :=
  ⟨fun h =>
    let _i := @Quotient.field _ _ I h
    Field.toIsField _,
    maximal_of_isField _⟩

end Quotient

section Pi

/-- `R^n/I^n` is a `R/I`-module. -/
/-
**Ideal.modulePi** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：{ι : Type u_1} →   {R : Type u_3} →     [inst : Ring R] → (I : Ideal R) → 
[inst_1 : I.IsTwoSided] → _root_.Module (R ⧸ I) ((ι → R) ⧸ Ideal.pi fun x => I)
参数：I : Ideal R；R ⧸ I；(ι → R) ⧸ Ideal.pi fun x => I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R^n/I^n` is a `R/I`-module.
-/
instance modulePi [I.IsTwoSided] : Module (R ⧸ I) ((ι → R) ⧸ pi fun _ ↦ I) where
  smul c m :=
    Quotient.liftOn₂' c m (fun r m ↦ Submodule.Quotient.mk <| r • m) <| by
      intro c₁ m₁ c₂ m₂ hc hm
      apply Ideal.Quotient.eq.2
      rw [Submodule.quotientRel_def] at hc hm
      intro i
      exact I.mul_sub_mul_mem hc (hm i)
  one_smul := by rintro ⟨a⟩; exact congr_arg _ (one_smul _ _)
  mul_smul := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact congr_arg _ (mul_smul _ _ _)
  smul_add := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact congr_arg _ (smul_add _ _ _)
  smul_zero := by rintro ⟨a⟩; exact congr_arg _ (smul_zero _)
  add_smul := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact congr_arg _ (add_smul _ _ _)
  zero_smul := by rintro ⟨a⟩; exact congr_arg _ (zero_smul _ _)

variable (ι) in
/-- `R^n/I^n` is isomorphic to `(R/I)^n` as an `R/I`-module. -/
/-
**Ideal.piQuotEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：(ι : Type u_1) →   {R : Type u_3} →     [inst : Ring R] → (I : Ideal R) → 
[inst_1 : I.IsTwoSided] → ((ι → R) ⧸ Ideal.pi fun x => I) ≃ₗ[R ⧸ I] ι → R ⧸ I
参数：ι → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R^n/I^n` is isomorphic to `(R/I)^n` as an `R/I`-module.
-/
noncomputable def piQuotEquiv [I.IsTwoSided] : ((ι → R) ⧸ pi fun _ ↦ I) ≃ₗ[R ⧸ I] ι → (R ⧸ I) where
  toFun x := Quotient.liftOn' x (fun f i ↦ Ideal.Quotient.mk I (f i)) fun _ _ hab ↦
    funext fun i ↦ (Submodule.Quotient.eq' _).2 (QuotientAddGroup.leftRel_apply.mp hab i)
  map_add' := by rintro ⟨_⟩ ⟨_⟩; rfl
  map_smul' := by rintro ⟨_⟩ ⟨_⟩; rfl
  invFun x := Ideal.Quotient.mk _ (Quotient.out <| x ·)
  left_inv := by
    rintro ⟨x⟩
    exact Ideal.Quotient.eq.2 fun i ↦ Ideal.Quotient.eq.1 (Quotient.out_eq' _)
  right_inv x := funext fun i ↦ Quotient.out_eq' (x i)

set_option backward.isDefEq.respectTransparency false in
/-- If `f : R^n → R^m` is an `R`-linear map and `I ⊆ R` is an ideal, then the image of `I^n` is
    contained in `I^m`. -/
/-
**Ideal.map_pi** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} [inst : Ring R] (I : Ideal
 R) [I.IsTwoSided] [Finite ι] (x : ι → R),   (∀ (i : ι), x i ∈ I) → ∀ (f : (ι → 
R) →ₗ[R] ι' → R) (i : ι'), f x i ∈ I
参数：I : Ideal R；x : ι → R；∀ (i : ι), x i ∈ I；f : (ι → R) →ₗ[R] ι' → R；i : ι'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pi_eq_sum_univ`：pi_eq_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {
R : Type*} [NonAssocSemiring R] (x : ι -> R) : x = ∑ i, (x i) • fun j => if i = 
j th…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I

--- 原说明 ---
If `f : R^n → R^m` is an `R`-linear map and `I ⊆ R` is an ideal, then the image 
of `I^n` is
    contained in `I^m`.
-/
theorem map_pi [I.IsTwoSided] [Finite ι] (x : ι → R) (hi : ∀ i, x i ∈ I)
    (f : (ι → R) →ₗ[R] ι' → R) (i : ι') : f x i ∈ I := by
  classical
    cases nonempty_fintype ι
    rw [pi_eq_sum_univ x]
    simp only [Finset.sum_apply, smul_eq_mul, map_sum, Pi.smul_apply, map_smul]
    exact I.sum_mem fun j _ => I.mul_mem_right _ (hi j)

end Pi

open scoped Pointwise in
/-- A ring is made up of a disjoint union of cosets of an ideal. -/
/-
**Ideal.univ_eq_iUnion_image_add** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u_3} [inst : Ring R] (I : Ideal R), Set.univ = ⋃ x, Quotient.o
ut x +ᵥ ↑I
参数：I : Ideal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.univ_eq_iUnion_vadd`：∀ {α : Type u_1} [inst : AddGroup 
α] (H : AddSubgroup α), Set.univ = ⋃ x, Quotient.out x +ᵥ ↑H

--- 原说明 ---
A ring is made up of a disjoint union of cosets of an ideal.
-/
lemma univ_eq_iUnion_image_add : (Set.univ (α := R)) = ⋃ x : R ⧸ I, x.out +ᵥ (I : Set R) :=
  QuotientAddGroup.univ_eq_iUnion_vadd I.toAddSubgroup

end Ideal

/-
**finite_iff_ideal_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_3} [inst : Ring R] (I : Ideal R), Finite R ↔ Finite ↥I ∧ Fin
ite (R ⧸ I)
参数：I : Ideal R；R ⧸ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_iff_addSubgroup_quotient`：∀ {G : Type u_2} [inst : AddGroup G] (H
 : AddSubgroup G), Finite G ↔ Finite ↥H ∧ Finite (G ⧸ H)
-/
lemma finite_iff_ideal_quotient (I : Ideal R) : Finite R ↔ Finite I ∧ Finite (R ⧸ I) :=
  finite_iff_addSubgroup_quotient I.toAddSubgroup
/-
**Finite.of_ideal_quotient** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Quotient`。
形式化陈述：Finite.of_ideal_quotient (I : Ideal R) [Finite I] [Finite (R ⧸ I)] : Finit
e R
参数：I : Ideal R；R ⧸ I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finite_iff_ideal_quotient`：∀ {R : Type u_3} [inst : Ring R] (I : Ideal R
), Finite R ↔ Finite ↥I ∧ Finite (R ⧸ I)
-/
lemma Finite.of_ideal_quotient (I : Ideal R) [Finite I] [Finite (R ⧸ I)] : Finite R := by
  rw [finite_iff_ideal_quotient]; constructor <;> assumption
