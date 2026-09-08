/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.Ideal.Maximal

/-!
# The set of non-invertible elements of a monoid

## Main definitions

* `nonunits` is the set of non-invertible elements of a monoid.

## Main results

* `exists_max_ideal_of_mem_nonunits`: every element of `nonunits` is contained in a maximal ideal
-/

@[expose] public section


variable {F α β : Type*} {a b : α}

/-- The set of non-invertible elements of a monoid. -/
/-
**nonunits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nonunits (α : Type*) [Monoid α] : Set α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of non-invertible elements of a monoid.
-/
def nonunits (α : Type*) [Monoid α] : Set α :=
  { a | ¬IsUnit a }

@[simp]
/-
**mem_nonunits_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nonunits_iff [Monoid α] : a in nonunits α ↔ ¬IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nonunits_iff [Monoid α] : a ∈ nonunits α ↔ ¬IsUnit a :=
  Iff.rfl
/-
**mul_mem_nonunits_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mem_nonunits_right [CommMonoid α] : b in nonunits α -> a * b in nonuni
ts α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `isUnit_of_mul_isUnit_right`：isUnit_of_mul_isUnit_right [Monoid M] [IsDed
ekindFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
-/
theorem mul_mem_nonunits_right [CommMonoid α] : b ∈ nonunits α → a * b ∈ nonunits α :=
  mt isUnit_of_mul_isUnit_right
/-
**mul_mem_nonunits_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mem_nonunits_left [CommMonoid α] : a in nonunits α -> a * b in nonunit
s α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `isUnit_of_mul_isUnit_left`：isUnit_of_mul_isUnit_left [Monoid M] [IsDedek
indFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
-/
theorem mul_mem_nonunits_left [CommMonoid α] : a ∈ nonunits α → a * b ∈ nonunits α :=
  mt isUnit_of_mul_isUnit_left
/-
**zero_mem_nonunits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_mem_nonunits [MonoidWithZero α] : 0 in nonunits α ↔ (0 : α) != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `isUnit_zero_iff`：isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1
-/
theorem zero_mem_nonunits [MonoidWithZero α] : 0 ∈ nonunits α ↔ (0 : α) ≠ 1 :=
  not_congr isUnit_zero_iff

@[simp high] -- High priority shortcut lemma
/-
**one_notMem_nonunits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_notMem_nonunits [Monoid α] : (1 : α) ∉ nonunits α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem one_notMem_nonunits [Monoid α] : (1 : α) ∉ nonunits α :=
  not_not_intro isUnit_one

@[simp high] -- High priority shortcut lemma
/-
**map_mem_nonunits_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mem_nonunits_iff [Monoid α] [Monoid β] [FunLike F α β] [MonoidHomClass
 F α β] (f : F) [IsLocalHom f] (a) : f a in nonunits β ↔ a in nonunits α
参数：f : F；a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `IsUnit.of_map`：IsUnit.of_map (f : F) [IsLocalHom f] (a : R) (h : IsUnit 
(f a)) : IsUnit a
-/
theorem map_mem_nonunits_iff [Monoid α] [Monoid β] [FunLike F α β] [MonoidHomClass F α β] (f : F)
    [IsLocalHom f] (a) : f a ∈ nonunits β ↔ a ∈ nonunits α :=
  ⟨fun h ha => h <| ha.map f, fun h ha => h <| ha.of_map⟩
/-
**coe_subset_nonunits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_subset_nonunits [Semiring α] {I : Ideal α} (h : I != ⊤) : (I : Set α) 
subseteq nonunits α
参数：h : I != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
-/
theorem coe_subset_nonunits [Semiring α] {I : Ideal α} (h : I ≠ ⊤) : (I : Set α) ⊆ nonunits α :=
  fun _x hx hu => h <| I.eq_top_of_isUnit_mem hx hu
/-
**exists_max_ideal_of_mem_nonunits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_max_ideal_of_mem_nonunits [CommSemiring α] (h : a in nonunits α) : 
exists I : Ideal α, I.IsMaximal ∧ a in I
参数：h : a in nonunits α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_singleton_eq_top`：span_singleton_eq_top {x} : span ({x} : Set
 α) = ⊤ ↔ IsUnit x
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem exists_max_ideal_of_mem_nonunits [CommSemiring α] (h : a ∈ nonunits α) :
    ∃ I : Ideal α, I.IsMaximal ∧ a ∈ I := by
  have : Ideal.span ({a} : Set α) ≠ ⊤ := by
    intro H
    rw [Ideal.span_singleton_eq_top] at H
    contradiction
  rcases Ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩
  use I, Imax
  apply H
  apply Ideal.subset_span
  exact Set.mem_singleton a

namespace Submonoid

variable {C : Type*} [SetLike C α]

/-
**Submonoid.inv_mem_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：inv_mem_of_isUnit [DivisionMonoid α] [SubmonoidClass C α] {S : C} {a : S} 
(ha : IsUnit a) : (a : α)⁻¹ in S
参数：ha : IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem inv_mem_of_isUnit [DivisionMonoid α] [SubmonoidClass C α] {S : C} {a : S} (ha : IsUnit a) :
    (a : α)⁻¹ ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  convert! u⁻¹.1.2
  exact (map_inv ((subtype <| ofClass S).comp <| Units.coeHom S) u).symm

section Group

variable [Group α] [SubmonoidClass C α] {S : C} {a : S}

/-
**Submonoid.isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：isUnit_iff : IsUnit a ↔ (a : α)⁻¹ in S where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.inv_mem_of_isUnit`：inv_mem_of_isUnit [DivisionMonoid α] [Submo
noidClass C α] {S : C} {a : S} (ha : IsUnit a) : (a : α)⁻¹ in S
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
theorem isUnit_iff : IsUnit a ↔ (a : α)⁻¹ ∈ S where
  mp := inv_mem_of_isUnit
  mpr h := ⟨⟨a, ⟨_, h⟩, Subtype.ext (mul_inv_cancel _), Subtype.ext (inv_mul_cancel _)⟩, rfl⟩
/-
**Submonoid.mem_nonunits_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {α : Type u_2} {C : Type u_4} [inst : SetLike C α] [inst_1 : Group α] [i
nst_2 : SubmonoidClass C α] {S : C} {a : ↥S},   a ∈ nonunits ↥S ↔ (↑a)⁻¹ ∉ S
参数：↑a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nonunits_iff`：mem_nonunits_iff [Monoid α] : a in nonunits α ↔ ¬IsUni
t a
· 使用定理 `Submonoid.isUnit_iff`：isUnit_iff : IsUnit a ↔ (a : α)⁻¹ in S where mp
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem mem_nonunits_iff : a ∈ nonunits S ↔ (a : α)⁻¹ ∉ S := by
  rw [mem_nonunits_iff, isUnit_iff]

end Group

section GroupWithZero

variable [GroupWithZero α] [SubmonoidClass C α] {S : C} {a : S}

/-
**Submonoid.isUnit_iff_and** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：isUnit_iff_and : IsUnit a ↔ (a : α) != 0 ∧ (a : α)⁻¹ in S where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `Submonoid.inv_mem_of_isUnit`：inv_mem_of_isUnit [DivisionMonoid α] [Submo
noidClass C α] {S : C} {a : S} (ha : IsUnit a) : (a : α)⁻¹ in S
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
-/
theorem isUnit_iff_and : IsUnit a ↔ (a : α) ≠ 0 ∧ (a : α)⁻¹ ∈ S where
  mp h := ⟨(h.map <| subtype <| ofClass S).ne_zero, inv_mem_of_isUnit h⟩
  mpr h :=
    ⟨⟨a, ⟨_, h.2⟩, Subtype.ext (mul_inv_cancel₀ h.1), Subtype.ext (inv_mul_cancel₀ h.1)⟩, rfl⟩
/-
**Submonoid.isUnit_iff_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：isUnit_iff_of_ne_zero (ha : (a : α) != 0) : IsUnit a ↔ (a : α)⁻¹ in S
参数：ha : (a : α) != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.isUnit_iff_and`：isUnit_iff_and : IsUnit a ↔ (a : α) != 0 ∧ (a 
: α)⁻¹ in S where mp h
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_iff_of_ne_zero (ha : (a : α) ≠ 0) : IsUnit a ↔ (a : α)⁻¹ ∈ S := by
  rw [isUnit_iff_and, and_iff_right ha]
/-
**Submonoid.mem_nonunits_iff_or** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_nonunits_iff_or : a in nonunits S ↔ (a : α) = 0 ∨ (a : α)⁻¹ ∉ S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nonunits_iff`：mem_nonunits_iff [Monoid α] : a in nonunits α ↔ ¬IsUni
t a
· 使用定理 `Submonoid.isUnit_iff_and`：isUnit_iff_and : IsUnit a ↔ (a : α) != 0 ∧ (a 
: α)⁻¹ in S where mp h
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nonunits_iff_or : a ∈ nonunits S ↔ (a : α) = 0 ∨ (a : α)⁻¹ ∉ S := by
  rw [mem_nonunits_iff, isUnit_iff_and, not_and_or, Ne, not_not]
/-
**Submonoid.mem_nonunits_iff_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_nonunits_iff_of_ne_zero (ha : (a : α) != 0) : a in nonunits S ↔ (a : α
)⁻¹ ∉ S
参数：ha : (a : α) != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.mem_nonunits_iff_or`：mem_nonunits_iff_or : a in nonunits S ↔ (
a : α) = 0 ∨ (a : α)⁻¹ ∉ S
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nonunits_iff_of_ne_zero (ha : (a : α) ≠ 0) : a ∈ nonunits S ↔ (a : α)⁻¹ ∉ S := by
  rw [mem_nonunits_iff_or, or_iff_right ha]

end GroupWithZero

end Submonoid

