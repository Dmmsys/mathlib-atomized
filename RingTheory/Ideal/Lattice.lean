/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# The lattice of ideals in a ring

Some basic results on lattice operations on ideals: `⊥`, `⊤`, `⊔`, `⊓`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

public section


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open scoped Pointwise

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) : IsTwoSided (⊥ : Ideal α) :=
  ⟨fun _ h ↦ by rw [h, zero_mul]; exact zero_mem _⟩
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) : IsTwoSided (⊤ : Ideal α) := ⟨fun _ _ ↦ trivial⟩
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {ι} (I : ι → Ideal α) [∀ i, (I i).IsTwoSided] : (⨅ i, I i).IsTwoSided :=
  ⟨fun _ h ↦ (Submodule.mem_iInf _).mpr (mul_mem_right _ _ <| (Submodule.mem_iInf _).mp h ·)⟩
/-
**Ideal.eq_top_of_unit_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_top_of_unit_mem (x y : α) (hx : x in I) (h : y * x = 1) : I = ⊤
参数：x y : α；hx : x in I；h : y * x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem eq_top_of_unit_mem (x y : α) (hx : x ∈ I) (h : y * x = 1) : I = ⊤ :=
  eq_top_iff.2 fun z _ =>
    calc
      z * y * x ∈ I := I.mul_mem_left _ hx
      _ = z * (y * x) := mul_assoc z y x
      _ = z := by rw [h, mul_one]
/-
**Ideal.eq_top_of_isUnit_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_top_of_isUnit_mem {x} (hx : x in I) (h : IsUnit x) : I = ⊤
参数：hx : x in I；h : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.exists_left_inv`：IsUnit.exists_left_inv {a : M} (h : IsUnit a) : 
exists b, b * a = 1
· 使用定理 `Ideal.eq_top_of_unit_mem`：eq_top_of_unit_mem (x y : α) (hx : x in I) (h 
: y * x = 1) : I = ⊤
-/
theorem eq_top_of_isUnit_mem {x} (hx : x ∈ I) (h : IsUnit x) : I = ⊤ :=
  let ⟨y, hy⟩ := h.exists_left_inv
  eq_top_of_unit_mem I x y hx hy
/-
**Ideal.eq_top_iff_one** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.eq_top_of_unit_mem`：eq_top_of_unit_mem (x y : α) (hx : x in I) (h 
: y * x = 1) : I = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_top_iff_one : I = ⊤ ↔ (1 : α) ∈ I :=
  ⟨by rintro rfl; trivial, fun h => eq_top_of_unit_mem _ _ 1 h (by simp)⟩
/-
**Ideal.ne_top_iff_one** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
-/
theorem ne_top_iff_one : I ≠ ⊤ ↔ (1 : α) ∉ I :=
  not_congr I.eq_top_iff_one

section Lattice

variable {R : Type u} [Semiring R]

/-
**Ideal.mem_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_sup_left {S T : Ideal R} : forall {x : R}, x in S -> x in S ⊔ T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem mem_sup_left {S T : Ideal R} : ∀ {x : R}, x ∈ S → x ∈ S ⊔ T :=
  @le_sup_left _ _ S T
/-
**Ideal.mem_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_sup_right {S T : Ideal R} : forall {x : R}, x in T -> x in S ⊔ T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem mem_sup_right {S T : Ideal R} : ∀ {x : R}, x ∈ T → x ∈ S ⊔ T :=
  @le_sup_right _ _ S T
/-
**Ideal.mem_iSup_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_iSup_of_mem {ι : Sort*} {S : ι -> Ideal R} (i : ι) : forall {x : R}, x
 in S i -> x in iSup S
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem mem_iSup_of_mem {ι : Sort*} {S : ι → Ideal R} (i : ι) : ∀ {x : R}, x ∈ S i → x ∈ iSup S :=
  @le_iSup _ _ _ S _
/-
**Ideal.mem_sSup_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_sSup_of_mem {S : Set (Ideal R)} {s : Ideal R} (hs : s in S) : forall {
x : R}, x in s -> x in sSup S
参数：Ideal R；hs : s in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem mem_sSup_of_mem {S : Set (Ideal R)} {s : Ideal R} (hs : s ∈ S) :
    ∀ {x : R}, x ∈ s → x ∈ sSup S :=
  @le_sSup _ _ _ _ hs
/-
**Ideal.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ forall ⦃I⦄, I in s ->
 x in I
参数：Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
-/
theorem mem_sInf {s : Set (Ideal R)} {x : R} : x ∈ sInf s ↔ ∀ ⦃I⦄, I ∈ s → x ∈ I :=
  ⟨fun hx I his => hx I ⟨I, iInf_pos his⟩, fun H _I ⟨_J, hij⟩ => hij ▸ fun _S ⟨hj, hS⟩ => hS ▸ H hj⟩
/-
**Ideal.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_inf {I J : Ideal R} {x : R} : x in I ⊓ J ↔ x in I ∧ x in J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {I J : Ideal R} {x : R} : x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J :=
  Iff.rfl
/-
**Ideal.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_iInf {ι : Sort*} {I : ι -> Ideal R} {x : R} : x in iInf I ↔ forall i, 
x in I i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_iInf`：mem_iInf {ι} (p : ι -> Submodule R M) {x} : x in ⨅ i
, p i ↔ forall i, x in p i
-/
theorem mem_iInf {ι : Sort*} {I : ι → Ideal R} {x : R} : x ∈ iInf I ↔ ∀ i, x ∈ I i :=
  Submodule.mem_iInf _
/-
**Ideal.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
-/
theorem mem_bot {x : R} : x ∈ (⊥ : Ideal R) ↔ x = 0 :=
  Submodule.mem_bot _

end Lattice

end Ideal

end Semiring

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

/-- All ideals in a division (semi)ring are trivial. -/
/-
**Ideal.eq_bot_or_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_bot_or_top : I = ⊥ ∨ I = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Ideal.ne_top_iff_one`：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I

--- 原说明 ---
All ideals in a division (semi)ring are trivial.
-/
theorem eq_bot_or_top : I = ⊥ ∨ I = ⊤ := by
  rw [or_iff_not_imp_right]
  change _ ≠ _ → _
  rw [Ideal.ne_top_iff_one]
  intro h1
  rw [eq_bot_iff]
  intro r hr
  by_cases H : r = 0; · simpa
  simpa [H, h1] using I.mul_mem_left r⁻¹ hr

end Ideal

end DivisionSemiring

