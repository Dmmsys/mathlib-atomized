/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Integer Complement

We define the complement of the integers in the complex plane and give some basic lemmas about it.
We also show that the upper half plane embeds into the integer complement.

-/

@[expose] public section

open UpperHalfPlane

/-- The complement of the integers in `ℂ` -/
/-
**Complex.integerComplement** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Complex.integerComplement
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement of the integers in `ℂ`
-/
def Complex.integerComplement := (Set.range ((↑) : ℤ → ℂ))ᶜ

namespace Complex

local notation "ℂ_ℤ" => integerComplement

/-
**Complex.integerComplement_eq** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：integerComplement_eq : Complex_Int = {z : Complex | ¬ exists (n : Int), n 
= z}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integerComplement_eq : ℂ_ℤ = {z : ℂ | ¬ ∃ (n : ℤ), n = z} := rfl
/-
**Complex.mem_integerComplement_iff** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：mem_integerComplement_iff {x : Complex} : x in Complex_Int ↔ ¬ exists (n :
 Int), n = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_integerComplement_iff {x : ℂ} : x ∈ ℂ_ℤ ↔ ¬ ∃ (n : ℤ), n = x := Iff.rfl

@[deprecated (since := "2026-01-29")]
alias integerComplement.mem_iff := mem_integerComplement_iff

@[simp]
/-
**Complex._root_.UpperHalfPlane.coe_mem_integerComplement** 是 Mathlib 中的一个引理，位于命
名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.UpperHalfPlane.coe_mem_integerComplement (z : ℍ) : ↑z ∈ ℂ_ℤ :=
  not_exists.mpr fun x hx ↦ ne_intCast z x hx.symm

@[simp]
/-
**Complex.add_intCast_mem_integerComplement** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：add_intCast_mem_integerComplement {x : Complex} (a : Int) : x + (a : Compl
ex) in Complex_Int ↔ x in Complex_Int
参数：a : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
-/
lemma add_intCast_mem_integerComplement {x : ℂ} (a : ℤ) : x + (a : ℂ) ∈ ℂ_ℤ ↔ x ∈ ℂ_ℤ := by
  simp only [mem_integerComplement_iff, not_iff_not]
  exact ⟨(Exists.elim · fun n hn ↦ ⟨n - a, by simp [hn]⟩),
    (Exists.elim · fun n hn ↦ ⟨n + a, by simp [hn]⟩)⟩

@[deprecated (since := "2026-01-29")]
alias integerComplement.add_coe_int_mem := add_intCast_mem_integerComplement
/-
**Complex.integerComplement.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex.integerCo
mplement`。
形式化陈述：∀ {x : ℂ}, x ∈ Complex.integerComplement → x ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
-/
lemma integerComplement.ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) : x ≠ 0 :=
  fun hx' ↦ hx ⟨0, by exact_mod_cast hx'.symm⟩
/-
**Complex.integerComplement_add_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：integerComplement_add_ne_zero {x : Complex} (hx : x in Complex_Int) (a : I
nt) : x + (a : Complex) != 0
参数：hx : x in Complex_Int；a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.integerComplement.ne_zero`：∀ {x : ℂ}, x ∈ Complex.integerComplem
ent → x ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Complex.add_intCast_mem_integerComplement`：add_intCast_mem_integerComple
ment {x : Complex} (a : Int) : x + (a : Complex) in Complex_Int ↔ x in Complex_I
nt
-/
lemma integerComplement_add_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) (a : ℤ) : x + (a : ℂ) ≠ 0 :=
  integerComplement.ne_zero ((add_intCast_mem_integerComplement a).mpr hx)
/-
**Complex.integerComplement.ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex.integerCom
plement`。
形式化陈述：∀ {x : ℂ}, x ∈ Complex.integerComplement → x ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
-/
lemma integerComplement.ne_one {x : ℂ} (hx : x ∈ ℂ_ℤ) : x ≠ 1 :=
  fun hx' ↦ hx ⟨1, by exact_mod_cast hx'.symm⟩
/-
**Complex.integerComplement_pow_two_ne_pow_two** 是 Mathlib 中的一个引理，位于命名空间 `Comple
x`。
形式化陈述：integerComplement_pow_two_ne_pow_two {x : Complex} (hx : x in Complex_Int)
 (n : Int) : x ^ 2 != n ^ 2
参数：hx : x in Complex_Int；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma integerComplement_pow_two_ne_pow_two {x : ℂ} (hx : x ∈ ℂ_ℤ) (n : ℤ) : x ^ 2 ≠ n ^ 2 := by
  have := not_exists.mp hx n
  have := not_exists.mp hx (-n)
  simp_all [sq_eq_sq_iff_eq_or_eq_neg, eq_comm]
/-
**Complex.upperHalfPlane_inter_integerComplement** 是 Mathlib 中的一个引理，位于命名空间 `Comp
lex`。
形式化陈述：upperHalfPlane_inter_integerComplement : {z : Complex | 0 < z.im} inter Co
mplex_Int = {z : Complex | 0 < z.im}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `UpperHalfPlane.coe_mem_integerComplement`：∀ (z : UpperHalfPlane), ↑z ∈ C
omplex.integerComplement
-/
lemma upperHalfPlane_inter_integerComplement :
    {z : ℂ | 0 < z.im} ∩ ℂ_ℤ = {z : ℂ | 0 < z.im} := by
  apply Set.inter_eq_self_of_subset_left
  exact fun z hz ↦ UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩
/-
**Complex._root_.UpperHalfPlane.int_div_mem_integerComplement** 是 Mathlib 中的一个引理
，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.UpperHalfPlane.int_div_mem_integerComplement (z : ℍ) {n : ℤ} (hn : n ≠ 0) :
    n / (z : ℂ) ∈ ℂ_ℤ := by
  rintro ⟨_, hm⟩
  have : (n / (z : ℂ)).im ≠ 0 := by simp [div_im, z.ne_zero, hn, z.im_ne_zero]
  simpa [← hm]

end Complex

