/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Zify

/-!
# The length function, reduced words, and descents

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

Given any element $w \in W$, its *length* (`CoxeterSystem.length`), denoted $\ell(w)$, is the
minimum number $\ell$ such that $w$ can be written as a product of a sequence of $\ell$ simple
reflections:
$$w = s_{i_1} \cdots s_{i_\ell}.$$
We prove for all $w_1, w_2 \in W$ that $\ell (w_1 w_2) \leq \ell (w_1) + \ell (w_2)$
and that $\ell (w_1 w_2)$ has the same parity as $\ell (w_1) + \ell (w_2)$.

We define a *reduced word* (`CoxeterSystem.IsReduced`) for an element $w \in W$ to be a way of
writing $w$ as a product of exactly $\ell(w)$ simple reflections. Every element of $W$ has a reduced
word.

We say that $i \in B$ is a *left descent* (`CoxeterSystem.IsLeftDescent`) of $w \in W$ if
$\ell(s_i w) < \ell(w)$. We show that if $i$ is a left descent of $w$, then
$\ell(s_i w) + 1 = \ell(w)$. On the other hand, if $i$ is not a left descent of $w$, then
$\ell(s_i w) = \ell(w) + 1$. We similarly define right descents (`CoxeterSystem.IsRightDescent`) and
prove analogous results.

## Main definitions

* `cs.length`
* `cs.IsReduced`
* `cs.IsLeftDescent`
* `cs.IsRightDescent`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CoxeterSystem

open List Matrix Function

variable {B W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd

/-! ### Length -/

/-
**CoxeterSystem.exists_word_with_prod** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Length
-/
private theorem exists_word_with_prod (w : W) : ∃ n ω, n = ω.length ∧ π ω = w := by
  rcases cs.wordProd_surjective w with ⟨ω, rfl⟩
  use ω.length, ω

open scoped Classical in
/-- The length of `w`; i.e., the minimum number of simple reflections that
must be multiplied to form `w`. -/
/-
**CoxeterSystem.length** 是 Mathlib 中的一个定义，位于命名空间 `CoxeterSystem`。
形式化陈述：{B : Type u_1} → {W : Type u_2} → [inst : Group W] → {M : CoxeterMatrix B}
 → CoxeterSystem M W → W → ℕ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Length.0.CoxeterSystem.exists_word_
with_prod`：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B
} (cs : CoxeterSystem M W) (w : W),   ∃ n ω, n = ω.length ∧ cs.wordProd…

--- 原说明 ---
The length of `w`; i.e., the minimum number of simple reflections that
must be multiplied to form `w`.
-/
@[no_expose] noncomputable def length (w : W) : ℕ := Nat.find (cs.exists_word_with_prod w)

local prefix:100 "ℓ " => cs.length

/-- The proposition that `ω` is reduced; that is, it has minimal length among all words that
represent the same element of `W`. -/
/-
**CoxeterSystem.IsReduced** 是 Mathlib 中的一个定义，位于命名空间 `CoxeterSystem`。
形式化陈述：IsReduced (ω : List B) : Prop
参数：ω : List B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that `ω` is reduced; that is, it has minimal length among all wo
rds that
represent the same element of `W`.
-/
def IsReduced (ω : List B) : Prop := ℓ (π ω) = ω.length
/-
**CoxeterSystem.IsReduced.eq** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem.IsReduced`
。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} (cs
 : CoxeterSystem M W) {ω : List B},   cs.IsReduced ω → cs.length (cs.wordProd ω)
 = ω.length
参数：cs : CoxeterSystem M W；cs.wordProd ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsReduced.eq {ω : List B} (hω : cs.IsReduced ω) : ℓ (π ω) = ω.length := hω
/-
**CoxeterSystem.exists_isReduced** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：exists_isReduced (w : W) : exists ω : List B, cs.IsReduced ω ∧ w = π ω
参数：w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Length.0.CoxeterSystem.exists_word_
with_prod`：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B
} (cs : CoxeterSystem M W) (w : W),   ∃ n ω, n = ω.length ∧ cs.wordProd…
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem exists_isReduced (w : W) : ∃ ω : List B, cs.IsReduced ω ∧ w = π ω := by
  classical
  obtain ⟨ω, hω, rfl⟩ := Nat.find_spec (cs.exists_word_with_prod w)
  exact ⟨ω, hω, rfl⟩

@[deprecated (since := "2026-03-25")] alias exists_reduced_word := exists_isReduced
@[deprecated (since := "2026-03-25")] alias exists_reduced_word' := exists_isReduced
/-
**CoxeterSystem.length_wordProd_le** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_wordProd_le (ω : List B) : ℓ (π ω) <= ω.length
参数：ω : List B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Length.0.CoxeterSystem.exists_word_
with_prod`：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B
} (cs : CoxeterSystem M W) (w : W),   ∃ n ω, n = ω.length ∧ cs.wordProd…
-/
theorem length_wordProd_le (ω : List B) : ℓ (π ω) ≤ ω.length := by
  classical
  exact Nat.find_min' (cs.exists_word_with_prod (π ω)) ⟨ω, rfl, rfl⟩
/-
**CoxeterSystem.length_one** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} (cs
 : CoxeterSystem M W), cs.length 1 = 0
参数：cs : CoxeterSystem M W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `CoxeterSystem.length_wordProd_le`：length_wordProd_le (ω : List B) : ℓ (π
 ω) <= ω.length
-/
@[simp] theorem length_one : ℓ (1 : W) = 0 := Nat.eq_zero_of_le_zero (cs.length_wordProd_le [])

@[simp]
/-
**CoxeterSystem.length_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_eq_zero_iff {w : W} : ℓ w = 0 ↔ w = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoxeterSystem.exists_isReduced`：exists_isReduced (w : W) : exists ω : Li
st B, cs.IsReduced ω ∧ w = π ω
· 使用定理 `List.eq_nil_of_length_eq_zero`：∀ {α : Type u_1} {l : List α}, l.length =
 0 → l = []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.wordProd_nil`：∀ {B : Type u_1} {W : Type u_3} [inst : Grou
p W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W), cs.wordProd [] = 1
· 使用定理 `CoxeterSystem.length_one`：∀ {B : Type u_1} {W : Type u_2} [inst : Group 
W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W), cs.length 1 = 0
-/
theorem length_eq_zero_iff {w : W} : ℓ w = 0 ↔ w = 1 := by
  constructor
  · intro h
    rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    have : ω = [] := eq_nil_of_length_eq_zero (hω.symm.trans h)
    rw [this, wordProd_nil]
  · rintro rfl
    exact cs.length_one

@[simp]
/-
**CoxeterSystem.length_inv** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_inv (w : W) : ℓ (w⁻¹) = ℓ w
参数：w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_antisymm`：∀ {n m : ℕ}, n ≤ m → m ≤ n → n = m
· 使用定理 `CoxeterSystem.exists_isReduced`：exists_isReduced (w : W) : exists ω : Li
st B, cs.IsReduced ω ∧ w = π ω
· 使用定理 `CoxeterSystem.length_wordProd_le`：length_wordProd_le (ω : List B) : ℓ (π
 ω) <= ω.length
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `CoxeterSystem.wordProd_reverse`：∀ {B : Type u_1} {W : Type u_3} [inst : 
Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.wordP
rod ω.reverse = (cs.…
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem length_inv (w : W) : ℓ (w⁻¹) = ℓ w := by
  apply Nat.le_antisymm
  · rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    have := cs.length_wordProd_le ω.reverse
    rwa [wordProd_reverse, length_reverse, ← hω] at this
  · rcases cs.exists_isReduced w⁻¹ with ⟨ω, hω, h'ω⟩
    have := cs.length_wordProd_le ω.reverse
    rwa [wordProd_reverse, length_reverse, ← h'ω, ← hω, inv_inv, ← h'ω] at this
/-
**CoxeterSystem.length_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_mul_le (w₁ w₂ : W) : ℓ (w₁ * w₂) <= ℓ w₁ + ℓ w₂
参数：w₁ w₂ : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoxeterSystem.exists_isReduced`：exists_isReduced (w : W) : exists ω : Li
st B, cs.IsReduced ω ∧ w = π ω
· 使用定理 `CoxeterSystem.length_wordProd_le`：length_wordProd_le (ω : List B) : ℓ (π
 ω) <= ω.length
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CoxeterSystem.IsReduced.eq`：∀ {B : Type u_1} {W : Type u_2} [inst : Grou
p W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) {ω : List B},   cs.IsReduced
 ω → cs.length (…
· 使用定理 `CoxeterSystem.wordProd_append`：wordProd_append (ω ω' : List B) : π (ω ++
 ω') = π ω * π ω'
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem length_mul_le (w₁ w₂ : W) : ℓ (w₁ * w₂) ≤ ℓ w₁ + ℓ w₂ := by
  rcases cs.exists_isReduced w₁ with ⟨ω₁, hω₁, rfl⟩
  rcases cs.exists_isReduced w₂ with ⟨ω₂, hω₂, rfl⟩
  have := cs.length_wordProd_le (ω₁ ++ ω₂)
  simpa [hω₁.eq, hω₂.eq, wordProd_append] using this
/-
**CoxeterSystem.length_le_length_mul_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Coxeter
System`。
形式化陈述：length_le_length_mul_add_left (w₁ w₂ : W) : ℓ w₂ <= ℓ (w₁ * w₂) + ℓ w₁
参数：w₁ w₂ : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CoxeterSystem.length_inv`：length_inv (w : W) : ℓ (w⁻¹) = ℓ w
· 使用定理 `CoxeterSystem.length_mul_le`：length_mul_le (w₁ w₂ : W) : ℓ (w₁ * w₂) <= 
ℓ w₁ + ℓ w₂
-/
theorem length_le_length_mul_add_left (w₁ w₂ : W) : ℓ w₂ ≤ ℓ (w₁ * w₂) + ℓ w₁ := by
  simpa [add_comm] using cs.length_mul_le w₁⁻¹ (w₁ * w₂)
/-
**CoxeterSystem.length_le_length_mul_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Coxete
rSystem`。
形式化陈述：length_le_length_mul_add_right (w₁ w₂ : W) : ℓ w₁ <= ℓ (w₁ * w₂) + ℓ w₂
参数：w₁ w₂ : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `CoxeterSystem.length_inv`：length_inv (w : W) : ℓ (w⁻¹) = ℓ w
· 使用定理 `CoxeterSystem.length_mul_le`：length_mul_le (w₁ w₂ : W) : ℓ (w₁ * w₂) <= 
ℓ w₁ + ℓ w₂
-/
theorem length_le_length_mul_add_right (w₁ w₂ : W) : ℓ w₁ ≤ ℓ (w₁ * w₂) + ℓ w₂ := by
  simpa using cs.length_mul_le (w₁ * w₂) w₂⁻¹

@[deprecated length_le_length_mul_add_right (since := "2026-03-25")]
/-
**CoxeterSystem.length_mul_ge_length_sub_length** 是 Mathlib 中的一个定理，位于命名空间 `Coxet
erSystem`。
形式化陈述：length_mul_ge_length_sub_length (w₁ w₂ : W) : ℓ w₁ - ℓ w₂ <= ℓ (w₁ * w₂)
参数：w₁ w₂ : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_le_iff_le_add`：∀ {a b c : ℕ}, a - b ≤ c ↔ a ≤ c + b
· 使用定理 `CoxeterSystem.length_le_length_mul_add_right`：length_le_length_mul_add_r
ight (w₁ w₂ : W) : ℓ w₁ <= ℓ (w₁ * w₂) + ℓ w₂
-/
theorem length_mul_ge_length_sub_length (w₁ w₂ : W) : ℓ w₁ - ℓ w₂ ≤ ℓ (w₁ * w₂) := by
  rw [Nat.sub_le_iff_le_add]; exact length_le_length_mul_add_right ..

@[deprecated length_le_length_mul_add_left (since := "2026-03-25")]
/-
**CoxeterSystem.length_mul_ge_length_sub_length'** 是 Mathlib 中的一个定理，位于命名空间 `Coxe
terSystem`。
形式化陈述：length_mul_ge_length_sub_length' (w₁ w₂ : W) : ℓ w₂ - ℓ w₁ <= ℓ (w₁ * w₂)
参数：w₁ w₂ : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_le_iff_le_add`：∀ {a b c : ℕ}, a - b ≤ c ↔ a ≤ c + b
· 使用定理 `CoxeterSystem.length_le_length_mul_add_left`：length_le_length_mul_add_le
ft (w₁ w₂ : W) : ℓ w₂ <= ℓ (w₁ * w₂) + ℓ w₁
-/
theorem length_mul_ge_length_sub_length' (w₁ w₂ : W) : ℓ w₂ - ℓ w₁ ≤ ℓ (w₁ * w₂) := by
  rw [Nat.sub_le_iff_le_add]; exact length_le_length_mul_add_left ..

@[deprecated "use `length_le_length_mul_add_left` and `length_le_length_mul_add_right"
(since := "2026-03-25")]
/-
**CoxeterSystem.length_mul_ge_max** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_mul_ge_max (w₁ w₂ : W) : max (ℓ w₁ - ℓ w₂) (ℓ w₂ - ℓ w₁) <= ℓ (w₁ *
 w₂)
参数：w₁ w₂ : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `CoxeterSystem.length_mul_ge_length_sub_length`：length_mul_ge_length_sub_
length (w₁ w₂ : W) : ℓ w₁ - ℓ w₂ <= ℓ (w₁ * w₂)
· 使用定理 `CoxeterSystem.length_mul_ge_length_sub_length'`：length_mul_ge_length_sub
_length' (w₁ w₂ : W) : ℓ w₂ - ℓ w₁ <= ℓ (w₁ * w₂)
-/
theorem length_mul_ge_max (w₁ w₂ : W) : max (ℓ w₁ - ℓ w₂) (ℓ w₂ - ℓ w₁) ≤ ℓ (w₁ * w₂) :=
  max_le (length_mul_ge_length_sub_length ..) (length_mul_ge_length_sub_length' ..)

/-- The homomorphism that sends each element `w : W` to the parity of the length of `w`.
(See `lengthParity_eq_ofAdd_length`.) -/
/-
**CoxeterSystem.lengthParity** 是 Mathlib 中的一个定义，位于命名空间 `CoxeterSystem`。
形式化陈述：lengthParity : W ->* Multiplicative (ZMod 2)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism that sends each element `w : W` to the parity of the length of 
`w`.
(See `lengthParity_eq_ofAdd_length`.)
-/
def lengthParity : W →* Multiplicative (ZMod 2) := cs.lift ⟨fun _ ↦ Multiplicative.ofAdd 1, by
  simp_rw [CoxeterMatrix.IsLiftable, ← ofAdd_add, (by decide : (1 + 1 : ZMod 2) = 0)]
  simp⟩
/-
**CoxeterSystem.lengthParity_simple** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：lengthParity_simple (i : B) : cs.lengthParity (s i) = Multiplicative.ofAdd
 1
参数：i : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoxeterSystem.lift_apply_simple`：lift_apply_simple {G : Type*} [Monoid G
] {f : B -> G} (hf : IsLiftable M f) (i : B) : cs.lift ⟨f, hf⟩ (s i) = f i
-/
theorem lengthParity_simple (i : B) :
    cs.lengthParity (s i) = Multiplicative.ofAdd 1 := cs.lift_apply_simple _ _
/-
**CoxeterSystem.lengthParity_comp_simple** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSyste
m`。
形式化陈述：lengthParity_comp_simple : cs.lengthParity ∘ cs.simple = fun _ => Multipli
cative.ofAdd 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CoxeterSystem.lengthParity_simple`：lengthParity_simple (i : B) : cs.leng
thParity (s i) = Multiplicative.ofAdd 1
-/
theorem lengthParity_comp_simple :
    cs.lengthParity ∘ cs.simple = fun _ ↦ Multiplicative.ofAdd 1 := funext cs.lengthParity_simple
/-
**CoxeterSystem.lengthParity_eq_ofAdd_length** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterS
ystem`。
形式化陈述：lengthParity_eq_ofAdd_length (w : W) : cs.lengthParity w = Multiplicative.
ofAdd (↑(ℓ w))
参数：w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoxeterSystem.exists_isReduced`：exists_isReduced (w : W) : exists ω : Li
st B, cs.IsReduced ω ∧ w = π ω
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.wordProd.eq_1`：∀ {B : Type u_1} {W : Type u_3} [inst : Gro
up W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.wordProd
 ω = (List.map cs…
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `CoxeterSystem.lengthParity_comp_simple`：lengthParity_comp_simple : cs.le
ngthParity ∘ cs.simple = fun _ => Multiplicative.ofAdd 1
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ofAdd_nsmul`：ofAdd_nsmul [AddMonoid α] (n : Nat) (a : α) : ofAdd (n • a)
 = ofAdd a ^ n
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
-/
theorem lengthParity_eq_ofAdd_length (w : W) :
    cs.lengthParity w = Multiplicative.ofAdd (↑(ℓ w)) := by
  rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
  rw [hω, wordProd, map_list_prod, List.map_map, lengthParity_comp_simple, map_const',
    prod_replicate, ← ofAdd_nsmul, nsmul_one]
/-
**CoxeterSystem.length_mul_mod_two** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_mul_mod_two (w₁ w₂ : W) : ℓ (w₁ * w₂) % 2 = (ℓ w₁ + ℓ w₂) % 2
参数：w₁ w₂ : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_eq_natCast_iff'`：natCast_eq_natCast_iff' (a b c : Nat) : (a
 : ZMod c) = (b : ZMod c) ↔ a % c = b % c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CoxeterSystem.lengthParity_eq_ofAdd_length`：lengthParity_eq_ofAdd_length
 (w : W) : cs.lengthParity w = Multiplicative.ofAdd (↑(ℓ w))
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem length_mul_mod_two (w₁ w₂ : W) : ℓ (w₁ * w₂) % 2 = (ℓ w₁ + ℓ w₂) % 2 := by
  rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_add]
  simpa only [lengthParity_eq_ofAdd_length, ofAdd_add] using! map_mul cs.lengthParity w₁ w₂

@[simp]
/-
**CoxeterSystem.length_simple** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_simple (i : B) : ℓ (s i) = 1
参数：i : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_antisymm`：∀ {n m : ℕ}, n ≤ m → m ≤ n → n = m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.wordProd_singleton`：∀ {B : Type u_1} {W : Type u_3} [inst 
: Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (i : B),   cs.wordProd
 [i] = cs.simple i
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CoxeterSystem.length_wordProd_le`：length_wordProd_le (ω : List B) : ℓ (π
 ω) <= ω.length
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `CoxeterSystem.lengthParity_eq_ofAdd_length`：lengthParity_eq_ofAdd_length
 (w : W) : cs.lengthParity w = Multiplicative.ofAdd (↑(ℓ w))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CoxeterSystem.lengthParity_simple`：lengthParity_simple (i : B) : cs.leng
thParity (s i) = Multiplicative.ofAdd 1
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
-/
theorem length_simple (i : B) : ℓ (s i) = 1 := by
  apply Nat.le_antisymm
  · simpa using cs.length_wordProd_le [i]
  · by_contra! length_lt_one
    have : cs.lengthParity (s i) = Multiplicative.ofAdd 0 := by
      rw [lengthParity_eq_ofAdd_length, Nat.lt_one_iff.mp length_lt_one, Nat.cast_zero]
    have : Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd 1 :=
      this.symm.trans (cs.lengthParity_simple i)
    contradiction
/-
**CoxeterSystem.length_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_eq_one_iff {w : W} : ℓ w = 1 ↔ exists i : B, w = s i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoxeterSystem.exists_isReduced`：exists_isReduced (w : W) : exists ω : Li
st B, cs.IsReduced ω ∧ w = π ω
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_eq_one_iff`：∀ {α : Type u_1} {l : List α}, l.length = 1 ↔ ∃ 
a, l = [a]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CoxeterSystem.wordProd_singleton`：∀ {B : Type u_1} {W : Type u_3} [inst 
: Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (i : B),   cs.wordProd
 [i] = cs.simple i
· 使用定理 `CoxeterSystem.length_simple`：length_simple (i : B) : ℓ (s i) = 1
-/
theorem length_eq_one_iff {w : W} : ℓ w = 1 ↔ ∃ i : B, w = s i := by
  constructor
  · intro h
    rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    rcases List.length_eq_one_iff.mp (hω.symm.trans h) with ⟨i, rfl⟩
    exact ⟨i, cs.wordProd_singleton i⟩
  · rintro ⟨i, rfl⟩
    exact cs.length_simple i
/-
**CoxeterSystem.length_mul_simple_ne** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_mul_simple_ne (w : W) (i : B) : ℓ (w * s i) != ℓ w
参数：w : W；i : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoxeterSystem.length_mul_mod_two`：length_mul_mod_two (w₁ w₂ : W) : ℓ (w₁
 * w₂) % 2 = (ℓ w₁ + ℓ w₂) % 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.length_simple`：length_simple (i : B) : ℓ (s i) = 1
-/
theorem length_mul_simple_ne (w : W) (i : B) : ℓ (w * s i) ≠ ℓ w := by
  intro eq
  have length_mod_two := cs.length_mul_mod_two w (s i)
  rw [eq, length_simple] at length_mod_two
  lia
/-
**CoxeterSystem.length_simple_mul_ne** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_simple_mul_ne (w : W) (i : B) : ℓ (s i * w) != ℓ w
参数：w : W；i : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CoxeterSystem.length_inv`：length_inv (w : W) : ℓ (w⁻¹) = ℓ w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `CoxeterSystem.inv_simple`：inv_simple (i : B) : (s i)⁻¹ = s i
· 使用定理 `CoxeterSystem.length_mul_simple_ne`：length_mul_simple_ne (w : W) (i : B)
 : ℓ (w * s i) != ℓ w
-/
theorem length_simple_mul_ne (w : W) (i : B) : ℓ (s i * w) ≠ ℓ w := by
  rw [← length_inv]
  simpa using cs.length_mul_simple_ne w⁻¹ i
/-
**CoxeterSystem.length_mul_simple** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_mul_simple (w : W) (i : B) : ℓ (w * s i) = ℓ w + 1 ∨ ℓ (w * s i) + 
1 = ℓ w
参数：w : W；i : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `CoxeterSystem.length_mul_simple_ne`：length_mul_simple_ne (w : W) (i : B)
 : ℓ (w * s i) != ℓ w
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `CoxeterSystem.length_simple`：length_simple (i : B) : ℓ (s i) = 1
· 使用定理 `CoxeterSystem.length_le_length_mul_add_right`：length_le_length_mul_add_r
ight (w₁ w₂ : W) : ℓ w₁ <= ℓ (w₁ * w₂) + ℓ w₂
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `CoxeterSystem.length_mul_le`：length_mul_le (w₁ w₂ : W) : ℓ (w₁ * w₂) <= 
ℓ w₁ + ℓ w₂
-/
theorem length_mul_simple (w : W) (i : B) : ℓ (w * s i) = ℓ w + 1 ∨ ℓ (w * s i) + 1 = ℓ w := by
  rcases (cs.length_mul_simple_ne w i).lt_or_gt with h | h <;> rw [← Nat.add_one_le_iff] at h
  · refine .inr (h.antisymm ?_)
    simpa using cs.length_le_length_mul_add_right w (s i)
  · refine .inl (h.antisymm' ?_)
    simpa using cs.length_mul_le w (s i)
/-
**CoxeterSystem.length_simple_mul** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：length_simple_mul (w : W) (i : B) : ℓ (s i * w) = ℓ w + 1 ∨ ℓ (s i * w) + 
1 = ℓ w
参数：w : W；i : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoxeterSystem.length_mul_simple`：length_mul_simple (w : W) (i : B) : ℓ (
w * s i) = ℓ w + 1 ∨ ℓ (w * s i) + 1 = ℓ w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.length_inv`：length_inv (w : W) : ℓ (w⁻¹) = ℓ w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `CoxeterSystem.inv_simple`：inv_simple (i : B) : (s i)⁻¹ = s i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_simple_mul (w : W) (i : B) : ℓ (s i * w) = ℓ w + 1 ∨ ℓ (s i * w) + 1 = ℓ w := by
  have := cs.length_mul_simple w⁻¹ i
  rwa [(by simp : w⁻¹ * (s i) = ((s i) * w)⁻¹), length_inv, length_inv] at this

/-! ### Reduced words -/

@[simp]
/-
**CoxeterSystem.isReduced_reverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：isReduced_reverse_iff (ω : List B) : cs.IsReduced (ω.reverse) ↔ cs.IsReduc
ed ω
参数：ω : List B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CoxeterSystem.wordProd_reverse`：∀ {B : Type u_1} {W : Type u_3} [inst : 
Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.wordP
rod ω.reverse = (cs.…
· 使用定理 `CoxeterSystem.length_inv`：length_inv (w : W) : ℓ (w⁻¹) = ℓ w
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Reduced words
-/
theorem isReduced_reverse_iff (ω : List B) : cs.IsReduced (ω.reverse) ↔ cs.IsReduced ω := by
  simp [IsReduced]
/-
**CoxeterSystem.IsReduced.reverse** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem.IsRed
uced`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} {cs
 : CoxeterSystem M W} {ω : List B},   cs.IsReduced ω → cs.IsReduced ω.reverse
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CoxeterSystem.isReduced_reverse_iff`：isReduced_reverse_iff (ω : List B) 
: cs.IsReduced (ω.reverse) ↔ cs.IsReduced ω
-/
theorem IsReduced.reverse {cs : CoxeterSystem M W} {ω : List B}
    (hω : cs.IsReduced ω) : cs.IsReduced (ω.reverse) :=
  (cs.isReduced_reverse_iff ω).mpr hω
/-
**CoxeterSystem.isReduced_take_and_drop** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isReduced_take_and_drop {ω : List B} (hω : cs.IsReduced ω) (j : ℕ) :
    cs.IsReduced (ω.take j) ∧ cs.IsReduced (ω.drop j) := by
  have h₁ : ℓ (π (ω.take j)) ≤ (ω.take j).length := cs.length_wordProd_le (ω.take j)
  have h₂ : ℓ (π (ω.drop j)) ≤ (ω.drop j).length := cs.length_wordProd_le (ω.drop j)
  have h₃ := calc
    (ω.take j).length + (ω.drop j).length
    _ = ω.length := by rw [← List.length_append, ω.take_append_drop j]
    _ = ℓ (π ω) := hω.symm
    _ = ℓ (π (ω.take j) * π (ω.drop j)) := by rw [← cs.wordProd_append, ω.take_append_drop j]
    _ ≤ ℓ (π (ω.take j)) + ℓ (π (ω.drop j)) := cs.length_mul_le _ _
  unfold IsReduced
  lia
/-
**CoxeterSystem.IsReduced.take** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem.IsReduce
d`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} {cs
 : CoxeterSystem M W} {ω : List B},   cs.IsReduced ω → ∀ (j : ℕ), cs.IsReduced (
List.take j ω)
参数：j : ℕ；List.take j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Length.0.CoxeterSystem.isReduced_ta
ke_and_drop`：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix
 B} (cs : CoxeterSystem M W) {ω : List B},   cs.IsReduced ω → ∀ (j : ℕ), …
-/
theorem IsReduced.take {cs : CoxeterSystem M W} {ω : List B} (hω : cs.IsReduced ω) (j : ℕ) :
    cs.IsReduced (ω.take j) :=
  (isReduced_take_and_drop _ hω _).1
/-
**CoxeterSystem.IsReduced.drop** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem.IsReduce
d`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} {cs
 : CoxeterSystem M W} {ω : List B},   cs.IsReduced ω → ∀ (j : ℕ), cs.IsReduced (
List.drop j ω)
参数：j : ℕ；List.drop j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Length.0.CoxeterSystem.isReduced_ta
ke_and_drop`：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix
 B} (cs : CoxeterSystem M W) {ω : List B},   cs.IsReduced ω → ∀ (j : ℕ), …
-/
theorem IsReduced.drop {cs : CoxeterSystem M W} {ω : List B} (hω : cs.IsReduced ω) (j : ℕ) :
    cs.IsReduced (ω.drop j) :=
  (isReduced_take_and_drop _ hω _).2
/-
**CoxeterSystem.not_isReduced_alternatingWord** 是 Mathlib 中的一个定理，位于命名空间 `Coxeter
System`。
形式化陈述：not_isReduced_alternatingWord (i i' : B) {m : Nat} (hM : M i i' != 0) (hm 
: m > M i i') : ¬cs.IsReduced (alternatingWord i i' m)
参数：i i' : B；hM : M i i' != 0；hm : m > M i i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 66 条，此处仅展示前 30 条）
-/
theorem not_isReduced_alternatingWord (i i' : B) {m : ℕ} (hM : M i i' ≠ 0) (hm : m > M i i') :
    ¬cs.IsReduced (alternatingWord i i' m) := by
  induction hm with
  | refl => -- Base case; m = M i i' + 1
    suffices h : ℓ (π (alternatingWord i i' (M i i' + 1))) < M i i' + 1 by
      unfold IsReduced
      rw [Nat.succ_eq_add_one, length_alternatingWord]
      lia
    have : M i i' + 1 ≤ M i i' * 2 := by linarith [Nat.one_le_iff_ne_zero.mpr hM]
    rw [cs.prod_alternatingWord_eq_prod_alternatingWord_sub i i' _ this]
    have : M i i' * 2 - (M i i' + 1) = M i i' - 1 := by lia
    rw [this]
    calc
      ℓ (π (alternatingWord i' i (M i i' - 1)))
      _ ≤ (alternatingWord i' i (M i i' - 1)).length := cs.length_wordProd_le _
      _ = M i i' - 1 := length_alternatingWord _ _ _
      _ ≤ M i i' := Nat.sub_le _ _
      _ < M i i' + 1 := Nat.lt_succ_self _
  | step m ih => -- Inductive step
    contrapose ih
    rw [alternatingWord_succ'] at ih
    apply IsReduced.drop (j := 1) at ih
    simpa using ih

/-! ### Descents -/

/-- The proposition that `i` is a left descent of `w`; that is, $\ell(s_i w) < \ell(w)$. -/
/-
**CoxeterSystem.IsLeftDescent** 是 Mathlib 中的一个定义，位于命名空间 `CoxeterSystem`。
形式化陈述：IsLeftDescent (w : W) (i : B) : Prop
参数：w : W；i : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that `i` is a left descent of `w`; that is, $\ell(s_i w) < \ell(
w)$.
-/
def IsLeftDescent (w : W) (i : B) : Prop := ℓ (s i * w) < ℓ w

/-- The proposition that `i` is a right descent of `w`; that is, $\ell(w s_i) < \ell(w)$. -/
/-
**CoxeterSystem.IsRightDescent** 是 Mathlib 中的一个定义，位于命名空间 `CoxeterSystem`。
形式化陈述：IsRightDescent (w : W) (i : B) : Prop
参数：w : W；i : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that `i` is a right descent of `w`; that is, $\ell(w s_i) < \ell
(w)$.
-/
def IsRightDescent (w : W) (i : B) : Prop := ℓ (w * s i) < ℓ w
/-
**CoxeterSystem.not_isLeftDescent_one** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：not_isLeftDescent_one (i : B) : ¬cs.IsLeftDescent 1 i
参数：i : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `CoxeterSystem.length_simple`：length_simple (i : B) : ℓ (s i) = 1
· 使用定理 `CoxeterSystem.length_one`：∀ {B : Type u_1} {W : Type u_2} [inst : Group 
W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W), cs.length 1 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_isLeftDescent_one (i : B) : ¬cs.IsLeftDescent 1 i := by simp [IsLeftDescent]
/-
**CoxeterSystem.not_isRightDescent_one** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`
。
形式化陈述：not_isRightDescent_one (i : B) : ¬cs.IsRightDescent 1 i
参数：i : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `CoxeterSystem.length_simple`：length_simple (i : B) : ℓ (s i) = 1
· 使用定理 `CoxeterSystem.length_one`：∀ {B : Type u_1} {W : Type u_2} [inst : Group 
W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W), cs.length 1 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_isRightDescent_one (i : B) : ¬cs.IsRightDescent 1 i := by simp [IsRightDescent]
/-
**CoxeterSystem.isLeftDescent_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：isLeftDescent_inv_iff {w : W} {i : B} : cs.IsLeftDescent w⁻¹ i ↔ cs.IsRigh
tDescent w i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CoxeterSystem.length_inv`：length_inv (w : W) : ℓ (w⁻¹) = ℓ w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `CoxeterSystem.inv_simple`：inv_simple (i : B) : (s i)⁻¹ = s i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLeftDescent_inv_iff {w : W} {i : B} :
    cs.IsLeftDescent w⁻¹ i ↔ cs.IsRightDescent w i := by
  unfold IsLeftDescent IsRightDescent
  nth_rw 1 [← length_inv]
  simp
/-
**CoxeterSystem.isRightDescent_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`
。
形式化陈述：isRightDescent_inv_iff {w : W} {i : B} : cs.IsRightDescent w⁻¹ i ↔ cs.IsLe
ftDescent w i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CoxeterSystem.isLeftDescent_inv_iff`：isLeftDescent_inv_iff {w : W} {i : 
B} : cs.IsLeftDescent w⁻¹ i ↔ cs.IsRightDescent w i
-/
theorem isRightDescent_inv_iff {w : W} {i : B} :
    cs.IsRightDescent w⁻¹ i ↔ cs.IsLeftDescent w i := by
  simpa using (cs.isLeftDescent_inv_iff (w := w⁻¹)).symm
/-
**CoxeterSystem.exists_leftDescent_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterS
ystem`。
形式化陈述：exists_leftDescent_of_ne_one {w : W} (hw : w != 1) : exists i : B, cs.IsLe
ftDescent w i
参数：hw : w != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoxeterSystem.exists_isReduced`：exists_isReduced (w : W) : exists ω : Li
st B, cs.IsReduced ω ∧ w = π ω
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.wordProd_nil`：∀ {B : Type u_1} {W : Type u_3} [inst : Grou
p W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W), cs.wordProd [] = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.exists_cons_of_ne_nil`：∀ {α : Type u_1} {l : List α}, l ≠ [] → ∃ b 
l', l = b :: l'
· 使用定理 `CoxeterSystem.IsLeftDescent.eq_1`：∀ {B : Type u_1} {W : Type u_2} [inst 
: Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (w : W) (i : B),   cs.
IsLeftDescent w i = (c…
· 使用定理 `CoxeterSystem.wordProd_cons`：wordProd_cons (i : B) (ω : List B) : π (i :
: ω) = s i * π ω
· 使用定理 `CoxeterSystem.simple_mul_simple_cancel_left`：simple_mul_simple_cancel_le
ft {w : W} (i : B) : s i * (s i * w) = w
· 使用定理 `CoxeterSystem.length_wordProd_le`：length_wordProd_le (ω : List B) : ℓ (π
 ω) <= ω.length
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem exists_leftDescent_of_ne_one {w : W} (hw : w ≠ 1) : ∃ i : B, cs.IsLeftDescent w i := by
  rcases cs.exists_isReduced w with ⟨ω, h, rfl⟩
  have h₁ : ω ≠ [] := by rintro rfl; simp at hw
  rcases List.exists_cons_of_ne_nil h₁ with ⟨i, ω', rfl⟩
  use i
  rw [IsLeftDescent, h, wordProd_cons, simple_mul_simple_cancel_left]
  calc
    ℓ (π ω') ≤ ω'.length := cs.length_wordProd_le ω'
    _ < (i :: ω').length := by simp
/-
**CoxeterSystem.exists_rightDescent_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Coxeter
System`。
形式化陈述：exists_rightDescent_of_ne_one {w : W} (hw : w != 1) : exists i : B, cs.IsR
ightDescent w i
参数：hw : w != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CoxeterSystem.exists_leftDescent_of_ne_one`：exists_leftDescent_of_ne_one
 {w : W} (hw : w != 1) : exists i : B, cs.IsLeftDescent w i
-/
theorem exists_rightDescent_of_ne_one {w : W} (hw : w ≠ 1) : ∃ i : B, cs.IsRightDescent w i := by
  simp only [← isLeftDescent_inv_iff]
  apply exists_leftDescent_of_ne_one
  simpa
/-
**CoxeterSystem.isLeftDescent_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：isLeftDescent_iff {w : W} {i : B} : cs.IsLeftDescent w i ↔ ℓ (s i * w) + 1
 = ℓ w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `CoxeterSystem.length_simple_mul`：length_simple_mul (w : W) (i : B) : ℓ (
s i * w) = ℓ w + 1 ∨ ℓ (s i * w) + 1 = ℓ w
-/
theorem isLeftDescent_iff {w : W} {i : B} :
    cs.IsLeftDescent w i ↔ ℓ (s i * w) + 1 = ℓ w := by
  unfold IsLeftDescent
  constructor
  · intro _
    exact (cs.length_simple_mul w i).resolve_left (by lia)
  · lia
/-
**CoxeterSystem.not_isLeftDescent_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：not_isLeftDescent_iff {w : W} {i : B} : ¬cs.IsLeftDescent w i ↔ ℓ (s i * w
) = ℓ w + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `CoxeterSystem.length_simple_mul`：length_simple_mul (w : W) (i : B) : ℓ (
s i * w) = ℓ w + 1 ∨ ℓ (s i * w) + 1 = ℓ w
-/
theorem not_isLeftDescent_iff {w : W} {i : B} :
    ¬cs.IsLeftDescent w i ↔ ℓ (s i * w) = ℓ w + 1 := by
  unfold IsLeftDescent
  constructor
  · intro _
    exact (cs.length_simple_mul w i).resolve_right (by lia)
  · lia
/-
**CoxeterSystem.isRightDescent_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：isRightDescent_iff {w : W} {i : B} : cs.IsRightDescent w i ↔ ℓ (w * s i) +
 1 = ℓ w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `CoxeterSystem.length_mul_simple`：length_mul_simple (w : W) (i : B) : ℓ (
w * s i) = ℓ w + 1 ∨ ℓ (w * s i) + 1 = ℓ w
-/
theorem isRightDescent_iff {w : W} {i : B} :
    cs.IsRightDescent w i ↔ ℓ (w * s i) + 1 = ℓ w := by
  unfold IsRightDescent
  constructor
  · intro _
    exact (cs.length_mul_simple w i).resolve_left (by lia)
  · lia
/-
**CoxeterSystem.not_isRightDescent_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`
。
形式化陈述：not_isRightDescent_iff {w : W} {i : B} : ¬cs.IsRightDescent w i ↔ ℓ (w * s
 i) = ℓ w + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `CoxeterSystem.length_mul_simple`：length_mul_simple (w : W) (i : B) : ℓ (
w * s i) = ℓ w + 1 ∨ ℓ (w * s i) + 1 = ℓ w
-/
theorem not_isRightDescent_iff {w : W} {i : B} :
    ¬cs.IsRightDescent w i ↔ ℓ (w * s i) = ℓ w + 1 := by
  unfold IsRightDescent
  constructor
  · intro _
    exact (cs.length_mul_simple w i).resolve_right (by lia)
  · lia
/-
**CoxeterSystem.isLeftDescent_iff_not_isLeftDescent_mul** 是 Mathlib 中的一个定理，位于命名空
间 `CoxeterSystem`。
形式化陈述：isLeftDescent_iff_not_isLeftDescent_mul {w : W} {i : B} : cs.IsLeftDescent
 w i ↔ ¬cs.IsLeftDescent (s i * w) i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.isLeftDescent_iff`：isLeftDescent_iff {w : W} {i : B} : cs.
IsLeftDescent w i ↔ ℓ (s i * w) + 1 = ℓ w
· 使用定理 `CoxeterSystem.not_isLeftDescent_iff`：not_isLeftDescent_iff {w : W} {i : 
B} : ¬cs.IsLeftDescent w i ↔ ℓ (s i * w) = ℓ w + 1
· 使用定理 `CoxeterSystem.simple_mul_simple_cancel_left`：simple_mul_simple_cancel_le
ft {w : W} (i : B) : s i * (s i * w) = w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isLeftDescent_iff_not_isLeftDescent_mul {w : W} {i : B} :
    cs.IsLeftDescent w i ↔ ¬cs.IsLeftDescent (s i * w) i := by
  rw [isLeftDescent_iff, not_isLeftDescent_iff, simple_mul_simple_cancel_left]
  tauto
/-
**CoxeterSystem.isRightDescent_iff_not_isRightDescent_mul** 是 Mathlib 中的一个定理，位于命
名空间 `CoxeterSystem`。
形式化陈述：isRightDescent_iff_not_isRightDescent_mul {w : W} {i : B} : cs.IsRightDesc
ent w i ↔ ¬cs.IsRightDescent (w * s i) i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.isRightDescent_iff`：isRightDescent_iff {w : W} {i : B} : c
s.IsRightDescent w i ↔ ℓ (w * s i) + 1 = ℓ w
· 使用定理 `CoxeterSystem.not_isRightDescent_iff`：not_isRightDescent_iff {w : W} {i 
: B} : ¬cs.IsRightDescent w i ↔ ℓ (w * s i) = ℓ w + 1
· 使用定理 `CoxeterSystem.simple_mul_simple_cancel_right`：simple_mul_simple_cancel_r
ight {w : W} (i : B) : w * s i * s i = w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isRightDescent_iff_not_isRightDescent_mul {w : W} {i : B} :
    cs.IsRightDescent w i ↔ ¬cs.IsRightDescent (w * s i) i := by
  rw [isRightDescent_iff, not_isRightDescent_iff, simple_mul_simple_cancel_right]
  tauto

end CoxeterSystem

