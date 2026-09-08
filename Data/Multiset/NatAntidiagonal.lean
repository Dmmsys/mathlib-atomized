/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Data.List.NatAntidiagonal
public import Mathlib.Data.Multiset.MapFold

/-!
# Antidiagonals in ℕ × ℕ as multisets

This file defines the antidiagonals of ℕ × ℕ as multisets: the `n`-th antidiagonal is the multiset
of pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines file `Data.List.NatAntidiagonal` and is further refined by file
`Data.Finset.NatAntidiagonal`.
-/

@[expose] public section

assert_not_exists Monoid

namespace Multiset

namespace Nat

/-- The antidiagonal of a natural number `n` is
    the multiset of pairs `(i, j)` such that `i + j = n`. -/
/-
**Multiset.Nat.antidiagonal** 是 Mathlib 中的一个定义，位于命名空间 `Multiset.Nat`。
形式化陈述：antidiagonal (n : Nat) : Multiset (Nat × Nat)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The antidiagonal of a natural number `n` is
    the multiset of pairs `(i, j)` such that `i + j = n`.
-/
def antidiagonal (n : ℕ) : Multiset (ℕ × ℕ) :=
  List.Nat.antidiagonal n

/-- A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`. -/
@[simp]
/-
**Multiset.Nat.mem_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：mem_antidiagonal {n : Nat} {x : Nat × Nat} : x in antidiagonal n ↔ x.1 + x
.2 = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Nat.antidiagonal.eq_1`：∀ (n : ℕ), Multiset.Nat.antidiagonal n =
 ↑(List.Nat.antidiagonal n)
· 使用定理 `Multiset.mem_coe`：mem_coe {a : α} {l : List α} : a in (l : Multiset α) ↔
 a in l
· 使用定理 `List.Nat.mem_antidiagonal`：mem_antidiagonal {n : Nat} {x : Nat × Nat} : 
x in antidiagonal n ↔ x.1 + x.2 = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A pair (i, j) is contained in the antidiagonal of `n` if and only if `i + j = n`
.
-/
theorem mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} : x ∈ antidiagonal n ↔ x.1 + x.2 = n := by
  rw [antidiagonal, mem_coe, List.Nat.mem_antidiagonal]

/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp]
/-
**Multiset.Nat.card_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：card_antidiagonal (n : Nat) : card (antidiagonal n) = n + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Nat.antidiagonal.eq_1`：∀ (n : ℕ), Multiset.Nat.antidiagonal n =
 ↑(List.Nat.antidiagonal n)
· 使用定理 `Multiset.coe_card`：coe_card (l : List α) : card (l : Multiset α) = lengt
h l
· 使用定理 `List.Nat.length_antidiagonal`：length_antidiagonal (n : Nat) : (antidiago
nal n).length = n + 1

--- 原说明 ---
The cardinality of the antidiagonal of `n` is `n+1`.
-/
theorem card_antidiagonal (n : ℕ) : card (antidiagonal n) = n + 1 := by
  rw [antidiagonal, coe_card, List.Nat.length_antidiagonal]

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp]
/-
**Multiset.Nat.antidiagonal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：antidiagonal_zero : antidiagonal 0 = {(0, 0)}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The antidiagonal of `0` is the list `[(0, 0)]`
-/
theorem antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
  rfl

/-- The antidiagonal of `n` does not contain duplicate entries. -/
@[simp]
/-
**Multiset.Nat.nodup_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：nodup_antidiagonal (n : Nat) : Nodup (antidiagonal n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.coe_nodup`：coe_nodup {l : List α} : @Nodup α l ↔ l.Nodup
· 使用定理 `List.Nat.nodup_antidiagonal`：nodup_antidiagonal (n : Nat) : Nodup (antid
iagonal n)

--- 原说明 ---
The antidiagonal of `n` does not contain duplicate entries.
-/
theorem nodup_antidiagonal (n : ℕ) : Nodup (antidiagonal n) :=
  coe_nodup.2 <| List.Nat.nodup_antidiagonal n

@[simp]
/-
**Multiset.Nat.antidiagonal_succ** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：antidiagonal_succ {n : Nat} : antidiagonal (n + 1) = (0, n + 1) ::ₘ (antid
iagonal n).map (Prod.map Nat.succ id)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Nat.antidiagonal_succ`：antidiagonal_succ {n : Nat} : antidiagonal (
n + 1) = (0, n + 1) :: (antidiagonal n).map (Prod.map Nat.succ id)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem antidiagonal_succ {n : ℕ} :
    antidiagonal (n + 1) = (0, n + 1) ::ₘ (antidiagonal n).map (Prod.map Nat.succ id) := by
  simp only [antidiagonal, List.Nat.antidiagonal_succ, map_coe, cons_coe]
/-
**Multiset.Nat.antidiagonal_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：antidiagonal_succ' {n : Nat} : antidiagonal (n + 1) = (n + 1, 0) ::ₘ (anti
diagonal n).map (Prod.map id Nat.succ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Nat.antidiagonal.eq_1`：∀ (n : ℕ), Multiset.Nat.antidiagonal n =
 ↑(List.Nat.antidiagonal n)
· 使用定理 `List.Nat.antidiagonal_succ'`：antidiagonal_succ' {n : Nat} : antidiagonal
 (n + 1) = (antidiagonal n).map (Prod.map id Nat.succ) ++ [(n + 1, 0)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_add`：coe_add (s t : List α) : (s + t : Multiset α) = (s ++ 
t : List α)
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用定理 `Multiset.map_coe`：∀ {α : Type u_1} {β : Type v} (f : α → β) (l : List α)
, Multiset.map f ↑l = ↑(List.map f l)
· 使用定理 `List.singleton_append`：∀ {α : Type u_1} {x : α} {l : List α}, [x] ++ l =
 x :: l
· 使用定理 `Multiset.cons_coe`：cons_coe (a : α) (l : List α) : (a ::ₘ l : Multiset α
) = (a :: l : List α)
-/
theorem antidiagonal_succ' {n : ℕ} :
    antidiagonal (n + 1) = (n + 1, 0) ::ₘ (antidiagonal n).map (Prod.map id Nat.succ) := by
  rw [antidiagonal, List.Nat.antidiagonal_succ', ← coe_add, Multiset.add_comm, antidiagonal,
    map_coe, coe_add, List.singleton_append, cons_coe]
/-
**Multiset.Nat.antidiagonal_succ_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：antidiagonal_succ_succ' {n : Nat} : antidiagonal (n + 2) = (0, n + 2) ::ₘ 
(n + 2, 0) ::ₘ (antidiagonal n).map (Prod.map Nat.succ Nat.succ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Nat.antidiagonal_succ`：antidiagonal_succ {n : Nat} : antidiagon
al (n + 1) = (0, n + 1) ::ₘ (antidiagonal n).map (Prod.map Nat.succ id)
· 使用定理 `Multiset.Nat.antidiagonal_succ'`：antidiagonal_succ' {n : Nat} : antidiag
onal (n + 1) = (n + 1, 0) ::ₘ (antidiagonal n).map (Prod.map id Nat.succ)
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Prod.map_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type
 u_4} (f : α → β) (g : γ → δ) (x : α) (y : γ),   Prod.map f g (x, y) = (f x, g y
)
-/
theorem antidiagonal_succ_succ' {n : ℕ} :
    antidiagonal (n + 2) =
      (0, n + 2) ::ₘ (n + 2, 0) ::ₘ (antidiagonal n).map (Prod.map Nat.succ Nat.succ) := by
  rw [antidiagonal_succ, antidiagonal_succ', map_cons, map_map, Prod.map_apply]
  rfl
/-
**Multiset.Nat.map_swap_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nat`。
形式化陈述：map_swap_antidiagonal {n : Nat} : (antidiagonal n).map Prod.swap = antidia
gonal n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Nat.antidiagonal.eq_1`：∀ (n : ℕ), Multiset.Nat.antidiagonal n =
 ↑(List.Nat.antidiagonal n)
· 使用定理 `Multiset.map_coe`：∀ {α : Type u_1} {β : Type v} (f : α → β) (l : List α)
, Multiset.map f ↑l = ↑(List.map f l)
· 使用定理 `List.Nat.map_swap_antidiagonal`：map_swap_antidiagonal {n : Nat} : (antid
iagonal n).map Prod.swap = (antidiagonal n).reverse
· 使用定理 `Multiset.coe_reverse`：coe_reverse (l : List α) : (reverse l : Multiset α
) = l
-/
theorem map_swap_antidiagonal {n : ℕ} : (antidiagonal n).map Prod.swap = antidiagonal n := by
  rw [antidiagonal, map_coe, List.Nat.map_swap_antidiagonal, coe_reverse]

end Nat

end Multiset

