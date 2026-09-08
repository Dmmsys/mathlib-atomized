/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Products of lists of prime elements.

This file contains some theorems relating `Prime` and products of `List`s.

-/

public section


open List

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M]

/-- Prime `p` divides the product of a list `L` iff it divides some `a ∈ L` -/
/-
**Prime.dvd_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.dvd_prod_iff {p : M} {L : List M} (pp : Prime p) : p ∣ L.prod ↔ exis
ts a in L, p ∣ a
参数：pp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_nil`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α], [].prod =
 1
· 使用定理 `Prime.not_dvd_one`：not_dvd_one : ¬p ∣ 1
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `List.dvd_prod`：dvd_prod [CommMonoid M] {a} {l : List M} (ha : a in l) : 
a ∣ l.prod

--- 原说明 ---
Prime `p` divides the product of a list `L` iff it divides some `a ∈ L`
-/
theorem Prime.dvd_prod_iff {p : M} {L : List M} (pp : Prime p) : p ∣ L.prod ↔ ∃ a ∈ L, p ∣ a := by
  constructor
  · intro h
    induction L with
    | nil =>
      rw [prod_nil] at h
      exact absurd h pp.not_dvd_one
    | cons L_hd L_tl L_ih =>
      rw [prod_cons] at h
      rcases pp.dvd_or_dvd h with hd | hd
      · exact ⟨L_hd, mem_cons_self, hd⟩
      · obtain ⟨x, hx1, hx2⟩ := L_ih hd
        exact ⟨x, mem_cons_of_mem L_hd hx1, hx2⟩
  · exact fun ⟨a, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod ha1)
/-
**Prime.not_dvd_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.not_dvd_prod {p : M} {L : List M} (pp : Prime p) (hL : forall a in L
, ¬p ∣ a) : ¬p ∣ L.prod
参数：pp : Prime p；hL : forall a in L, ¬p ∣ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prime.dvd_prod_iff`：Prime.dvd_prod_iff {p : M} {L : List M} (pp : Prime 
p) : p ∣ L.prod ↔ exists a in L, p ∣ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
-/
theorem Prime.not_dvd_prod {p : M} {L : List M} (pp : Prime p) (hL : ∀ a ∈ L, ¬p ∣ a) :
    ¬p ∣ L.prod :=
  mt (Prime.dvd_prod_iff pp).1 <| not_exists.2 fun a => not_and.2 (hL a)

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M] [Subsingleton Mˣ]

/-
**mem_list_primes_of_dvd_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_list_primes_of_dvd_prod {p : M} (hp : Prime p) {L : List M} (hL : fora
ll q in L, Prime q) (hpL : p ∣ L.prod) : p in L
参数：hp : Prime p；hL : forall q in L, Prime q；hpL : p ∣ L.prod。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prime.dvd_prod_iff`：Prime.dvd_prod_iff {p : M} {L : List M} (pp : Prime 
p) : p ∣ L.prod ↔ exists a in L, p ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {M : Type*} [CommMonoidWi
thZero M] [IsCancelMulZero M] [Subsingleton Mˣ] {p q : M} (pp : Prime p) (qp : P
rime q) : p …
-/
theorem mem_list_primes_of_dvd_prod {p : M} (hp : Prime p) {L : List M} (hL : ∀ q ∈ L, Prime q)
    (hpL : p ∣ L.prod) : p ∈ L := by
  obtain ⟨x, hx1, hx2⟩ := hp.dvd_prod_iff.mp hpL
  rwa [(prime_dvd_prime_iff_eq hp (hL x hx1)).mp hx2]
/-
**perm_of_prod_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：perm_of_prod_eq_prod : forall {l₁ l₂ : List M}, l₁.prod = l₂.prod -> (fora
ll p in l₁, Prime p) -> (forall p in l₂, Prime p) -> Perm l₁ l₂ | [], [], _, _, 
_ => Perm.nil | [], a :: l, h₁, _, h₃ => have ha : a ∣ 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem perm_of_prod_eq_prod :
    ∀ {l₁ l₂ : List M}, l₁.prod = l₂.prod → (∀ p ∈ l₁, Prime p) → (∀ p ∈ l₂, Prime p) → Perm l₁ l₂
  | [], [], _, _, _ => Perm.nil
  | [], a :: l, h₁, _, h₃ =>
    have ha : a ∣ 1 := prod_nil (α := M) ▸ h₁.symm ▸ (prod_cons (l := l)).symm ▸ dvd_mul_right _ _
    absurd ha (Prime.not_dvd_one (h₃ a mem_cons_self))
  | a :: l, [], h₁, h₂, _ =>
    have ha : a ∣ 1 := prod_nil (α := M) ▸ h₁ ▸ (prod_cons (l := l)).symm ▸ dvd_mul_right _ _
    absurd ha (Prime.not_dvd_one (h₂ a mem_cons_self))
  | a :: l₁, b :: l₂, h, hl₁, hl₂ => by
    classical
      have hl₁' : ∀ p ∈ l₁, Prime p := fun p hp => hl₁ p (mem_cons_of_mem _ hp)
      have hl₂' : ∀ p ∈ (b :: l₂).erase a, Prime p := fun p hp => hl₂ p (mem_of_mem_erase hp)
      have ha : a ∈ b :: l₂ :=
        mem_list_primes_of_dvd_prod (hl₁ a mem_cons_self) hl₂
          (h ▸ by rw [prod_cons]; exact dvd_mul_right _ _)
      have hb : b :: l₂ ~ a :: (b :: l₂).erase a := perm_cons_erase ha
      have hl : prod l₁ = prod ((b :: l₂).erase a) :=
        (mul_right_inj' (hl₁ a mem_cons_self).ne_zero).1 <| by
          rwa [← prod_cons, ← prod_cons, ← hb.prod_eq]
      exact Perm.trans ((perm_of_prod_eq_prod hl hl₁' hl₂').cons _) hb.symm

end CancelCommMonoidWithZero

