/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Multiset.NatAntidiagonal

/-!
# Antidiagonals in ℕ × ℕ as finsets

This file defines the antidiagonals of ℕ × ℕ as finsets: the `n`-th antidiagonal is the finset of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines files `Data.List.NatAntidiagonal` and `Data.Multiset.NatAntidiagonal`, providing an
instance enabling `Finset.antidiagonal` on `Nat`.
-/

@[expose] public section

assert_not_exists Field

open Function

namespace Finset

open Finset.HasAntidiagonal

namespace Nat

/-- The antidiagonal of a natural number `n` is
    the finset of pairs `(i, j)` such that `i + j = n`. -/
/-
**Finset.Nat.instHasAntidiagonal** 是 Mathlib 中的一个实例，位于命名空间 `Finset.Nat`。
形式化陈述：instHasAntidiagonal : HasAntidiagonal Nat where antidiagonal n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nat.nodup_antidiagonal`：nodup_antidiagonal (n : Nat) : Nodup (a
ntidiagonal n)

--- 原说明 ---
The antidiagonal of a natural number `n` is
    the finset of pairs `(i, j)` such that `i + j = n`.
-/
instance instHasAntidiagonal : HasAntidiagonal ℕ where
  antidiagonal n := ⟨Multiset.Nat.antidiagonal n, Multiset.Nat.nodup_antidiagonal n⟩
  mem_antidiagonal {n} {xy} := by
    rw [mem_def, Multiset.Nat.mem_antidiagonal]
/-
**Finset.Nat.antidiagonal_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonal_eq_map (n : Nat) : antidiagonal n = (range (n + 1)).map ⟨fun 
i => (i, n - i), fun _ _ h => (Prod.ext_iff.1 h).1⟩
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma antidiagonal_eq_map (n : ℕ) :
    antidiagonal n = (range (n + 1)).map ⟨fun i ↦ (i, n - i), fun _ _ h ↦ (Prod.ext_iff.1 h).1⟩ :=
  rfl
/-
**Finset.Nat.antidiagonal_eq_map'** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonal_eq_map' (n : Nat) : antidiagonal n = (range (n + 1)).map ⟨fun
 i => (n - i, i), fun _ _ h => (Prod.ext_iff.1 h).2⟩
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `Prod.swap_injective`：swap_injective : Function.Injective (@swap α β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.HasAntidiagonal.map_swap_antidiagonal`：∀ {A : Type u_1} [inst : A
ddCommMonoid A] [inst_1 : Finset.HasAntidiagonal A] {n : A},   Finset.map { toFu
n := Prod.swap, inj' := ⋯ } (Finse…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Finset.Nat.antidiagonal_eq_map`：antidiagonal_eq_map (n : Nat) : antidiag
onal n = (range (n + 1)).map ⟨fun i => (i, n - i), fun _ _ h => (Prod.ext_iff.1 
h).1⟩
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
-/
lemma antidiagonal_eq_map' (n : ℕ) :
    antidiagonal n =
      (range (n + 1)).map ⟨fun i ↦ (n - i, i), fun _ _ h ↦ (Prod.ext_iff.1 h).2⟩ := by
  rw [← map_swap_antidiagonal, antidiagonal_eq_map, map_map]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.Nat.antidiagonal_eq_image** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonal_eq_image (n : Nat) : antidiagonal n = (range (n + 1)).image f
un i => (i, n - i)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma antidiagonal_eq_image (n : ℕ) :
    antidiagonal n = (range (n + 1)).image fun i ↦ (i, n - i) := by
  simp only [antidiagonal_eq_map, map_eq_image, Function.Embedding.coeFn_mk]

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.Nat.antidiagonal_eq_image'** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonal_eq_image' (n : Nat) : antidiagonal n = (range (n + 1)).image 
fun i => (n - i, i)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用引理 `Finset.Nat.antidiagonal_eq_map'`：antidiagonal_eq_map' (n : Nat) : antidi
agonal n = (range (n + 1)).map ⟨fun i => (n - i, i), fun _ _ h => (Prod.ext_iff.
1 h).2⟩
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma antidiagonal_eq_image' (n : ℕ) :
    antidiagonal n = (range (n + 1)).image fun i ↦ (n - i, i) := by
  simp only [antidiagonal_eq_map', map_eq_image, Function.Embedding.coeFn_mk]

/-- The cardinality of the antidiagonal of `n` is `n + 1`. -/
@[simp]
/-
**Finset.Nat.card_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：card_antidiagonal (n : Nat) : (antidiagonal n).card = n + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Nat.card_antidiagonal`：card_antidiagonal (n : Nat) : card (anti
diagonal n) = n + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The cardinality of the antidiagonal of `n` is `n + 1`.
-/
theorem card_antidiagonal (n : ℕ) : (antidiagonal n).card = n + 1 := by simp [antidiagonal]

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp]
/-
**Finset.Nat.antidiagonal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonal_zero : antidiagonal 0 = {(0, 0)}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The antidiagonal of `0` is the list `[(0, 0)]`
-/
theorem antidiagonal_zero : antidiagonal 0 = {(0, 0)} := rfl
/-
**Finset.Nat.antidiagonal_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonal_succ (n : Nat) : antidiagonal (n + 1) = cons (0, n + 1) ((ant
idiagonal n).map (Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩ (Embedding.re
fl _))) (by simp)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用引理 `Nat.succ_injective`：succ_injective : Injective Nat.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.cons_val`：cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1
· 使用定理 `Finset.map_val`：map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.m
ap f
· 使用定理 `Multiset.Nat.antidiagonal_succ`：antidiagonal_succ {n : Nat} : antidiagon
al (n + 1) = (0, n + 1) ::ₘ (antidiagonal n).map (Prod.map Nat.succ id)
-/
theorem antidiagonal_succ (n : ℕ) :
    antidiagonal (n + 1) =
      cons (0, n + 1)
        ((antidiagonal n).map
          (Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩ (Embedding.refl _)))
        (by simp) := by
  apply eq_of_veq
  rw [cons_val, map_val]
  apply Multiset.Nat.antidiagonal_succ
/-
**Finset.Nat.antidiagonal_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonal_succ' (n : Nat) : antidiagonal (n + 1) = cons (n + 1, 0) ((an
tidiagonal n).map (Embedding.prodMap (Embedding.refl _) ⟨Nat.succ, Nat.succ_inje
ctive⟩)) (by simp)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用引理 `Nat.succ_injective`：succ_injective : Injective Nat.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.cons_val`：cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1
· 使用定理 `Finset.map_val`：map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.m
ap f
· 使用定理 `Multiset.Nat.antidiagonal_succ'`：antidiagonal_succ' {n : Nat} : antidiag
onal (n + 1) = (n + 1, 0) ::ₘ (antidiagonal n).map (Prod.map id Nat.succ)
-/
theorem antidiagonal_succ' (n : ℕ) :
    antidiagonal (n + 1) =
      cons (n + 1, 0)
        ((antidiagonal n).map
          (Embedding.prodMap (Embedding.refl _) ⟨Nat.succ, Nat.succ_injective⟩))
        (by simp) := by
  apply eq_of_veq
  rw [cons_val, map_val]
  exact Multiset.Nat.antidiagonal_succ'
/-
**Finset.Nat.antidiagonal_succ_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonal_succ_succ' {n : Nat} : antidiagonal (n + 2) = cons (0, n + 2)
 (cons (n + 2, 0) ((antidiagonal n).map (Embedding.prodMap ⟨Nat.succ, Nat.succ_i
njective⟩ ⟨Nat.succ, Nat.succ_injective⟩)) <| by simp) (by simp)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.succ_injective`：succ_injective : Injective Nat.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nat.antidiagonal_succ`：antidiagonal_succ (n : Nat) : antidiagonal
 (n + 1) = cons (0, n + 1) ((antidiagonal n).map (Embedding.prodMap ⟨Nat.succ, N
at.succ_injective⟩…
· 使用定理 `Finset.Nat.antidiagonal_succ'`：antidiagonal_succ' (n : Nat) : antidiagon
al (n + 1) = cons (n + 1, 0) ((antidiagonal n).map (Embedding.prodMap (Embedding
.refl _) ⟨Nat.succ,…
· 使用定理 `Finset.cons.congr_simp`：∀ {α : Type u_1} (a a_1 : α) (e_a : a = a_1) (s 
s_1 : Finset α) (e_s : s = s_1) (h : a ∉ s),   Finset.cons a s h = Finset.cons a
_1 s_1 ⋯
· 使用定理 `Finset.map_cons`：map_cons (f : α ↪ β) (a : α) (s : Finset α) (ha : a ∉ s
) : (cons a s ha).map f = cons (f a) (s.map f) (by simpa using ha)
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
-/
theorem antidiagonal_succ_succ' {n : ℕ} :
    antidiagonal (n + 2) =
      cons (0, n + 2)
        (cons (n + 2, 0)
            ((antidiagonal n).map
              (Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩
                ⟨Nat.succ, Nat.succ_injective⟩)) <|
          by simp)
        (by simp) := by
  simp_rw [antidiagonal_succ (n + 1), antidiagonal_succ', Finset.map_cons, map_map]
  rfl
/-
**Finset.Nat.antidiagonal.fst_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat.antidiago
nal`。
形式化陈述：∀ {n : ℕ} {kl : ℕ × ℕ}, kl ∈ Finset.HasAntidiagonal.antidiagonal n → kl.1 
< n + 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Finset.HasAntidiagonal.antidiagonal.fst_le`：∀ {A : Type u_1} [inst : Add
CommMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fi
nset.HasAntidiagonal A] {n : A} …
-/
theorem antidiagonal.fst_lt {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.1 < n + 1 :=
  Nat.lt_succ_of_le <| antidiagonal.fst_le hlk
/-
**Finset.Nat.antidiagonal.snd_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nat.antidiago
nal`。
形式化陈述：∀ {n : ℕ} {kl : ℕ × ℕ}, kl ∈ Finset.HasAntidiagonal.antidiagonal n → kl.2 
< n + 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Finset.HasAntidiagonal.antidiagonal.snd_le`：∀ {A : Type u_1} [inst : Add
CommMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fi
nset.HasAntidiagonal A] {n : A} …
-/
theorem antidiagonal.snd_lt {n : ℕ} {kl : ℕ × ℕ} (hlk : kl ∈ antidiagonal n) : kl.2 < n + 1 :=
  Nat.lt_succ_of_le <| antidiagonal.snd_le hlk
/-
**Finset.Nat.antidiagonal_filter_snd_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset.
Nat`。
形式化陈述：∀ {n k : ℕ},   k ≤ n →     {a ∈ Finset.HasAntidiagonal.antidiagonal n | a.
2 ≤ k} =       Finset.map ({ toFun := fun x => x + (n - k), inj' := ⋯ }.prodMap 
(Function.Embedding.refl ℕ))         (Finset.HasAntidiagonal.antidiagonal k)
参数：{ toFun := fun x => x + (n - k), inj' := ⋯ }.prodMap (Function.Embedding.refl
 ℕ)；Finset.HasAntidiagonal.antidiagonal k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_add_eq_add_tsub`：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a 
+ c - b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Embedding.refl_apply`：∀ (α : Sort u_1) (a : α), (Function.Embed
ding.refl α) a = a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
-/
@[simp] lemma antidiagonal_filter_snd_le_of_le {n k : ℕ} (h : k ≤ n) :
    {a ∈ antidiagonal n | a.snd ≤ k} = (antidiagonal k).map
      (Embedding.prodMap ⟨_, add_left_injective (n - k)⟩ (Embedding.refl ℕ)) := by
  ext ⟨i, j⟩
  suffices i + j = n ∧ j ≤ k ↔ ∃ a, a + j = k ∧ a + (n - k) = i by simpa
  refine ⟨fun hi ↦ ⟨k - j, tsub_add_cancel_of_le hi.2, ?_⟩, ?_⟩
  · rw [add_comm, tsub_add_eq_add_tsub h, ← hi.1, add_assoc, Nat.add_sub_of_le hi.2,
      add_tsub_cancel_right]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨?_, hl ▸ Nat.le_add_left j l⟩
    rw [add_assoc, add_comm, add_assoc, add_comm j l, hl]
    exact Nat.sub_add_cancel h
/-
**Finset.Nat.antidiagonal_filter_fst_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset.
Nat`。
形式化陈述：∀ {n k : ℕ},   k ≤ n →     {a ∈ Finset.HasAntidiagonal.antidiagonal n | a.
1 ≤ k} =       Finset.map ((Function.Embedding.refl ℕ).prodMap { toFun := fun x 
=> x + (n - k), inj' := ⋯ })         (Finset.HasAntidiagonal.antidiagonal k)
参数：(Function.Embedding.refl ℕ).prodMap { toFun := fun x => x + (n - k), inj' := 
⋯ }；Finset.HasAntidiagonal.antidiagonal k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `exists₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∃ a b, p a b) ↔ ∃ a b, q a b
)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.HasAntidiagonal.map_prodComm_antidiagonal`：∀ {A : Type u_1} [inst
 : AddCommMonoid A] [inst_1 : Finset.HasAntidiagonal A] {n : A},   Finset.map (E
quiv.prodComm A A).toEmbedding (Finset…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.Nat.antidiagonal_filter_snd_le_of_le`：∀ {n k : ℕ},   k ≤ n →     
{a ∈ Finset.HasAntidiagonal.antidiagonal n | a.2 ≤ k} =       Finset.map ({ toFu
n := fun x => x + (n - k), inj' :…
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Function.Embedding.refl_apply`：∀ (α : Sort u_1) (a : α), (Function.Embed
ding.refl α) a = a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
@[simp] lemma antidiagonal_filter_fst_le_of_le {n k : ℕ} (h : k ≤ n) :
    {a ∈ antidiagonal n | a.fst ≤ k} = (antidiagonal k).map
      (Embedding.prodMap (Embedding.refl ℕ) ⟨_, add_left_injective (n - k)⟩) := by
  have aux₁ : fun a ↦ a.fst ≤ k = (fun a ↦ a.snd ≤ k) ∘ (Equiv.prodComm ℕ ℕ).symm := rfl
  have aux₂ : ∀ i j, (∃ a b, a + b = k ∧ b = i ∧ a + (n - k) = j) ↔
                      ∃ a b, a + b = k ∧ a = i ∧ b + (n - k) = j :=
    fun i j ↦ by rw [exists_comm]; exact exists₂_congr (fun a b ↦ by rw [add_comm])
  rw [← map_prodComm_antidiagonal]
  simp_rw [aux₁, ← map_filter, antidiagonal_filter_snd_le_of_le h, map_map]
  ext ⟨i, j⟩
  simpa using aux₂ i j
/-
**Finset.Nat.antidiagonal_filter_le_fst_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset.
Nat`。
形式化陈述：∀ {n k : ℕ},   k ≤ n →     {a ∈ Finset.HasAntidiagonal.antidiagonal n | k 
≤ a.1} =       Finset.map ({ toFun := fun x => x + k, inj' := ⋯ }.prodMap (Funct
ion.Embedding.refl ℕ))         (Finset.HasAntidiagonal.antidiagonal (n - k))
参数：{ toFun := fun x => x + k, inj' := ⋯ }.prodMap (Function.Embedding.refl ℕ)；Fi
nset.HasAntidiagonal.antidiagonal (n - k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_comm`：∀ {n m k : ℕ}, k ≤ n → n + m - k = n - k + m
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Embedding.refl_apply`：∀ (α : Sort u_1) (a : α), (Function.Embed
ding.refl α) a = a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
-/
@[simp] lemma antidiagonal_filter_le_fst_of_le {n k : ℕ} (h : k ≤ n) :
    {a ∈ antidiagonal n | k ≤ a.fst} = (antidiagonal (n - k)).map
      (Embedding.prodMap ⟨_, add_left_injective k⟩ (Embedding.refl ℕ)) := by
  ext ⟨i, j⟩
  suffices i + j = n ∧ k ≤ i ↔ ∃ a, a + j = n - k ∧ a + k = i by simpa
  refine ⟨fun hi ↦ ⟨i - k, ?_, tsub_add_cancel_of_le hi.2⟩, ?_⟩
  · rw [← Nat.sub_add_comm hi.2, hi.1]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨?_, Nat.le_add_left k l⟩
    rw [add_right_comm, hl]
    exact tsub_add_cancel_of_le h
/-
**Finset.Nat.antidiagonal_filter_le_snd_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset.
Nat`。
形式化陈述：∀ {n k : ℕ},   k ≤ n →     {a ∈ Finset.HasAntidiagonal.antidiagonal n | k 
≤ a.2} =       Finset.map ((Function.Embedding.refl ℕ).prodMap { toFun := fun x 
=> x + k, inj' := ⋯ })         (Finset.HasAntidiagonal.antidiagonal (n - k))
参数：(Function.Embedding.refl ℕ).prodMap { toFun := fun x => x + k, inj' := ⋯ }；Fi
nset.HasAntidiagonal.antidiagonal (n - k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `exists₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∃ a b, p a b) ↔ ∃ a b, q a b
)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.HasAntidiagonal.map_prodComm_antidiagonal`：∀ {A : Type u_1} [inst
 : AddCommMonoid A] [inst_1 : Finset.HasAntidiagonal A] {n : A},   Finset.map (E
quiv.prodComm A A).toEmbedding (Finset…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.Nat.antidiagonal_filter_le_fst_of_le`：∀ {n k : ℕ},   k ≤ n →     
{a ∈ Finset.HasAntidiagonal.antidiagonal n | k ≤ a.1} =       Finset.map ({ toFu
n := fun x => x + k, inj' := ⋯ }.…
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Function.Embedding.refl_apply`：∀ (α : Sort u_1) (a : α), (Function.Embed
ding.refl α) a = a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
@[simp] lemma antidiagonal_filter_le_snd_of_le {n k : ℕ} (h : k ≤ n) :
    {a ∈ antidiagonal n | k ≤ a.snd} = (antidiagonal (n - k)).map
      (Embedding.prodMap (Embedding.refl ℕ) ⟨_, add_left_injective k⟩) := by
  have aux₁ : fun a ↦ k ≤ a.snd = (fun a ↦ k ≤ a.fst) ∘ (Equiv.prodComm ℕ ℕ).symm := rfl
  have aux₂ : ∀ i j, (∃ a b, a + b = n - k ∧ b = i ∧ a + k = j) ↔
                      ∃ a b, a + b = n - k ∧ a = i ∧ b + k = j :=
    fun i j ↦ by rw [exists_comm]; exact exists₂_congr (fun a b ↦ by rw [add_comm])
  rw [← map_prodComm_antidiagonal]
  simp_rw [aux₁, ← map_filter, antidiagonal_filter_le_fst_of_le h,
    map_map]
  ext ⟨i, j⟩
  simpa using aux₂ i j

/-- The set `antidiagonal n` is equivalent to `Fin (n+1)`, via the first projection. -/
@[simps]
/-
**Finset.Nat.antidiagonalEquivFin** 是 Mathlib 中的一个定义，位于命名空间 `Finset.Nat`。
形式化陈述：antidiagonalEquivFin (n : Nat) : antidiagonal n ≃ Fin (n + 1) where toFun
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `antidiagonal n` is equivalent to `Fin (n+1)`, via the first projection.
-/
def antidiagonalEquivFin (n : ℕ) : antidiagonal n ≃ Fin (n + 1) where
  toFun := fun ⟨⟨i, _⟩, h⟩ ↦ ⟨i, antidiagonal.fst_lt h⟩
  invFun := fun ⟨i, h⟩ ↦ ⟨⟨i, n - i⟩, by
    rw [mem_antidiagonal, add_comm, Nat.sub_add_cancel]
    exact Nat.le_of_lt_succ h⟩

end Nat

end Finset

