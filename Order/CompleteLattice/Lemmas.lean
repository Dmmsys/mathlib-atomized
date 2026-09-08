/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Bool.Set
public import Mathlib.Data.Nat.Set
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Theory of complete lattices

This file contains results on complete lattices that need more theory to develop.

## Naming conventions

In lemma names,
* `sSup` is called `sSup`
* `sInf` is called `sInf`
* `⨆ i, s i` is called `iSup`
* `⨅ i, s i` is called `iInf`
* `⨆ i j, s i j` is called `iSup₂`. This is an `iSup` inside an `iSup`.
* `⨅ i j, s i j` is called `iInf₂`. This is an `iInf` inside an `iInf`.
* `⨆ i ∈ s, t i` is called `biSup` for "bounded `iSup`". This is the special case of `iSup₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `biInf` for "bounded `iInf`". This is the special case of `iInf₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `iSup f`, the supremum of the range of `f`;
* `⨅ i, f i` : `iInf f`, the infimum of the range of `f`.
-/

public section

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

open OrderDual

section

variable [CompleteLattice α] {f g s : ι → α} {a b : α}

/-!
### `iSup` and `iInf` under `Bool`
-/

@[to_dual]
/-
**iSup_bool_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ f false
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Bool.range_eq`：range_eq {α : Type*} (f : Bool -> α) : range f = {f false
, f true}
· 使用定理 `sSup_pair`：sSup_pair {a b : α} : sSup {a, b} = a ⊔ b
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a

--- 原说明 ---
### `iSup` and `iInf` under `Bool`
-/
theorem iSup_bool_eq {f : Bool → α} : ⨆ b : Bool, f b = f true ⊔ f false := by
  rw [iSup, Bool.range_eq, sSup_pair, sup_comm]

@[to_dual]
/-
**sup_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_bool_eq`：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ 
f false
· 使用定理 `Bool.cond_true`：∀ {α : Sort u} {a b : α}, (bif true then a else b) = a
· 使用定理 `Bool.cond_false`：∀ {α : Sort u} {a b : α}, (bif false then a else b) = b
-/
theorem sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y := by
  rw [iSup_bool_eq, Bool.cond_true, Bool.cond_false]

/-!
### `iSup` and `iInf` under `ℕ`
-/

@[to_dual]
/-
**iSup_ge_eq_iSup_nat_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_ge_eq_iSup_nat_add (u : Nat -> α) (n : Nat) : ⨆ i >= n, u i = ⨆ i, u 
(i + n)
参数：u : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n

--- 原说明 ---
### `iSup` and `iInf` under `ℕ`
-/
theorem iSup_ge_eq_iSup_nat_add (u : ℕ → α) (n : ℕ) : ⨆ i ≥ n, u i = ⨆ i, u (i + n) := by
  apply le_antisymm <;> simp only [iSup_le_iff]
  · refine fun i hi => le_sSup ⟨i - n, ?_⟩
    dsimp only
    rw [Nat.sub_add_cancel hi]
  · exact fun i => le_sSup ⟨i + n, iSup_pos (Nat.le_add_left _ _)⟩

-- `to_dual` cannot translate between `Monotone` and `Antitone`.
/-
**Monotone.iSup_nat_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.iSup_nat_add {f : Nat -> α} (hf : Monotone f) (k : Nat) : ⨆ n, f 
(n + k) = ⨆ n, f n
参数：hf : Monotone f；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem Monotone.iSup_nat_add {f : ℕ → α} (hf : Monotone f) (k : ℕ) : ⨆ n, f (n + k) = ⨆ n, f n :=
  le_antisymm (iSup_le fun i => le_iSup _ (i + k)) <| iSup_mono fun i => hf <| Nat.le_add_right i k
/-
**Antitone.iInf_nat_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.iInf_nat_add {f : Nat -> α} (hf : Antitone f) (k : Nat) : ⨅ n, f 
(n + k) = ⨅ n, f n
参数：hf : Antitone f；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.iSup_nat_add`：Monotone.iSup_nat_add {f : Nat -> α} (hf : Monoto
ne f) (k : Nat) : ⨆ n, f (n + k) = ⨆ n, f n
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem Antitone.iInf_nat_add {f : ℕ → α} (hf : Antitone f) (k : ℕ) : ⨅ n, f (n + k) = ⨅ n, f n :=
  hf.dual_right.iSup_nat_add k

-- Not `@[simp]` since the subterm `?f (i + ?k)` produces an ugly higher-order unification problem.
-- (Although the `simpNF` linter does not complain.)
-- See: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/complete_lattice.20and.20has_sup/near/316497982
/-
**iSup_iInf_ge_nat_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_iInf_ge_nat_add (f : Nat -> α) (k : Nat) : ⨆ n, ⨅ i >= n, f (i + k) =
 ⨆ n, ⨅ i >= n, f i
参数：f : Nat -> α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
f : ι → α} {p q : ι → Prop},   (∀ (i : ι), p i → q i) → ⨅ i, ⨅ (_ : q i), f i ≤ 
…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.iSup_nat_add`：Monotone.iSup_nat_add {f : Nat -> α} (hf : Monoto
ne f) (k : Nat) : ⨆ n, f (n + k) = ⨆ n, f n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_ge_eq_iInf_nat_add`：∀ {α : Type u_1} [inst : CompleteLattice α] (u 
: ℕ → α) (n : ℕ), ⨅ i, ⨅ (_ : i ≥ n), u i = ⨅ i, u (i + n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_iInf_ge_nat_add (f : ℕ → α) (k : ℕ) :
    ⨆ n, ⨅ i ≥ n, f (i + k) = ⨆ n, ⨅ i ≥ n, f i := by
  have hf : Monotone fun n => ⨅ i ≥ n, f i := fun n m h => biInf_mono fun i => h.trans
  rw [← Monotone.iSup_nat_add hf k]
  · simp_rw [iInf_ge_eq_iInf_nat_add, ← Nat.add_assoc]

-- Not `@[simp]` since the subterm `?f (i + ?k)` produces an ugly higher-order unification problem.
-- (Although the `simpNF` linter does not complain.)
-- See: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/complete_lattice.20and.20has_sup/near/316497982
@[to_dual existing]
/-
**iInf_iSup_ge_nat_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_iSup_ge_nat_add : forall (f : Nat -> α) (k : Nat), ⨅ n, ⨆ i >= n, f (
i + k) = ⨅ n, ⨆ i >= n, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_iInf_ge_nat_add`：iSup_iInf_ge_nat_add (f : Nat -> α) (k : Nat) : ⨆ 
n, ⨅ i >= n, f (i + k) = ⨆ n, ⨅ i >= n, f i
-/
theorem iInf_iSup_ge_nat_add :
    ∀ (f : ℕ → α) (k : ℕ), ⨅ n, ⨆ i ≥ n, f (i + k) = ⨅ n, ⨆ i ≥ n, f i :=
  @iSup_iInf_ge_nat_add αᵒᵈ _

@[to_dual inf_iInf_nat_succ]
/-
**sup_iSup_nat_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_iSup_nat_succ (u : Nat -> α) : (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ i, u i
参数：u : Nat -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_union`：iSup_union {f : β -> α} {s t : Set β} : ⨆ x in s union t, f 
x = (⨆ x in s, f x) ⊔ ⨆ x in t, f x
· 使用定理 `iSup_singleton`：iSup_singleton {f : β -> α} {b : β} : ⨆ x in (singleton 
b : Set β), f x = f b
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
· 使用定理 `Nat.zero_union_range_succ`：zero_union_range_succ : {0} union range succ 
= univ
· 使用定理 `iSup_univ`：iSup_univ {f : β -> α} : ⨆ x in (univ : Set β), f x = ⨆ x, f 
x
-/
theorem sup_iSup_nat_succ (u : ℕ → α) : (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ i, u i :=
  calc
    (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ x ∈ {0} ∪ range Nat.succ, u x := by
      { rw [iSup_union, iSup_singleton, iSup_range] }
    _ = ⨆ i, u i := by rw [Nat.zero_union_range_succ, iSup_univ]

@[to_dual]
/-
**iInf_nat_gt_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_nat_gt_zero_eq (f : Nat -> α) : ⨅ i > 0, f i = ⨅ i, f (i + 1)
参数：f : Nat -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
· 使用定理 `Nat.range_succ`：Set.range Nat.succ = {i | 0 < i}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInf_nat_gt_zero_eq (f : ℕ → α) : ⨅ i > 0, f i = ⨅ i, f (i + 1) := by
  rw [← iInf_range, Nat.range_succ]
  simp

end

/-!
### Instances
-/

section CompleteLattice

variable [CompleteLattice α] {a : α} {s : Set α}

/-- This is a weaker version of `sup_sInf_eq` -/
@[to_dual iSup_inf_le_inf_sSup /-- This is a weaker version of `inf_sSup_eq` -/]
/-
**sup_sInf_le_iInf_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sInf_le_iInf_sup : a ⊔ sInf s <= ⨅ b in s, a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
This is a weaker version of `sup_sInf_eq`
-/
theorem sup_sInf_le_iInf_sup : a ⊔ sInf s ≤ ⨅ b ∈ s, a ⊔ b :=
  le_iInf₂ fun _ h => sup_le_sup_left (sInf_le h) _

/-- This is a weaker version of `sInf_sup_eq` -/
@[to_dual iSup_inf_le_sSup_inf /-- This is a weaker version of `sSup_inf_eq` -/]
/-
**sInf_sup_le_iInf_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sInf_sup_le_iInf_sup : sInf s ⊔ a <= ⨅ b in s, b ⊔ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `sup_le_sup_right`：sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
This is a weaker version of `sInf_sup_eq`
-/
theorem sInf_sup_le_iInf_sup : sInf s ⊔ a ≤ ⨅ b ∈ s, b ⊔ a :=
  le_iInf₂ fun _ h => sup_le_sup_right (sInf_le h) _

@[to_dual]
/-
**iInf_sup_le_iInf_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_sup_le_iInf_sup (f : ι -> α) (a : α) : (⨅ i, f i) ⊔ a <= ⨅ i, (f i ⊔ 
a)
参数：f : ι -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `sup_le_sup_right`：sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem iInf_sup_le_iInf_sup (f : ι → α) (a : α) :
    (⨅ i, f i) ⊔ a ≤ ⨅ i, (f i ⊔ a) :=
  le_iInf fun i ↦ sup_le_sup_right (iInf_le f i) a

@[to_dual iSup_inf_le_inf_iSup]
/-
**sup_iInf_le_iInf_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_iInf_le_iInf_sup (f : ι -> α) (a : α) : a ⊔ (⨅ i, f i) <= ⨅ i, (a ⊔ f 
i)
参数：f : ι -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem sup_iInf_le_iInf_sup (f : ι → α) (a : α) :
    a ⊔ (⨅ i, f i) ≤ ⨅ i, (a ⊔ f i) :=
  le_iInf fun i ↦ sup_le_sup_left (iInf_le f i) a

@[to_dual]
/-
**biInf_sup_le_biInf_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：biInf_sup_le_biInf_sup (f : β -> α) (s : Set β) (a : α) : (⨅ i in s, f i) 
⊔ a <= ⨅ i in s, f i ⊔ a
参数：f : β -> α；s : Set β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `sup_le_sup_right`：sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c
· 使用定理 `biInf_le`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_8} {s 
: Set ι} (f : ι → α) {i : ι}, i ∈ s → ⨅ i ∈ s, f i ≤ f i
-/
lemma biInf_sup_le_biInf_sup (f : β → α) (s : Set β) (a : α) :
    (⨅ i ∈ s, f i) ⊔ a ≤ ⨅ i ∈ s, f i ⊔ a :=
  le_iInf₂ fun _ hi ↦ sup_le_sup_right (biInf_le f hi) a

@[to_dual biSup_inf_le_inf_biSup]
/-
**sup_biInf_le_biInf_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sup_biInf_le_biInf_sup (f : β -> α) (s : Set β) (a : α) : a ⊔ (⨅ i in s, f
 i) <= ⨅ i in s, a ⊔ f i
参数：f : β -> α；s : Set β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `biInf_le`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_8} {s 
: Set ι} (f : ι → α) {i : ι}, i ∈ s → ⨅ i ∈ s, f i ≤ f i
-/
lemma sup_biInf_le_biInf_sup (f : β → α) (s : Set β) (a : α) :
    a ⊔ (⨅ i ∈ s, f i) ≤ ⨅ i ∈ s, a ⊔ f i :=
  le_iInf₂ fun _ hi ↦ sup_le_sup_left (biInf_le f hi) a

@[to_dual le_iSup_inf_iSup]
/-
**iInf_sup_iInf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_sup_iInf_le (f g : ι -> α) : (⨅ i, f i) ⊔ ⨅ i, g i <= ⨅ i, f i ⊔ g i
参数：f g : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem iInf_sup_iInf_le (f g : ι → α) : (⨅ i, f i) ⊔ ⨅ i, g i ≤ ⨅ i, f i ⊔ g i :=
  sup_le (iInf_mono fun _ => le_sup_left) (iInf_mono fun _ => le_sup_right)

@[to_dual]
/-
**disjoint_sSup_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_sSup_left {a : Set α} {b : α} (d : Disjoint (sSup a) b) {i} (hi :
 i in a) : Disjoint i b
参数：d : Disjoint (sSup a) b；hi : i in a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iSup_inf_le_sSup_inf`：∀ {α : Type u_1} [inst : CompleteLattice α] {a : α
} {s : Set α}, ⨆ b ∈ s, b ⊓ a ≤ sSup s ⊓ a
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
-/
theorem disjoint_sSup_left {a : Set α} {b : α} (d : Disjoint (sSup a) b) {i} (hi : i ∈ a) :
    Disjoint i b :=
  disjoint_iff_inf_le.mpr (iSup₂_le_iff.1 (iSup_inf_le_sSup_inf.trans d.le_bot) i hi :)

@[to_dual]
/-
**disjoint_sSup_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_sSup_right {a : Set α} {b : α} (d : Disjoint b (sSup a)) {i} (hi 
: i in a) : Disjoint b i
参数：d : Disjoint b (sSup a)；hi : i in a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iSup_inf_le_inf_sSup`：∀ {α : Type u_1} [inst : CompleteLattice α] {a : α
} {s : Set α}, ⨆ b ∈ s, a ⊓ b ≤ a ⊓ sSup s
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
-/
theorem disjoint_sSup_right {a : Set α} {b : α} (d : Disjoint b (sSup a)) {i} (hi : i ∈ a) :
    Disjoint b i :=
  disjoint_iff_inf_le.mpr (iSup₂_le_iff.mp (iSup_inf_le_inf_sSup.trans d.le_bot) i hi :)

@[to_dual]
/-
**disjoint_of_sSup_disjoint_of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjoint_of_sSup_disjoint_of_le_of_le {a b : α} {c d : Set α} (hs : forall
 e in c, e <= a) (ht : forall e in d, e <= b) (hd : Disjoint a b) (he : ⊥ ∉ c ∨ 
⊥ ∉ d) : Disjoint c d
参数：hs : forall e in c, e <= a；ht : forall e in d, e <= b；hd : Disjoint a b；he : 
⊥ ∉ c ∨ ⊥ ∉ d。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma disjoint_of_sSup_disjoint_of_le_of_le {a b : α} {c d : Set α} (hs : ∀ e ∈ c, e ≤ a)
    (ht : ∀ e ∈ d, e ≤ b) (hd : Disjoint a b) (he : ⊥ ∉ c ∨ ⊥ ∉ d) : Disjoint c d := by
  grind

@[to_dual]
/-
**disjoint_of_sSup_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjoint_of_sSup_disjoint {a b : Set α} (hd : Disjoint (sSup a) (sSup b)) 
(he : ⊥ ∉ a ∨ ⊥ ∉ b) : Disjoint a b
参数：hd : Disjoint (sSup a) (sSup b)；he : ⊥ ∉ a ∨ ⊥ ∉ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `disjoint_of_sSup_disjoint_of_le_of_le`：disjoint_of_sSup_disjoint_of_le_o
f_le {a b : α} {c d : Set α} (hs : forall e in c, e <= a) (ht : forall e in d, e
 <= b) (hd : Disjoint a b) …
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
lemma disjoint_of_sSup_disjoint {a b : Set α} (hd : Disjoint (sSup a) (sSup b))
    (he : ⊥ ∉ a ∨ ⊥ ∉ b) : Disjoint a b :=
  disjoint_of_sSup_disjoint_of_le_of_le (fun _ hc ↦ le_sSup hc) (fun _ hc ↦ le_sSup hc) hd he

end CompleteLattice

namespace ULift

universe v

@[to_dual]
/-
**ULift.supSet** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：supSet [SupSet α] : SupSet (ULift.{v} α) where sSup s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance supSet [SupSet α] : SupSet (ULift.{v} α) where sSup s := ULift.up (sSup <| ULift.up ⁻¹' s)

@[to_dual]
/-
**ULift.down_sSup** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：down_sSup [SupSet α] (s : Set (ULift.{v} α)) : (sSup s).down = sSup (ULift
.up ⁻¹' s)
参数：s : Set (ULift.{v} α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem down_sSup [SupSet α] (s : Set (ULift.{v} α)) : (sSup s).down = sSup (ULift.up ⁻¹' s) := rfl

@[to_dual]
/-
**ULift.up_sSup** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：up_sSup [SupSet α] (s : Set α) : up (sSup s) = sSup (ULift.down ⁻¹' s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem up_sSup [SupSet α] (s : Set α) : up (sSup s) = sSup (ULift.down ⁻¹' s) := rfl

@[to_dual]
/-
**ULift.down_iSup** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：down_iSup [SupSet α] (f : ι -> ULift.{v} α) : (⨆ i, f i).down = ⨆ i, (f i)
.down
参数：f : ι -> ULift.{v} α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.preimage_eq_iff_eq_image`：preimage_eq_iff_eq_image {f : α -> β} (hf 
: Bijective f) {s t} : f ⁻¹' s = t ↔ s = f '' t
· 使用定理 `ULift.up_bijective`：up_bijective : Bijective (@up α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem down_iSup [SupSet α] (f : ι → ULift.{v} α) : (⨆ i, f i).down = ⨆ i, (f i).down :=
  congr_arg sSup <| (preimage_eq_iff_eq_image ULift.up_bijective).mpr <|
    Eq.symm (range_comp _ _).symm

@[to_dual]
/-
**ULift.up_iSup** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：up_iSup [SupSet α] (f : ι -> α) : up (⨆ i, f i) = ⨆ i, up (f i)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ULift.down_iSup`：down_iSup [SupSet α] (f : ι -> ULift.{v} α) : (⨆ i, f i
).down = ⨆ i, (f i).down
-/
theorem up_iSup [SupSet α] (f : ι → α) : up (⨆ i, f i) = ⨆ i, up (f i) :=
  congr_arg ULift.up <| (down_iSup _).symm
/-
**ULift.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：instCompleteLattice [CompleteLattice α] : CompleteLattice (ULift.{v} α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ULift.down_injective`：∀ {α : Type u_1}, Function.Injective ULift.down
-/
instance instCompleteLattice [CompleteLattice α] : CompleteLattice (ULift.{v} α) :=
  ULift.down_injective.completeLattice _ .rfl .rfl down_sup down_inf
    (fun s => by rw [sSup_eq_iSup', down_iSup, iSup_subtype''])
    (fun s => by rw [sInf_eq_iInf', down_iInf, iInf_subtype'']) down_top down_bot

end ULift

namespace PUnit

/-
**PUnit.instCompleteLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：instCompleteLinearOrder : CompleteLinearOrder PUnit where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanAlgebra.le_top`：∀ {α : Type u} [self : BooleanAlgebra α] (a : α),
 a ≤ ⊤
· 使用定理 `BooleanAlgebra.bot_le`：∀ {α : Type u} [self : BooleanAlgebra α] (a : α),
 ⊥ ≤ a
· 使用定理 `LinearOrder.le_total`：∀ {α : Type u_2} [self : LinearOrder α] (a b : α),
 a ≤ b ∨ b ≤ a
· 使用定理 `LinearOrder.compare_eq_compareOfLessAndEq`：∀ {α : Type u_2} [self : Line
arOrder α] (a b : α), compare a b = compareOfLessAndEq a b
-/
instance instCompleteLinearOrder : CompleteLinearOrder PUnit where
  __ := instBooleanAlgebra
  __ := instLinearOrder
  sSup := fun _ => unit
  sInf := fun _ => unit
  isLUB_sSup _ := ⟨top_mem_upperBounds _, bot_mem_lowerBounds _⟩
  isGLB_sInf _ := ⟨bot_mem_lowerBounds _, top_mem_upperBounds _⟩
  le_himp_iff := by intros; trivial
  himp_bot := by intros; trivial
  sdiff_le_iff := by intros; trivial
  top_sdiff := by intros; trivial

end PUnit

