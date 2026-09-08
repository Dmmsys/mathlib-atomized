/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.List.FinRange

/-!
# Instances for finite types

This file is a collection of basic `Fintype` instances for types such as `Fin`, `Prod` and pi types.
-/

@[expose] public section

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset

/-
**Fin.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Fin.fintype (n : Nat) : Fintype (Fin n)
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodup_finRange`：∀ (n : ℕ), (List.finRange n).Nodup
· 使用定理 `List.mem_finRange`：∀ {n : ℕ} (x : Fin n), x ∈ List.finRange n
-/
instance Fin.fintype (n : ℕ) : Fintype (Fin n) :=
  ⟨⟨List.finRange n, List.nodup_finRange n⟩, List.mem_finRange⟩
/-
**Fin.univ_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.univ_def (n : Nat) : (univ : Finset (Fin n)) = ⟨List.finRange n, List.
nodup_finRange n⟩
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fin.univ_def (n : ℕ) : (univ : Finset (Fin n)) = ⟨List.finRange n, List.nodup_finRange n⟩ :=
  rfl
/-
**Finset.univ_fin2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.univ_fin2 : (univ : Finset (Fin 2)) = {0, 1}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finset.univ_fin2 : (univ : Finset (Fin 2)) = {0, 1} := rfl
/-
**Finset.val_univ_fin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.val_univ_fin (n : Nat) : (Finset.univ : Finset (Fin n)).val = List.
finRange n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finset.val_univ_fin (n : ℕ) : (Finset.univ : Finset (Fin n)).val = List.finRange n := rfl

/-- See also `nonempty_encodable`, `nonempty_denumerable`. -/
/-
**nonempty_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fintype α)
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
See also `nonempty_encodable`, `nonempty_denumerable`.
-/
theorem nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fintype α) := by
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  exact ⟨.ofEquiv _ e.symm⟩
/-
**List.toFinset_finRange** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ (n : ℕ), (List.finRange n).toFinset = Finset.univ
参数：n : ℕ；List.finRange n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem List.toFinset_finRange (n : ℕ) : (List.finRange n).toFinset = Finset.univ := by
  ext; simp
/-
**Fin.univ_val_map** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), Multiset.map f Finset.univ.val =
 ↑(List.ofFn f)
参数：f : Fin n → α；List.ofFn f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_eq_map`：ofFn_eq_map {n} {f : Fin n -> α} : ofFn f = (finRange 
n).map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem Fin.univ_val_map {n : ℕ} (f : Fin n → α) :
    Finset.univ.val.map f = List.ofFn f := by
  simp [List.ofFn_eq_map, univ_def]
/-
**Fin.univ_image_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.univ_image_def {n : Nat} [DecidableEq α] (f : Fin n -> α) : Finset.uni
v.image f = (List.ofFn f).toFinset
参数：f : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.univ_val_map`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), Multiset.map
 f Finset.univ.val = ↑(List.ofFn f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Fin.univ_image_def {n : ℕ} [DecidableEq α] (f : Fin n → α) :
    Finset.univ.image f = (List.ofFn f).toFinset := by
  simp [Finset.image]
/-
**Fin.univ_map_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.univ_map_def {n : Nat} (f : Fin n ↪ α) : Finset.univ.map f = ⟨List.ofF
n f, List.nodup_ofFn.mpr f.injective⟩
参数：f : Fin n ↪ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodup_ofFn`：nodup_ofFn {n} {f : Fin n -> α} : Nodup (ofFn f) ↔ Func
tion.Injective f
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.univ_val_map`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), Multiset.map
 f Finset.univ.val = ↑(List.ofFn f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mk.congr_simp`：∀ {α : Type u_4} (val val_1 : Multiset α) (e_val :
 val = val_1) (nodup : val.Nodup),   { val := val, nodup := nodup } = { val := v
al_1, nodu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Fin.univ_map_def {n : ℕ} (f : Fin n ↪ α) :
    Finset.univ.map f = ⟨List.ofFn f, List.nodup_ofFn.mpr f.injective⟩ := by
  simp [Finset.map]

@[simp]
/-
**Fin.image_succAbove_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.image_succAbove_univ {n : Nat} (i : Fin (n + 1)) : univ.image i.succAb
ove = {i}ᶜ
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Fin.image_succAbove_univ {n : ℕ} (i : Fin (n + 1)) : univ.image i.succAbove = {i}ᶜ := by
  ext m
  simp

@[simp]
/-
**Fin.image_succ_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.image_succ_univ (n : Nat) : (univ : Finset (Fin n)).image Fin.succ = {
0}ᶜ
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succAbove_zero`：∀ {n : ℕ}, Fin.succAbove 0 = Fin.succ
· 使用定理 `Fin.image_succAbove_univ`：Fin.image_succAbove_univ {n : Nat} (i : Fin (n
 + 1)) : univ.image i.succAbove = {i}ᶜ
-/
theorem Fin.image_succ_univ (n : ℕ) : (univ : Finset (Fin n)).image Fin.succ = {0}ᶜ := by
  rw [← Fin.succAbove_zero, Fin.image_succAbove_univ]

@[simp]
/-
**Fin.image_castSucc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.image_castSucc (n : Nat) : (univ : Finset (Fin n)).image Fin.castSucc 
= {Fin.last n}ᶜ
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succAbove_last`：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
· 使用定理 `Fin.image_succAbove_univ`：Fin.image_succAbove_univ {n : Nat} (i : Fin (n
 + 1)) : univ.image i.succAbove = {i}ᶜ
-/
theorem Fin.image_castSucc (n : ℕ) :
    (univ : Finset (Fin n)).image Fin.castSucc = {Fin.last n}ᶜ := by
  rw [← Fin.succAbove_last, Fin.image_succAbove_univ]

/- The following three lemmas use `Finset.cons` instead of `insert` and `Finset.map` instead of
`Finset.image` to reduce proof obligations downstream. -/
/-- Embed `Fin n` into `Fin (n + 1)` by prepending zero to the `univ` -/
/-
**Fin.univ_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.univ_succ (n : Nat) : (univ : Finset (Fin (n + 1))) = Finset.cons 0 (u
niv.map ⟨Fin.succ, Fin.succ_injective _⟩) (by simp [map_eq_image])
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Fin.succ_injective`：succ_injective (n : Nat) : Injective (@Fin.succ n)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Fin.image_succ_univ`：Fin.image_succ_univ (n : Nat) : (univ : Finset (Fin
 n)).image Fin.succ = {0}ᶜ
· 使用定理 `Finset.cons.congr_simp`：∀ {α : Type u_1} (a a_1 : α) (e_a : a = a_1) (s 
s_1 : Finset α) (e_s : s = s_1) (h : a ∉ s),   Finset.cons a s h = Finset.cons a
_1 s_1 ⋯
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.insert_compl_self`：insert_compl_self (x : α) : insert x ({x}ᶜ : F
inset α) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Embed `Fin n` into `Fin (n + 1)` by prepending zero to the `univ`
-/
theorem Fin.univ_succ (n : ℕ) :
    (univ : Finset (Fin (n + 1))) =
      Finset.cons 0 (univ.map ⟨Fin.succ, Fin.succ_injective _⟩) (by simp [map_eq_image]) := by
  simp [map_eq_image]

/-- Embed `Fin n` into `Fin (n + 1)` by appending a new `Fin.last n` to the `univ` -/
/-
**Fin.univ_castSuccEmb** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.univ_castSuccEmb (n : Nat) : (univ : Finset (Fin (n + 1))) = Finset.co
ns (Fin.last n) (univ.map Fin.castSuccEmb) (by simp [map_eq_image])
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Fin.image_castSucc`：Fin.image_castSucc (n : Nat) : (univ : Finset (Fin n
)).image Fin.castSucc = {Fin.last n}ᶜ
· 使用定理 `Finset.cons.congr_simp`：∀ {α : Type u_1} (a a_1 : α) (e_a : a = a_1) (s 
s_1 : Finset α) (e_s : s = s_1) (h : a ∉ s),   Finset.cons a s h = Finset.cons a
_1 s_1 ⋯
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.insert_compl_self`：insert_compl_self (x : α) : insert x ({x}ᶜ : F
inset α) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Embed `Fin n` into `Fin (n + 1)` by appending a new `Fin.last n` to the `univ`
-/
theorem Fin.univ_castSuccEmb (n : ℕ) :
    (univ : Finset (Fin (n + 1))) =
      Finset.cons (Fin.last n) (univ.map Fin.castSuccEmb) (by simp [map_eq_image]) := by
  simp [map_eq_image]

/-- Embed `Fin n` into `Fin (n + 1)` by inserting
around a specified pivot `p : Fin (n + 1)` into the `univ` -/
/-
**Fin.univ_succAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.univ_succAbove (n : Nat) (p : Fin (n + 1)) : (univ : Finset (Fin (n + 
1))) = Finset.cons p (univ.map <| Fin.succAboveEmb p) (by simp)
参数：n : Nat；p : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Fin.image_succAbove_univ`：Fin.image_succAbove_univ {n : Nat} (i : Fin (n
 + 1)) : univ.image i.succAbove = {i}ᶜ
· 使用定理 `Finset.cons.congr_simp`：∀ {α : Type u_1} (a a_1 : α) (e_a : a = a_1) (s 
s_1 : Finset α) (e_s : s = s_1) (h : a ∉ s),   Finset.cons a s h = Finset.cons a
_1 s_1 ⋯
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.insert_compl_self`：insert_compl_self (x : α) : insert x ({x}ᶜ : F
inset α) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Embed `Fin n` into `Fin (n + 1)` by inserting
around a specified pivot `p : Fin (n + 1)` into the `univ`
-/
theorem Fin.univ_succAbove (n : ℕ) (p : Fin (n + 1)) :
    (univ : Finset (Fin (n + 1))) = Finset.cons p (univ.map <| Fin.succAboveEmb p) (by simp) := by
  simp [map_eq_image]
/-
**Fin.univ_image_get** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (l : List α), Finset.image l.get F
inset.univ = l.toFinset
参数：l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.univ_image_def`：Fin.univ_image_def {n : Nat} [DecidableEq α] (f : Fi
n n -> α) : Finset.univ.image f = (List.ofFn f).toFinset
· 使用定理 `List.ofFn_get`：∀ {α : Type u} (l : List α), List.ofFn l.get = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem Fin.univ_image_get [DecidableEq α] (l : List α) :
    Finset.univ.image l.get = l.toFinset := by
  simp [univ_image_def]
/-
**Fin.univ_image_getElem'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β] (l : List α) (f : α
 → β),   Finset.image (fun i => f l[↑i]) Finset.univ = (List.map f l).toFinset
参数：l : List α；f : α → β；fun i => f l[↑i]；List.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.univ_image_def`：Fin.univ_image_def {n : Nat} [DecidableEq α] (f : Fi
n n -> α) : Finset.univ.image f = (List.ofFn f).toFinset
· 使用定理 `List.ofFn_getElem_eq_map`：ofFn_getElem_eq_map {β : Type*} (l : List α) (
f : α -> β) : ofFn (fun i : Fin l.length => f <| l[(i : Nat)]) = l.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem Fin.univ_image_getElem' [DecidableEq β] (l : List α) (f : α → β) :
    Finset.univ.image (fun i : Fin l.length => f <| l[(i : Nat)]) = (l.map f).toFinset := by
  simp only [univ_image_def, List.ofFn_getElem_eq_map]
/-
**Fin.univ_image_get'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.univ_image_get' [DecidableEq β] (l : List α) (f : α -> β) : Finset.uni
v.image (f <| l.get ·) = (l.map f).toFinset
参数：l : List α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.univ_image_getElem'`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidab
leEq β] (l : List α) (f : α → β),   Finset.image (fun i => f l[↑i]) Finset.univ 
= (List.map f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Fin.univ_image_get' [DecidableEq β] (l : List α) (f : α → β) :
    Finset.univ.image (f <| l.get ·) = (l.map f).toFinset := by
  simp
/-
**Fin.eq_iff_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.eq_iff_eq_zero_iff (a b : Fin 2) : a = b ↔ (a = 0 ↔ b = 0)
参数：a b : Fin 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Fin.fin_two_eq_of_eq_zero_iff`：∀ {a b : Fin 2}, (a = 0 ↔ b = 0) → a = b
-/
lemma Fin.eq_iff_eq_zero_iff (a b : Fin 2) : a = b ↔ (a = 0 ↔ b = 0) :=
  ⟨by rintro rfl; rfl, fin_two_eq_of_eq_zero_iff⟩
/-
**Unique.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Unique.fintype {α : Type*} [Unique α] : Fintype α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
instance Unique.fintype {α : Type*} [Unique α] : Fintype α :=
  Fintype.ofSubsingleton default

/-- Short-circuit instance to decrease search for `Unique.fintype`,
since that relies on a subsingleton elimination for `Unique`. -/
/-
**Fintype.subtypeEq** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Fintype.subtypeEq (y : α) : Fintype { x // x = y }
参数：y : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Short-circuit instance to decrease search for `Unique.fintype`,
since that relies on a subsingleton elimination for `Unique`.
-/
instance Fintype.subtypeEq (y : α) : Fintype { x // x = y } :=
  Fintype.subtype {y} (by simp)

/-- Short-circuit instance to decrease search for `Unique.fintype`,
since that relies on a subsingleton elimination for `Unique`. -/
/-
**Fintype.subtypeEq'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Fintype.subtypeEq' (y : α) : Fintype { x // y = x }
参数：y : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Short-circuit instance to decrease search for `Unique.fintype`,
since that relies on a subsingleton elimination for `Unique`.
-/
instance Fintype.subtypeEq' (y : α) : Fintype { x // y = x } :=
  Fintype.subtype {y} (by simp [eq_comm])
/-
**Fintype.univ_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.univ_empty : @univ Empty _ = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.univ_empty : @univ Empty _ = ∅ :=
  rfl
/-
**Fintype.univ_pempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.univ_pempty : @univ PEmpty _ = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.univ_pempty : @univ PEmpty _ = ∅ :=
  rfl
/-
**Unit.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Unit.fintype : Fintype Unit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
instance Unit.fintype : Fintype Unit :=
  Fintype.ofSubsingleton ()
/-
**Fintype.univ_unit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.univ_unit : @univ Unit _ = {()}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.univ_unit : @univ Unit _ = {()} :=
  rfl
/-
**PUnit.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PUnit.fintype : Fintype PUnit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
instance PUnit.fintype : Fintype PUnit :=
  Fintype.ofSubsingleton PUnit.unit
/-
**Fintype.univ_punit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.univ_punit : @univ PUnit _ = {PUnit.unit}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.univ_punit : @univ PUnit _ = {PUnit.unit} :=
  rfl

@[simp]
/-
**Fintype.univ_bool** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.univ_bool : @univ Bool _ = {true, false}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.univ_bool : @univ Bool _ = {true, false} :=
  rfl

/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
@[instance_reducible]
/-
**Fintype.prodLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fintype.prodLeft {α β} [DecidableEq α] [Fintype (α × β)] [Nonempty β] : Fi
ntype α
参数：α × β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given that `α × β` is a fintype, `α` is also a fintype.
-/
def Fintype.prodLeft {α β} [DecidableEq α] [Fintype (α × β)] [Nonempty β] : Fintype α :=
  ⟨(@univ (α × β) _).image Prod.fst, fun a => by simp⟩

/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
@[instance_reducible]
/-
**Fintype.prodRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fintype.prodRight {α β} [DecidableEq β] [Fintype (α × β)] [Nonempty α] : F
intype β
参数：α × β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given that `α × β` is a fintype, `β` is also a fintype.
-/
def Fintype.prodRight {α β} [DecidableEq β] [Fintype (α × β)] [Nonempty α] : Fintype β :=
  ⟨(@univ (α × β) _).image Prod.snd, fun b => by simp⟩
/-
**ULift.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.fintype (α : Type*) [Fintype α] : Fintype (ULift α)
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance ULift.fintype (α : Type*) [Fintype α] : Fintype (ULift α) :=
  Fintype.ofEquiv _ Equiv.ulift.symm
/-
**PLift.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PLift.fintype (α : Type*) [Fintype α] : Fintype (PLift α)
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance PLift.fintype (α : Type*) [Fintype α] : Fintype (PLift α) :=
  Fintype.ofEquiv _ Equiv.plift.symm
/-
**PLift.fintypeProp** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PLift.fintypeProp (p : Prop) [Decidable p] : Fintype (PLift p)
参数：p : Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PLift.fintypeProp (p : Prop) [Decidable p] : Fintype (PLift p) :=
  ⟨if h : p then {⟨h⟩} else ∅, fun ⟨h⟩ => by simp [h]⟩
/-
**Quotient.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.fintype [Fintype α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α -> 
α -> Prop)] : Fintype (Quotient s)
参数：s : Setoid α；(· ≈ ·) : α -> α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
-/
instance Quotient.fintype [Fintype α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α → α → Prop)] :
    Fintype (Quotient s) :=
  Fintype.ofSurjective Quotient.mk'' Quotient.mk''_surjective
/-
**PSigma.fintypePropLeft** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PSigma.fintypePropLeft {α : Prop} {β : α -> Type*} [Decidable α] [forall a
, Fintype (β a)] : Fintype (Σ' a, β a)
参数：β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PSigma.fintypePropLeft {α : Prop} {β : α → Type*} [Decidable α] [∀ a, Fintype (β a)] :
    Fintype (Σ' a, β a) :=
  if h : α then Fintype.ofEquiv (β h) ⟨fun x => ⟨h, x⟩, PSigma.snd, fun _ => rfl, fun ⟨_, _⟩ => rfl⟩
  else ⟨∅, fun x => (h x.1).elim⟩
/-
**PSigma.fintypePropRight** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PSigma.fintypePropRight {α : Type*} {β : α -> Prop} [forall a, Decidable (
β a)] [Fintype α] : Fintype (Σ' a, β a)
参数：β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PSigma.fintypePropRight {α : Type*} {β : α → Prop} [∀ a, Decidable (β a)] [Fintype α] :
    Fintype (Σ' a, β a) :=
  Fintype.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
/-
**PSigma.fintypePropProp** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PSigma.fintypePropProp {α : Prop} {β : α -> Prop} [Decidable α] [forall a,
 Decidable (β a)] : Fintype (Σ' a, β a)
参数：β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PSigma.fintypePropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] :
    Fintype (Σ' a, β a) :=
  if h : ∃ a, β a then ⟨{⟨h.fst, h.snd⟩}, fun ⟨_, _⟩ => by simp⟩ else ⟨∅, fun ⟨x, y⟩ =>
    (h ⟨x, y⟩).elim⟩
/-
**pfunFintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：pfunFintype (p : Prop) [Decidable p] (α : p -> Type*) [forall hp, Fintype 
(α hp)] : Fintype (forall hp : p, α hp)
参数：p : Prop；α : p -> Type*；α hp。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pfunFintype (p : Prop) [Decidable p] (α : p → Type*) [∀ hp, Fintype (α hp)] :
    Fintype (∀ hp : p, α hp) :=
  if hp : p then Fintype.ofEquiv (α hp) ⟨fun a _ => a, fun f => f hp, fun _ => rfl, fun _ => rfl⟩
  else ⟨singleton fun h => (hp h).elim, fun h => mem_singleton.2
    (funext fun x => by contradiction)⟩

section Trunc

/-- For `s : Multiset α`, we can lift the existential statement that `∃ x, x ∈ s` to a `Trunc α`.
-/
/-
**truncOfMultisetExistsMem** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：truncOfMultisetExistsMem {α} (s : Multiset α) : (exists x, x in s) -> Trun
c α
参数：s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `s : Multiset α`, we can lift the existential statement that `∃ x, x ∈ s` to
 a `Trunc α`.
-/
def truncOfMultisetExistsMem {α} (s : Multiset α) : (∃ x, x ∈ s) → Trunc α :=
  Quotient.recOnSubsingleton s fun l h =>
    match l, h with
    | [], _ => False.elim (by tauto)
    | a :: _, _ => Trunc.mk a

/-- A `Nonempty` `Fintype` constructively contains an element.
-/
/-
**truncOfNonemptyFintype** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：truncOfNonemptyFintype (α) [Nonempty α] [Fintype α] : Trunc α
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Nonempty` `Fintype` constructively contains an element.
-/
def truncOfNonemptyFintype (α) [Nonempty α] [Fintype α] : Trunc α :=
  truncOfMultisetExistsMem Finset.univ.val (by simp)

/-- By iterating over the elements of a fintype, we can lift an existential statement `∃ a, P a`
to `Trunc (Σ' a, P a)`, containing data.
-/
/-
**truncSigmaOfExists** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：truncSigmaOfExists {α} [Fintype α] {P : α -> Prop} [DecidablePred P] (h : 
exists a, P a) : Trunc (Σ' a, P a)
参数：h : exists a, P a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
By iterating over the elements of a fintype, we can lift an existential statemen
t `∃ a, P a`
to `Trunc (Σ' a, P a)`, containing data.
-/
def truncSigmaOfExists {α} [Fintype α] {P : α → Prop} [DecidablePred P] (h : ∃ a, P a) :
    Trunc (Σ' a, P a) :=
  @truncOfNonemptyFintype (Σ' a, P a) ((Exists.elim h) fun a ha => ⟨⟨a, ha⟩⟩) _

end Trunc

namespace Multiset

variable [Fintype α] [Fintype β]

@[simp]
/-
**Multiset.count_univ** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_univ [DecidableEq α] (a : α) : count a Finset.univ.val = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.count_eq_one_of_mem`：count_eq_one_of_mem [DecidableEq α] {a : α
} {s : Multiset α} (d : Nodup s) (h : a in s) : count a s = 1
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem count_univ [DecidableEq α] (a : α) : count a Finset.univ.val = 1 :=
  count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _)

@[simp]
/-
**Multiset.map_univ_val_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_univ_val_equiv (e : α ≃ β) : map e univ.val = univ.val
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.map_univ_equiv`：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map
 f.toEmbedding = univ
· 使用定理 `Finset.map_val`：map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.m
ap f
· 使用定理 `Equiv.coe_toEmbedding`：coe_toEmbedding : (f.toEmbedding : α -> β) = f
-/
theorem map_univ_val_equiv (e : α ≃ β) :
    map e univ.val = univ.val := by
  rw [← congr_arg Finset.val (Finset.map_univ_equiv e), Finset.map_val, Equiv.coe_toEmbedding]

/-- For functions on finite sets, they are bijections iff they map universes into universes. -/
@[simp]
/-
**Multiset.bijective_iff_map_univ_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bijective_iff_map_univ_eq_univ (f : α -> β) : f.Bijective ↔ map f (Finset.
univ : Finset α).val = univ.val
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.map_univ_equiv`：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map
 f.toEmbedding = univ
· 使用定理 `Multiset.inj_on_of_nodup_map`：inj_on_of_nodup_map {f : α -> β} {s : Mult
iset α} : Nodup (map f s) -> forall x in s, forall y in s, f x = f y -> x = y
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Finset.mem_univ_val`：mem_univ_val : forall x, x in (univ : Finset α).1

--- 原说明 ---
For functions on finite sets, they are bijections iff they map universes into un
iverses.
-/
theorem bijective_iff_map_univ_eq_univ (f : α → β) :
    f.Bijective ↔ map f (Finset.univ : Finset α).val = univ.val :=
  ⟨fun bij ↦ congr_arg (·.val) (map_univ_equiv <| Equiv.ofBijective f bij),
    fun eq ↦ ⟨
      fun a₁ a₂ ↦ inj_on_of_nodup_map (eq.symm ▸ univ.nodup) _ (mem_univ a₁) _ (mem_univ a₂),
      fun b ↦ have ⟨a, _, h⟩ := mem_map.mp (eq.symm ▸ mem_univ_val b); ⟨a, h⟩⟩⟩

end Multiset

/-- Auxiliary definition to show `exists_seq_of_forall_finset_exists`. -/
/-
**seqOfForallFinsetExistsAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_4} →   [DecidableEq α] →     (P : α → Prop) → (r : α → α → Pro
p) → (∀ (s : Finset α), ∃ y, (∀ x ∈ s, P x) → P y ∧ ∀ x ∈ s, r x y) → ℕ → α
参数：P : α → Prop；r : α → α → Prop；∀ (s : Finset α), ∃ y, (∀ x ∈ s, P x) → P y ∧ ∀
 x ∈ s, r x y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition to show `exists_seq_of_forall_finset_exists`.
-/
noncomputable def seqOfForallFinsetExistsAux {α : Type*} [DecidableEq α] (P : α → Prop)
    (r : α → α → Prop) (h : ∀ s : Finset α, ∃ y, (∀ x ∈ s, P x) → P y ∧ ∀ x ∈ s, r x y) : ℕ → α
  | n =>
    Classical.choose
      (h
        (Finset.image (fun i : Fin n => seqOfForallFinsetExistsAux P r h i)
          (Finset.univ : Finset (Fin n))))

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m < n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
/-
**exists_seq_of_forall_finset_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_of_forall_finset_exists {α : Type*} (P : α -> Prop) (r : α -> α
 -> Prop) (h : forall s : Finset α, (forall x in s, P x) -> exists y, P y ∧ fora
ll x in s, r x y) : exists f : Nat -> α, (forall n, P (f n)) ∧ forall m n, m < n
 -> r (f m) (f n)
参数：P : α -> Prop；r : α -> α -> Prop；h : forall s : Finset α, (forall x in s, P x
) -> exists y, P y ∧ forall x in s, r x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `seqOfForallFinsetExistsAux.eq_1`：∀ {α : Type u_4} [inst : DecidableEq α]
 (P : α → Prop) (r : α → α → Prop)   (h : ∀ (s : Finset α), ∃ y, (∀ x ∈ s, P x) 
→ P y ∧ ∀ x ∈ s, r x …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)

--- 原说明 ---
Induction principle to build a sequence, by adding one point at a time satisfyin
g a given
relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point 
satisfying
some relation `r` with respect to all the points in `s`. Then one may construct 
a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m < n`.
We also ensure that all constructed points satisfy a given predicate `P`.
-/
theorem exists_seq_of_forall_finset_exists {α : Type*} (P : α → Prop) (r : α → α → Prop)
    (h : ∀ s : Finset α, (∀ x ∈ s, P x) → ∃ y, P y ∧ ∀ x ∈ s, r x y) :
    ∃ f : ℕ → α, (∀ n, P (f n)) ∧ ∀ m n, m < n → r (f m) (f n) := by
  classical
    have : Nonempty α := by
      rcases h ∅ (by simp) with ⟨y, _⟩
      exact ⟨y⟩
    choose! F hF using h
    have h' : ∀ s : Finset α, ∃ y, (∀ x ∈ s, P x) → P y ∧ ∀ x ∈ s, r x y := fun s => ⟨F s, hF s⟩
    set f := seqOfForallFinsetExistsAux P r h' with hf
    have A : ∀ n : ℕ, P (f n) := by
      intro n
      induction n using Nat.strong_induction_on with | _ n IH
      have IH' : ∀ x : Fin n, P (f x) := fun n => IH n.1 n.2
      rw [hf, seqOfForallFinsetExistsAux]
      exact
        (Classical.choose_spec
            (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n))))
            (by simp [IH'])).1
    refine ⟨f, A, fun m n hmn => ?_⟩
    conv_rhs => rw [hf]
    rw [seqOfForallFinsetExistsAux]
    apply
      (Classical.choose_spec
          (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n)))) (by simp [A])).2
    exact Finset.mem_image.2 ⟨⟨m, hmn⟩, Finset.mem_univ _, rfl⟩

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
symmetric relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m ≠ n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
/-
**exists_seq_of_forall_finset_exists'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_of_forall_finset_exists' {α : Type*} (P : α -> Prop) (r : α -> 
α -> Prop) [Std.Symm r] (h : forall s : Finset α, (forall x in s, P x) -> exists
 y, P y ∧ forall x in s, r x y) : exists f : Nat -> α, (forall n, P (f n)) ∧ Pai
rwise (r on f)
参数：P : α -> Prop；r : α -> α -> Prop；h : forall s : Finset α, (forall x in s, P x
) -> exists y, P y ∧ forall x in s, r x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_of_forall_finset_exists`：exists_seq_of_forall_finset_exists {
α : Type*} (P : α -> Prop) (r : α -> α -> Prop) (h : forall s : Finset α, (foral
l x in s, P x) -> exists…

--- 原说明 ---
Induction principle to build a sequence, by adding one point at a time satisfyin
g a given
symmetric relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point 
satisfying
some relation `r` with respect to all the points in `s`. Then one may construct 
a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m ≠ n`.
We also ensure that all constructed points satisfy a given predicate `P`.
-/
theorem exists_seq_of_forall_finset_exists' {α : Type*} (P : α → Prop) (r : α → α → Prop)
    [Std.Symm r] (h : ∀ s : Finset α, (∀ x ∈ s, P x) → ∃ y, P y ∧ ∀ x ∈ s, r x y) :
    ∃ f : ℕ → α, (∀ n, P (f n)) ∧ Pairwise (r on f) := by
  rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩
  refine ⟨f, hf, fun m n hmn => ?_⟩
  grind +splitIndPred
