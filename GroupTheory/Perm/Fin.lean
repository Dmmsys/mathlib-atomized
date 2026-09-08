/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yi Yuan
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Permutations of `Fin n`
-/

@[expose] public section

assert_not_exists LinearMap

open Equiv

/-- Permutations of `Fin (n + 1)` are equivalent to fixing a single
`Fin (n + 1)` and permuting the remaining with a `Perm (Fin n)`.
The fixed `Fin (n + 1)` is swapped with `0`. -/
/-
**Equiv.Perm.decomposeFin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.Perm.decomposeFin {n : Nat} : Perm (Fin n.succ) ≃ Fin n.succ × Perm 
(Fin n)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Permutations of `Fin (n + 1)` are equivalent to fixing a single
`Fin (n + 1)` and permuting the remaining with a `Perm (Fin n)`.
The fixed `Fin (n + 1)` is swapped with `0`.
-/
def Equiv.Perm.decomposeFin {n : ℕ} : Perm (Fin n.succ) ≃ Fin n.succ × Perm (Fin n) :=
  ((Equiv.permCongr <| finSuccEquiv n).trans Equiv.Perm.decomposeOption).trans
    (Equiv.prodCongr (finSuccEquiv n).symm (Equiv.refl _))

@[simp]
/-
**Equiv.Perm.decomposeFin_symm_of_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.decomposeFin_symm_of_refl {n : Nat} (p : Fin (n + 1)) : Equiv.P
erm.decomposeFin.symm (p, Equiv.refl _) = swap 0 p
参数：p : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.prodCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_1
1} {β₂ : Type u_12} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂),   ⇑(e₁.prodCongr e₂) = Prod.m
ap ⇑e₁ ⇑e₂
· 使用定理 `Equiv.Perm.decomposeOption_symm_apply`：∀ {α : Type u_1} [inst : Decidabl
eEq α] (i : Option α × Equiv.Perm α),   Equiv.Perm.decomposeOption.symm i = Equi
v.swap none i.1 * Equiv.opt…
· 使用定理 `Equiv.optionCongr_refl`：optionCongr_refl : optionCongr (Equiv.refl α) = 
Equiv.refl _
· 使用定理 `Equiv.refl_trans`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), (Equiv.refl α
).trans e = e
· 使用定理 `Equiv.trans_swap_trans_symm`：trans_swap_trans_symm [DecidableEq β] (a b 
: β) (e : α ≃ β) : (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b
)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finSuccEquiv_symm_none`：finSuccEquiv_symm_none : (finSuccEquiv n).symm n
one = 0
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Equiv.Perm.decomposeFin_symm_of_refl {n : ℕ} (p : Fin (n + 1)) :
    Equiv.Perm.decomposeFin.symm (p, Equiv.refl _) = swap 0 p := by
  simp [Equiv.Perm.decomposeFin, Equiv.permCongr_def, pull_end]

@[simp]
/-
**Equiv.Perm.decomposeFin_symm_of_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.decomposeFin_symm_of_one {n : Nat} (p : Fin (n + 1)) : Equiv.Pe
rm.decomposeFin.symm (p, 1) = swap 0 p
参数：p : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.decomposeFin_symm_of_refl`：Equiv.Perm.decomposeFin_symm_of_re
fl {n : Nat} (p : Fin (n + 1)) : Equiv.Perm.decomposeFin.symm (p, Equiv.refl _) 
= swap 0 p
-/
theorem Equiv.Perm.decomposeFin_symm_of_one {n : ℕ} (p : Fin (n + 1)) :
    Equiv.Perm.decomposeFin.symm (p, 1) = swap 0 p :=
  Equiv.Perm.decomposeFin_symm_of_refl p

@[simp]
/-
**Equiv.Perm.decomposeFin_symm_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.decomposeFin_symm_apply_zero {n : Nat} (p : Fin (n + 1)) (e : P
erm (Fin n)) : Equiv.Perm.decomposeFin.symm (p, e) 0 = p
参数：p : Fin (n + 1)；e : Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.prodCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_1
1} {β₂ : Type u_12} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂),   ⇑(e₁.prodCongr e₂) = Prod.m
ap ⇑e₁ ⇑e₂
· 使用定理 `Equiv.Perm.decomposeOption_symm_apply`：∀ {α : Type u_1} [inst : Decidabl
eEq α] (i : Option α × Equiv.Perm α),   Equiv.Perm.decomposeOption.symm i = Equi
v.swap none i.1 * Equiv.opt…
· 使用定理 `Equiv.permCongr_mul`：∀ {α : Type u_4} {β : Type u_5} (e : α ≃ β) (p q : 
Equiv.Perm α), e.permCongr (p * q) = e.permCongr p * e.permCongr q
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Equiv.optionCongr_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) (a 
: Option α), e.optionCongr a = Option.map (⇑e) a
· 使用定理 `finSuccEquiv_symm_none`：finSuccEquiv_symm_none : (finSuccEquiv n).symm n
one = 0
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Equiv.Perm.decomposeFin_symm_apply_zero {n : ℕ} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p, e) 0 = p := by simp [Equiv.Perm.decomposeFin]

@[simp]
/-
**Equiv.Perm.decomposeFin_symm_apply_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.decomposeFin_symm_apply_succ {n : Nat} (e : Perm (Fin n)) (p : 
Fin (n + 1)) (x : Fin n) : Equiv.Perm.decomposeFin.symm (p, e) x.succ = swap 0 p
 (e x).succ
参数：e : Perm (Fin n)；p : Fin (n + 1)；x : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.prodCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_1
1} {β₂ : Type u_12} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂),   ⇑(e₁.prodCongr e₂) = Prod.m
ap ⇑e₁ ⇑e₂
· 使用定理 `Equiv.Perm.decomposeOption_symm_apply`：∀ {α : Type u_1} [inst : Decidabl
eEq α] (i : Option α × Equiv.Perm α),   Equiv.Perm.decomposeOption.symm i = Equi
v.swap none i.1 * Equiv.opt…
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `Equiv.permCongr_mul`：∀ {α : Type u_4} {β : Type u_5} (e : α ≃ β) (p q : 
Equiv.Perm α), e.permCongr (p * q) = e.permCongr p * e.permCongr q
· 使用定理 `Equiv.permCongr_refl`：∀ {α' : Type u_1} {β' : Type u_2} (e : α' ≃ β'), e
.permCongr (Equiv.refl α') = Equiv.refl β'
· 使用定理 `finSuccEquiv_succ`：finSuccEquiv_succ (m : Fin n) : (finSuccEquiv n) m.su
cc = some m
· 使用定理 `Equiv.optionCongr_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) (a 
: Option α), e.optionCongr a = Option.map (⇑e) a
· 使用定理 `finSuccEquiv_symm_some`：finSuccEquiv_symm_some (m : Fin n) : (finSuccEqu
iv n).symm (some m) = m.succ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `finSuccEquiv_symm_none`：finSuccEquiv_symm_none : (finSuccEquiv n).symm n
one = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem Equiv.Perm.decomposeFin_symm_apply_succ {n : ℕ} (e : Perm (Fin n)) (p : Fin (n + 1))
    (x : Fin n) : Equiv.Perm.decomposeFin.symm (p, e) x.succ = swap 0 p (e x).succ := by
  refine Fin.cases ?_ ?_ p
  · simp [Equiv.Perm.decomposeFin]
  · intro i
    by_cases h : i = e x
    · simp [h, Equiv.Perm.decomposeFin]
    · simp [Equiv.Perm.decomposeFin, swap_apply_def, Ne.symm h]

@[simp]
/-
**Equiv.Perm.decomposeFin_symm_apply_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.decomposeFin_symm_apply_one {n : Nat} (e : Perm (Fin (n + 1))) 
(p : Fin (n + 2)) : Equiv.Perm.decomposeFin.symm (p, e) 1 = swap 0 p (e 0).succ
参数：e : Perm (Fin (n + 1))；p : Fin (n + 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_zero_eq_one`：∀ {n : ℕ}, Fin.succ 0 = 1
· 使用定理 `Equiv.Perm.decomposeFin_symm_apply_succ`：Equiv.Perm.decomposeFin_symm_ap
ply_succ {n : Nat} (e : Perm (Fin n)) (p : Fin (n + 1)) (x : Fin n) : Equiv.Perm
.decomposeFin.symm (p, e) x.s…
-/
theorem Equiv.Perm.decomposeFin_symm_apply_one {n : ℕ} (e : Perm (Fin (n + 1))) (p : Fin (n + 2)) :
    Equiv.Perm.decomposeFin.symm (p, e) 1 = swap 0 p (e 0).succ := by
  rw [← Fin.succ_zero_eq_one, Equiv.Perm.decomposeFin_symm_apply_succ e p 0]

@[simp]
/-
**Equiv.Perm.decomposeFin.symm_sign** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.decomposeFin.symm_sign {n : Nat} (p : Fin (n + 1)) (e : Perm (F
in n)) : Perm.sign (Equiv.Perm.decomposeFin.symm (p, e)) = ite (p = 0) 1 (-1) * 
Perm.sign e
参数：p : Fin (n + 1)；e : Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.prodCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_1
1} {β₂ : Type u_12} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂),   ⇑(e₁.prodCongr e₂) = Prod.m
ap ⇑e₁ ⇑e₂
· 使用定理 `Equiv.Perm.decomposeOption_symm_apply`：∀ {α : Type u_1} [inst : Decidabl
eEq α] (i : Option α × Equiv.Perm α),   Equiv.Perm.decomposeOption.symm i = Equi
v.swap none i.1 * Equiv.opt…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `Equiv.permCongr_mul`：∀ {α : Type u_4} {β : Type u_5} (e : α ≃ β) (p q : 
Equiv.Perm α), e.permCongr (p * q) = e.permCongr p * e.permCongr q
· 使用定理 `Equiv.permCongr_refl`：∀ {α' : Type u_1} {β' : Type u_2} (e : α' ≃ β'), e
.permCongr (Equiv.refl α') = Equiv.refl β'
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `Equiv.Perm.sign_refl`：sign_refl : sign (Equiv.refl α) = 1
· 使用定理 `Equiv.Perm.sign_permCongr`：sign_permCongr (e : α ≃ β) (p : Perm α) : sig
n (e.permCongr p) = sign p
· 使用定理 `Equiv.optionCongr_sign`：Equiv.optionCongr_sign {α : Type*} [DecidableEq 
α] [Fintype α] (e : Perm α) : Perm.sign e.optionCongr = Perm.sign e
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `finSuccEquiv_succ`：finSuccEquiv_succ (m : Fin n) : (finSuccEquiv n) m.su
cc = some m
· 使用定理 `Equiv.Perm.sign_swap'`：sign_swap' {x y : α} : sign (swap x y) = if x = y
 then 1 else -1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
（共 31 条，此处仅展示前 30 条）
-/
theorem Equiv.Perm.decomposeFin.symm_sign {n : ℕ} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Perm.sign (Equiv.Perm.decomposeFin.symm (p, e)) = ite (p = 0) 1 (-1) * Perm.sign e := by
  refine Fin.cases ?_ ?_ p <;> simp [Equiv.Perm.decomposeFin]

/-- The set of all permutations of `Fin (n + 1)` can be constructed by augmenting the set of
permutations of `Fin n` by each element of `Fin (n + 1)` in turn. -/
/-
**Finset.univ_perm_fin_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.univ_perm_fin_succ {n : Nat} : @Finset.univ (Perm <| Fin n.succ) _ 
= (Finset.univ : Finset <| Fin n.succ × Perm (Fin n)).map Equiv.Perm.decomposeFi
n.symm.toEmbedding
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.univ_map_equiv_to_embedding`：univ_map_equiv_to_embedding {α β : T
ype*} [Fintype α] [Fintype β] (e : α ≃ β) : univ.map e.toEmbedding = univ

--- 原说明 ---
The set of all permutations of `Fin (n + 1)` can be constructed by augmenting th
e set of
permutations of `Fin n` by each element of `Fin (n + 1)` in turn.
-/
theorem Finset.univ_perm_fin_succ {n : ℕ} :
    @Finset.univ (Perm <| Fin n.succ) _ =
      (Finset.univ : Finset <| Fin n.succ × Perm (Fin n)).map
        Equiv.Perm.decomposeFin.symm.toEmbedding :=
  (Finset.univ_map_equiv_to_embedding _).symm

section CycleRange

/-! ### `cycleRange` section

Define the permutations `Fin.cycleRange i`, the cycle `(0 1 2 ... i)`.
-/


open Equiv.Perm

/-
**finRotate_succ_eq_decomposeFin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finRotate_succ_eq_decomposeFin {n : Nat} : finRotate n.succ = decomposeFin
.symm (1, finRotate n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `finRotate_one`：finRotate_one : finRotate 1 = Equiv.refl _
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Equiv.Perm.decomposeFin_symm_of_refl`：Equiv.Perm.decomposeFin_symm_of_re
fl {n : Nat} (p : Fin (n + 1)) : Equiv.Perm.decomposeFin.symm (p, Equiv.refl _) 
= swap 0 p
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
· 使用定理 `Equiv.Perm.decomposeFin_symm_apply_zero`：Equiv.Perm.decomposeFin_symm_ap
ply_zero {n : Nat} (p : Fin (n + 1)) (e : Perm (Fin n)) : Equiv.Perm.decomposeFi
n.symm (p, e) 0 = p
· 使用定理 `coe_finRotate`：coe_finRotate (i : Fin n.succ) : (finRotate n.succ i : Na
t) = if i = Fin.last n then (0 : Nat) else i + 1
· 使用定理 `Equiv.Perm.decomposeFin_symm_apply_succ`：Equiv.Perm.decomposeFin_symm_ap
ply_succ {n : Nat} (e : Perm (Fin n)) (p : Fin (n + 1)) (x : Fin n) : Equiv.Perm
.decomposeFin.symm (p, e) x.s…
· 使用定理 `if_congr`：if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y
 = ite Q u v
· 使用定理 `Fin.succ_eq_last_succ`：∀ {n : ℕ} {i : Fin n.succ}, i.succ = Fin.last (n 
+ 1) ↔ i = Fin.last n
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Fin.last_add_one`：∀ (n : ℕ), Fin.last n + 1 = 0
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
（共 38 条，此处仅展示前 30 条）
-/
theorem finRotate_succ_eq_decomposeFin {n : ℕ} :
    finRotate n.succ = decomposeFin.symm (1, finRotate n) := by
  ext i
  cases n; · simp
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  rw [coe_finRotate, decomposeFin_symm_apply_succ, if_congr i.succ_eq_last_succ rfl rfl]
  split_ifs with h
  · simp [h]
  · rw [Fin.val_succ, Function.Injective.map_swap Fin.val_injective, Fin.val_succ, coe_finRotate,
      if_neg h, Fin.val_zero, Fin.val_one,
      swap_apply_of_ne_of_ne (Nat.succ_ne_zero _) (Nat.succ_succ_ne_one _)]

@[simp]
/-
**sign_finRotate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_finRotate (n : Nat) : Perm.sign (finRotate n) = (-1) ^ (n - 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_refl`：sign_refl : sign (Equiv.refl α) = 1
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `finRotate_one`：finRotate_one : finRotate 1 = Equiv.refl _
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `finRotate_succ_eq_decomposeFin`：finRotate_succ_eq_decomposeFin {n : Nat}
 : finRotate n.succ = decomposeFin.symm (1, finRotate n)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Equiv.Perm.decomposeFin.symm_sign`：Equiv.Perm.decomposeFin.symm_sign {n 
: Nat} (p : Fin (n + 1)) (e : Perm (Fin n)) : Perm.sign (Equiv.Perm.decomposeFin
.symm (p, e)) = ite (p …
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib`：∀ {n m : ℕ} [NeZero n] [inst : NeZer
o (OfNat.ofNat m)], NeZero (OfNat.ofNat m)
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem sign_finRotate (n : ℕ) : Perm.sign (finRotate n) = (-1) ^ (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih =>
      rw [finRotate_succ_eq_decomposeFin]
      simp [ih, pow_succ]

@[simp]
/-
**support_finRotate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：support_finRotate {n : Nat} : support (finRotate (n + 2)) = Finset.univ
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
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib`：∀ {n m : ℕ} [NeZero n] [inst : NeZer
o (OfNat.ofNat m)], NeZero (OfNat.ofNat m)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_finRotate {n : ℕ} : support (finRotate (n + 2)) = Finset.univ := by
  ext
  simp
/-
**support_finRotate_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：support_finRotate_of_le {n : Nat} (h : 2 <= n) : support (finRotate n) = F
inset.univ
参数：h : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `support_finRotate`：support_finRotate {n : Nat} : support (finRotate (n +
 2)) = Finset.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem support_finRotate_of_le {n : ℕ} (h : 2 ≤ n) : support (finRotate n) = Finset.univ := by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm, support_finRotate]
/-
**isCycle_finRotate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCycle_finRotate {n : Nat} : IsCycle (finRotate (n + 2))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib`：∀ {n m : ℕ} [NeZero n] [inst : NeZer
o (OfNat.ofNat m)], NeZero (OfNat.ofNat m)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `coe_finRotate_of_ne_last`：coe_finRotate_of_ne_last {i : Fin n.succ} (h :
 i != Fin.last n) : (finRotate (n + 1) i : Nat) = i + 1
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Fin.val_last`：∀ (n : ℕ), ↑(Fin.last n) = n
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
-/
theorem isCycle_finRotate {n : ℕ} : IsCycle (finRotate (n + 2)) := by
  refine ⟨0, by simp, fun x hx' => ⟨x, ?_⟩⟩
  clear hx'
  obtain ⟨x, hx⟩ := x
  rw [zpow_natCast, Fin.ext_iff, Fin.val_mk]
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [pow_succ', Perm.mul_apply, coe_finRotate_of_ne_last, ih (lt_trans x.lt_succ_self hx)]
    rw [Ne, Fin.ext_iff, ih (lt_trans x.lt_succ_self hx), Fin.val_last]
    exact ne_of_lt (Nat.lt_of_succ_lt_succ hx)
/-
**isCycle_finRotate_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCycle_finRotate_of_le {n : Nat} (h : 2 <= n) : IsCycle (finRotate n)
参数：h : 2 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `isCycle_finRotate`：isCycle_finRotate {n : Nat} : IsCycle (finRotate (n +
 2))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isCycle_finRotate_of_le {n : ℕ} (h : 2 ≤ n) : IsCycle (finRotate n) := by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]
  exact isCycle_finRotate

@[simp]
/-
**cycleType_finRotate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cycleType_finRotate {n : Nat} : cycleType (finRotate (n + 2)) = {n + 2}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.IsCycle.cycleType`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] {σ : Equiv.Perm α},   σ.IsCycle → σ.cycleType = {σ.support.ca
rd}
· 使用定理 `isCycle_finRotate`：isCycle_finRotate {n : Nat} : IsCycle (finRotate (n +
 2))
· 使用定理 `support_finRotate`：support_finRotate {n : Nat} : support (finRotate (n +
 2)) = Finset.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card.eq_1`：∀ (α : Type u_4) [inst : Fintype α], Fintype.card α =
 Finset.univ.card
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
theorem cycleType_finRotate {n : ℕ} : cycleType (finRotate (n + 2)) = {n + 2} := by
  rw [isCycle_finRotate.cycleType, support_finRotate, ← Fintype.card, Fintype.card_fin]
/-
**cycleType_finRotate_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cycleType_finRotate_of_le {n : Nat} (h : 2 <= n) : cycleType (finRotate n)
 = {n}
参数：h : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `cycleType_finRotate`：cycleType_finRotate {n : Nat} : cycleType (finRotat
e (n + 2)) = {n + 2}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cycleType_finRotate_of_le {n : ℕ} (h : 2 ≤ n) : cycleType (finRotate n) = {n} := by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm, cycleType_finRotate]

namespace Fin

variable {n : ℕ} {i j : Fin n}

/-- `Fin.cycleRange i` is the cycle `(0 1 2 ... i)` leaving `(i+1 ... (n-1))` unchanged. -/
/-
**Fin.cycleRange** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：cycleRange {n : Nat} (i : Fin n) : Perm (Fin n)
参数：i : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fin.cycleRange i` is the cycle `(0 1 2 ... i)` leaving `(i+1 ... (n-1))` unchan
ged.
-/
def cycleRange {n : ℕ} (i : Fin n) : Perm (Fin n) :=
  (finRotate (i + 1)).extendDomain (castLEEmb (by lia)).toEquivRange
/-
**Fin.cycleRange_of_gt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_of_gt (h : i < j) : cycleRange i j = j
参数：h : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleRange.eq_1`：∀ {n : ℕ} (i : Fin n), i.cycleRange = (finRotate (↑
i + 1)).extendDomain (Fin.castLEEmb ⋯).toEquivRange
· 使用定理 `Equiv.Perm.extendDomain_apply_not_subtype`：∀ {α' : Type u_9} {β' : Type 
u_10} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Sub
type p)   {b : β'}, ¬p b → (e.e…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.range_castLE`：range_castLE {n k : Nat} (h : n <= k) : Set.range (cas
tLE h) = { i : Fin k | (i : Nat) < n }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem cycleRange_of_gt (h : i < j) : cycleRange i j = j := by
  rw [cycleRange, Perm.extendDomain_apply_not_subtype]
  simpa using h

set_option backward.isDefEq.respectTransparency false in
/-
**Fin.cycleRange_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_of_le [NeZero n] (h : i <= j) : cycleRange j i = if i = j then 
0 else i + 1
参数：h : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.range_castLE`：range_castLE {n k : Nat} (h : n <= k) : Set.range (cas
tLE h) = { i : Fin k | (i : Nat) < n }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cycleRange.eq_1`：∀ {n : ℕ} (i : Fin n), i.cycleRange = (finRotate (↑
i + 1)).extendDomain (Fin.castLEEmb ⋯).toEquivRange
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Perm.extendDomain_apply_subtype`：∀ {α' : Type u_9} {β' : Type u_10
} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype
 p)   {b : β'} (h : p b), (…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Function.Embedding.toEquivRange_apply`：Function.Embedding.toEquivRange_a
pply (a : α) : f.toEquivRange a = ⟨f a, Set.mem_range_self a⟩
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Fin.eq_of_val_eq`：∀ {n : ℕ} {i j : Fin n}, ↑i = ↑j → i = j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.castLT.congr_simp`：∀ {n m : ℕ} (i i_1 : Fin m) (e_i : i = i_1) (h : 
↑i < n), i.castLT h = i_1.castLT ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `finRotate_last`：finRotate_last : finRotate (n + 1) (Fin.last _) = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Fin.val_add_one_of_lt'`：val_add_one_of_lt' {n : Nat} {i : Fin n} (h : i 
+ 1 < n) : haveI
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
-/
theorem cycleRange_of_le [NeZero n] (h : i ≤ j) :
    cycleRange j i = if i = j then 0 else i + 1 := by
  have iin : i ∈ Set.range (castLEEmb (n := j + 1) (by lia)) := by
    simp; lia
  have : (castLEEmb (by lia)).toEquivRange (castLT i (by lia)) = ⟨i, iin⟩ := by
    simp [coe_castLEEmb]; rfl
  rw [cycleRange,
    (finRotate (j + 1)).extendDomain_apply_subtype (castLEEmb (by lia)).toEquivRange iin,
    Function.Embedding.toEquivRange_apply]
  split_ifs with ch
  · have : ((castLEEmb (by lia)).toEquivRange.symm ⟨i, iin⟩) = last j := by
      simpa only [coe_castLEEmb, ← this, symm_apply_apply] using eq_of_val_eq (by simp [ch])
    rw [this, finRotate_last]
    rfl
  · have hj1 : (i + 1).1 = i.1 + 1 := val_add_one_of_lt' (by lia)
    have hj2 : (i.castLT (by lia) + 1 : Fin (j + 1)).1 =
      (i.castLT (by lia) : Fin (j + 1)) + 1 := val_add_one_of_lt' (by simp; lia)
    exact eq_of_val_eq (by simp [← this, hj1, hj2])
/-
**Fin.coe_cycleRange_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_cycleRange_of_le (h : i <= j) : (cycleRange j i : Nat) = if i = j then
 0 else (i : Nat) + 1
参数：h : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleRange_of_le`：cycleRange_of_le [NeZero n] (h : i <= j) : cycleRa
nge j i = if i = j then 0 else i + 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Fin.val_add_one_of_lt`：∀ {n : ℕ} {i : Fin n.succ}, i < Fin.last n → ↑(i 
+ 1) = ↑i + 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem coe_cycleRange_of_le (h : i ≤ j) :
    (cycleRange j i : ℕ) = if i = j then 0 else (i : ℕ) + 1 := by
  rcases n with - | n
  · exact absurd le_rfl j.pos.not_ge
  rw [cycleRange_of_le h]
  split_ifs with h'
  · rfl
  exact
    val_add_one_of_lt
      (calc
        (i : ℕ) < j := Fin.lt_def.mp (lt_of_le_of_ne h h')
        _ ≤ n := Nat.lt_succ_iff.mp j.2)
/-
**Fin.cycleRange_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_of_lt [NeZero n] (h : i < j) : cycleRange j i = i + 1
参数：h : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleRange_of_le`：cycleRange_of_le [NeZero n] (h : i <= j) : cycleRa
nge j i = if i = j then 0 else i + 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem cycleRange_of_lt [NeZero n] (h : i < j) : cycleRange j i = i + 1 := by
  rw [cycleRange_of_le h.le, if_neg h.ne]
/-
**Fin.coe_cycleRange_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：coe_cycleRange_of_lt (h : i < j) : (cycleRange j i : Nat) = i + 1
参数：h : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.coe_cycleRange_of_le`：coe_cycleRange_of_le (h : i <= j) : (cycleRang
e j i : Nat) = if i = j then 0 else (i : Nat) + 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem coe_cycleRange_of_lt (h : i < j) : (cycleRange j i : ℕ) = i + 1 := by
  rw [coe_cycleRange_of_le h.le, if_neg h.ne]
/-
**Fin.cycleRange_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_of_eq [NeZero n] (h : i = j) : cycleRange j i = 0
参数：h : i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleRange_of_le`：cycleRange_of_le [NeZero n] (h : i <= j) : cycleRa
nge j i = if i = j then 0 else i + 1
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem cycleRange_of_eq [NeZero n] (h : i = j) : cycleRange j i = 0 := by
  rw [cycleRange_of_le h.le, if_pos h]

@[simp]
/-
**Fin.cycleRange_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_self [NeZero n] (i : Fin n) : cycleRange i i = 0
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.cycleRange_of_eq`：cycleRange_of_eq [NeZero n] (h : i = j) : cycleRan
ge j i = 0
-/
theorem cycleRange_self [NeZero n] (i : Fin n) : cycleRange i i = 0 :=
  cycleRange_of_eq rfl
/-
**Fin.cycleRange_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_apply [NeZero n] (i j : Fin n) : cycleRange i j = if j < i then
 j + 1 else if j = i then 0 else j
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Fin.cycleRange_of_lt`：cycleRange_of_lt [NeZero n] (h : i < j) : cycleRan
ge j i = i + 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Fin.cycleRange_of_eq`：cycleRange_of_eq [NeZero n] (h : i = j) : cycleRan
ge j i = 0
· 使用定理 `Fin.cycleRange_of_gt`：cycleRange_of_gt (h : i < j) : cycleRange i j = j
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem cycleRange_apply [NeZero n] (i j : Fin n) :
    cycleRange i j = if j < i then j + 1 else if j = i then 0 else j := by
  split_ifs with h₁ h₂
  · exact cycleRange_of_lt h₁
  · exact cycleRange_of_eq h₂
  · exact cycleRange_of_gt (lt_of_le_of_ne (le_of_not_gt h₁) (Ne.symm h₂))

@[simp]
/-
**Fin.cycleRange_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_zero (n : Nat) [NeZero n] : cycleRange (0 : Fin n) = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleRange_self`：cycleRange_self [NeZero n] (i : Fin n) : cycleRange
 i i = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.cycleRange_of_gt`：cycleRange_of_gt (h : i < j) : cycleRange i j = j
· 使用定理 `Equiv.Perm.one_apply`：one_apply (x) : (1 : Perm α) x = x
-/
theorem cycleRange_zero (n : ℕ) [NeZero n] : cycleRange (0 : Fin n) = 1 := by
  ext j
  rcases (Fin.zero_le j).eq_or_lt with rfl | hj
  · simp
  · rw [cycleRange_of_gt hj, one_apply]

@[simp]
/-
**Fin.cycleRange_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_last (n : Nat) : cycleRange (last n) = finRotate (n + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.coe_cycleRange_of_le`：coe_cycleRange_of_le (h : i <= j) : (cycleRang
e j i : Nat) = if i = j then 0 else (i : Nat) + 1
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用定理 `coe_finRotate`：coe_finRotate (i : Fin n.succ) : (finRotate n.succ i : Na
t) = if i = Fin.last n then (0 : Nat) else i + 1
-/
theorem cycleRange_last (n : ℕ) : cycleRange (last n) = finRotate (n + 1) := by
  ext i
  rw [coe_cycleRange_of_le (le_last _), coe_finRotate]

@[simp]
/-
**Fin.cycleRange_mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_mk_zero (h : 0 < n) : cycleRange ⟨0, h⟩ = 1
参数：h : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_pos`：of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x
· 使用定理 `Fin.cycleRange_zero`：cycleRange_zero (n : Nat) [NeZero n] : cycleRange (
0 : Fin n) = 1
-/
theorem cycleRange_mk_zero (h : 0 < n) : cycleRange ⟨0, h⟩ = 1 :=
  have : NeZero n := .of_pos h
  cycleRange_zero n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.sign_cycleRange** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：sign_cycleRange (i : Fin n) : Perm.sign (cycleRange i) = (-1) ^ (i : Nat)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_extendDomain`：sign_extendDomain (e : Perm α) {p : β -> P
rop} [DecidablePred p] (f : α ≃ Subtype p) : Equiv.Perm.sign (e.extendDomain f) 
= Equiv.Perm.sign …
· 使用定理 `sign_finRotate`：sign_finRotate (n : Nat) : Perm.sign (finRotate n) = (-1
) ^ (n - 1)
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sign_cycleRange (i : Fin n) : Perm.sign (cycleRange i) = (-1) ^ (i : ℕ) := by
  simp [cycleRange]

@[simp]
/-
**Fin.succAbove_cycleRange** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succAbove_cycleRange (i j : Fin n) : i.succ.succAbove (i.cycleRange j) = s
wap 0 i.succ j.succ
参数：i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.val_castSucc`：∀ {n : ℕ} (i : Fin n), ↑i.castSucc = ↑i
· 使用定理 `Fin.val_succ`：∀ {n : ℕ} (j : Fin n), ↑j.succ = ↑j + 1
· 使用定理 `Fin.val_add_one_of_lt`：∀ {n : ℕ} {i : Fin n.succ}, i < Fin.last n → ↑(i 
+ 1) = ↑i + 1
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用定理 `Fin.cycleRange_of_lt`：cycleRange_of_lt [NeZero n] (h : i < j) : cycleRan
ge j i = i + 1
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `Fin.succ_ne_zero`：∀ {n : ℕ} (k : Fin n), k.succ ≠ 0
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用引理 `Fin.succ_injective`：succ_injective (n : Nat) : Injective (@Fin.succ n)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.cycleRange_self`：cycleRange_self [NeZero n] (i : Fin n) : cycleRange
 i i = 0
· 使用定理 `Fin.castSucc_zero`：∀ {n : ℕ} [inst : NeZero n], Fin.castSucc 0 = 0
· 使用定理 `Fin.succ_pos`：∀ {n : ℕ} (a : Fin n), 0 < a.succ
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `Fin.cycleRange_of_gt`：cycleRange_of_gt (h : i < j) : cycleRange i j = j
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem succAbove_cycleRange (i j : Fin n) :
    i.succ.succAbove (i.cycleRange j) = swap 0 i.succ j.succ := by
  cases n
  · rcases j with ⟨_, ⟨⟩⟩
  rcases lt_trichotomy j i with (hlt | heq | hgt)
  · have : castSucc (j + 1) = j.succ := by
      ext
      rw [val_castSucc, val_succ, Fin.val_add_one_of_lt (lt_of_lt_of_le hlt i.le_last)]
    rw [Fin.cycleRange_of_lt hlt, Fin.succAbove_of_castSucc_lt, this, swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · exact (Fin.succ_injective _).ne hlt.ne
    · rw [Fin.lt_def]
      simpa [this] using hlt
  · rw [heq, Fin.cycleRange_self, Fin.succAbove_of_castSucc_lt, swap_apply_right, Fin.castSucc_zero]
    · rw [Fin.castSucc_zero]
      apply Fin.succ_pos
  · rw [Fin.cycleRange_of_gt hgt, Fin.succAbove_of_le_castSucc, swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · apply (Fin.succ_injective _).ne hgt.ne.symm
    · simpa [Fin.le_iff_val_le_val] using hgt

@[simp]
/-
**Fin.cycleRange_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_succAbove (i : Fin (n + 1)) (j : Fin n) : i.cycleRange (i.succA
bove j) = j.succ
参数：i : Fin (n + 1)；j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.cycleRange_of_lt`：cycleRange_of_lt [NeZero n] (h : i < j) : cycleRan
ge j i = i + 1
· 使用定理 `Fin.coeSucc_eq_succ`：∀ {n : ℕ} {a : Fin n}, a.castSucc + 1 = a.succ
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Fin.cycleRange_of_gt`：cycleRange_of_gt (h : i < j) : cycleRange i j = j
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
-/
theorem cycleRange_succAbove (i : Fin (n + 1)) (j : Fin n) :
    i.cycleRange (i.succAbove j) = j.succ := by
  rcases lt_or_ge (castSucc j) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.cycleRange_of_lt h, Fin.coeSucc_eq_succ]
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.cycleRange_of_gt (Fin.le_castSucc_iff.mp h)]

@[simp]
/-
**Fin.cycleRange_symm_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_symm_zero [NeZero n] (i : Fin n) : i.cycleRange.symm 0 = i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Fin.cycleRange_self`：cycleRange_self [NeZero n] (i : Fin n) : cycleRange
 i i = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleRange_symm_zero [NeZero n] (i : Fin n) : i.cycleRange.symm 0 = i :=
  i.cycleRange.injective (by simp)

@[simp]
/-
**Fin.cycleRange_symm_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleRange_symm_succ (i : Fin (n + 1)) (j : Fin n) : i.cycleRange.symm j.s
ucc = i.succAbove j
参数：i : Fin (n + 1)；j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Fin.cycleRange_succAbove`：cycleRange_succAbove (i : Fin (n + 1)) (j : Fi
n n) : i.cycleRange (i.succAbove j) = j.succ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleRange_symm_succ (i : Fin (n + 1)) (j : Fin n) :
    i.cycleRange.symm j.succ = i.succAbove j :=
  i.cycleRange.injective (by simp)

@[simp]
/-
**Fin.insertNth_apply_cycleRange_symm** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_apply_cycleRange_symm {α : Type*} (p : Fin (n + 1)) (a : α) (x :
 Fin n -> α) (j : Fin (n + 1)) : (p.insertNth a x : _ -> α) (p.cycleRange.symm j
) = (Fin.cons a x : _ -> α) j
参数：p : Fin (n + 1)；a : α；x : Fin n -> α；j : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleRange_symm_zero`：cycleRange_symm_zero [NeZero n] (i : Fin n) : 
i.cycleRange.symm 0 = i
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cycleRange_symm_succ`：cycleRange_symm_succ (i : Fin (n + 1)) (j : Fi
n n) : i.cycleRange.symm j.succ = i.succAbove j
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
-/
theorem insertNth_apply_cycleRange_symm {α : Type*} (p : Fin (n + 1)) (a : α) (x : Fin n → α)
    (j : Fin (n + 1)) :
    (p.insertNth a x : _ → α) (p.cycleRange.symm j) = (Fin.cons a x : _ → α) j := by
  cases j using Fin.cases <;> simp

@[simp]
/-
**Fin.insertNth_comp_cycleRange_symm** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_comp_cycleRange_symm {α : Type*} (p : Fin (n + 1)) (a : α) (x : 
Fin n -> α) : (p.insertNth a x ∘ p.cycleRange.symm : _ -> α) = Fin.cons a x
参数：p : Fin (n + 1)；a : α；x : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNth_apply_cycleRange_symm`：insertNth_apply_cycleRange_symm {α 
: Type*} (p : Fin (n + 1)) (a : α) (x : Fin n -> α) (j : Fin (n + 1)) : (p.inser
tNth a x : _ -> α) (p.cyc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insertNth_comp_cycleRange_symm {α : Type*} (p : Fin (n + 1)) (a : α) (x : Fin n → α) :
    (p.insertNth a x ∘ p.cycleRange.symm : _ → α) = Fin.cons a x := by
  ext j
  simp
/-
**Fin.cons_removeNth_eq_comp_cycleRange_symm** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_removeNth_eq_comp_cycleRange_symm {α : Type*} (x : Fin (n + 1) -> α) 
(p : Fin (n + 1)) : Fin.cons (x p) (p.removeNth x) = x ∘ p.cycleRange.symm
参数：x : Fin (n + 1) -> α；p : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.cycleRange_symm_zero`：cycleRange_symm_zero [NeZero n] (i : Fin n) : 
i.cycleRange.symm 0 = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Fin.cycleRange_symm_succ`：cycleRange_symm_succ (i : Fin (n + 1)) (j : Fi
n n) : i.cycleRange.symm j.succ = i.succAbove j
-/
theorem cons_removeNth_eq_comp_cycleRange_symm {α : Type*}
    (x : Fin (n + 1) → α) (p : Fin (n + 1)) :
    Fin.cons (x p) (p.removeNth x) = x ∘ p.cycleRange.symm := by
  ext i
  cases i using Fin.cons <;> simp [Fin.removeNth_apply]

@[simp]
/-
**Fin.cons_apply_cycleRange** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_apply_cycleRange {α : Type*} (a : α) (x : Fin n -> α) (p j : Fin (n +
 1)) : (Fin.cons a x : _ -> α) (p.cycleRange j) = (p.insertNth a x : _ -> α) j
参数：a : α；x : Fin n -> α；p j : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.insertNth_apply_cycleRange_symm`：insertNth_apply_cycleRange_symm {α 
: Type*} (p : Fin (n + 1)) (a : α) (x : Fin n -> α) (j : Fin (n + 1)) : (p.inser
tNth a x : _ -> α) (p.cyc…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem cons_apply_cycleRange {α : Type*} (a : α) (x : Fin n → α) (p j : Fin (n + 1)) :
    (Fin.cons a x : _ → α) (p.cycleRange j) = (p.insertNth a x : _ → α) j := by
  rw [← insertNth_apply_cycleRange_symm, Equiv.symm_apply_apply]

@[simp]
/-
**Fin.cons_comp_cycleRange** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_comp_cycleRange {α : Type*} (a : α) (x : Fin n -> α) (p : Fin (n + 1)
) : (Fin.cons a x : _ -> α) ∘ p.cycleRange = p.insertNth a x
参数：a : α；x : Fin n -> α；p : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_apply_cycleRange`：cons_apply_cycleRange {α : Type*} (a : α) (x 
: Fin n -> α) (p j : Fin (n + 1)) : (Fin.cons a x : _ -> α) (p.cycleRange j) = (
p.insertNth a x…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_comp_cycleRange {α : Type*} (a : α) (x : Fin n → α) (p : Fin (n + 1)) :
    (Fin.cons a x : _ → α) ∘ p.cycleRange = p.insertNth a x := by
  ext; simp
/-
**Fin.isCycle_cycleRange** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：isCycle_cycleRange [NeZero n] (h0 : i != 0) : IsCycle (cycleRange i)
参数：h0 : i != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.IsCycle.extendDomain`：∀ {α : Type u_2} {β : Type u_3} {g : Eq
uiv.Perm α} {p : β → Prop} [inst : DecidablePred p] (f : α ≃ Subtype p),   g.IsC
ycle → (g.extendDomai…
· 使用定理 `isCycle_finRotate`：isCycle_finRotate {n : Nat} : IsCycle (finRotate (n +
 2))
-/
theorem isCycle_cycleRange [NeZero n] (h0 : i ≠ 0) : IsCycle (cycleRange i) := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (h0 rfl).elim
  exact isCycle_finRotate.extendDomain _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.cycleType_cycleRange** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleType_cycleRange [NeZero n] (h0 : i != 0) : cycleType (cycleRange i) =
 {(i + 1 : Nat)}
参数：h0 : i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.cycleType_extendDomain`：cycleType_extendDomain {β : Type*} [F
intype β] [DecidableEq β] {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p) 
{g : Perm α} : cycleTyp…
· 使用定理 `cycleType_finRotate`：cycleType_finRotate {n : Nat} : cycleType (finRotat
e (n + 2)) = {n + 2}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleType_cycleRange [NeZero n] (h0 : i ≠ 0) :
    cycleType (cycleRange i) = {(i + 1 : ℕ)} := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (h0 rfl).elim
  simp [cycleRange]
/-
**Fin.isThreeCycle_cycleRange_two** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：isThreeCycle_cycleRange_two : IsThreeCycle (cycleRange 2 : Perm (Fin (n + 
3)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.IsThreeCycle.eq_1`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : DecidableEq α] (σ : Equiv.Perm α), σ.IsThreeCycle = (σ.cycleType = {3})
· 使用定理 `Fin.cycleType_cycleRange`：cycleType_cycleRange [NeZero n] (h0 : i != 0) 
: cycleType (cycleRange i) = {(i + 1 : Nat)}
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib`：∀ {n m : ℕ} [NeZero n] [inst : NeZer
o (OfNat.ofNat m)], NeZero (OfNat.ofNat m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.Simproc.add_eq_le`：∀ (a : ℕ) {b c : ℕ}, b ≤ c → (a + b = c) = (a = c
 - b)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem isThreeCycle_cycleRange_two : IsThreeCycle (cycleRange 2 : Perm (Fin (n + 3))) := by
  rw [IsThreeCycle, cycleType_cycleRange two_ne_zero]
  simp

end Fin

end CycleRange

section cycleIcc

/-! ### The permutation `cycleIcc`

In this section, we define the permutation `cycleIcc i j`, which is the cycle `(i i+1 .... j)`
leaving `(0 ... i-1)` and `(j+1 ... n-1)` unchanged when `i ≤ j` and returning the dummy value `id`
when `i > j`. In other words, it rotates elements in `[i, j]` one step to the right.
-/

namespace Fin

local instance {n : ℕ} {i : Fin n} : NeZero (n - i) := NeZero.of_pos (by lia)

variable {n : ℕ} {i j k : Fin n}

/-- `cycleIcc i j` is the cycle `(i i+1 ... j)` leaving `(0 ... i-1)` and `(j+1 ... n-1)`
unchanged when `i < j` and returning the dummy value `id` when `i > j`.
In other words, it rotates elements in `[i, j]` one step to the right.
-/
/- `cycleIcc` is defined in two steps:
1. The first part is `cycleRange ((j - i).castLT (sub_val_lt_sub hij))`, which is an element of
`Perm (Fin (n - i))`. It rotates the sequence `(0 1 ... j-i)` while leaving `(j-i+1 ... n-i)`
unchanged.
2. Since `natAdd_castLEEmb (Nat.sub_le n i) : Fin (n - i) ↪ Fin n` maps each `x` to `x + i`, we can
embed the first part into `Fin n` using `extendDomain` to obtain an element of `Perm (Fin n)`.
This yields the cycle `(i i+1 ... j)` while leaving `(0 ... i-1)` and `(j+1 ... n-1)` unchanged.
-/
/-
**Fin.cycleIcc** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：cycleIcc (i j : Fin n) : Perm (Fin n)
参数：i j : Fin n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val

--- 原说明 ---
`cycleIcc` is defined in two steps:
1. The first part is `cycleRange ((j - i).castLT (sub_val_lt_sub hij))`, which i
s an element of
`Perm (Fin (n - i))`. It rotates the sequence `(0 1 ... j-i)` while leaving `(j-
i+1 ... n-i)`
unchanged.
2. Since `natAdd_castLEEmb (Nat.sub_le n i) : Fin (n - i) ↪ Fin n` maps each `x`
 to `x + i`, we can
embed the first part into `Fin n` using `extendDomain` to obtain an element of `
Perm (Fin n)`.
This yields the cycle `(i i+1 ... j)` while leaving `(0 ... i-1)` and `(j+1 ... 
n-1)` unchanged.
-/
def cycleIcc (i j : Fin n) : Perm (Fin n) := if hij : i ≤ j then (cycleRange ((j - i).castLT
  (sub_val_lt_sub hij))).extendDomain (natAdd_castLEEmb (Nat.sub_le n i)).toEquivRange else 1

@[simp]
/-
**Fin.cycleIcc_def_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_def_le {i j : Fin n} (hij : i <= j) : cycleIcc i j = (cycleRange 
((j - i).castLT (sub_val_lt_sub hij))).extendDomain (natAdd_castLEEmb (Nat.sub_l
e n i)).toEquivRange
参数：hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cycleIcc_def_le {i j : Fin n} (hij : i ≤ j) : cycleIcc i j =
    (cycleRange ((j - i).castLT (sub_val_lt_sub hij))).extendDomain
      (natAdd_castLEEmb (Nat.sub_le n i)).toEquivRange := by simp [cycleIcc, hij]

@[simp]
/-
**Fin.cycleIcc_def_gt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_def_gt (hij : i < j) : cycleIcc j i = 1
参数：hij : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem cycleIcc_def_gt (hij : i < j) : cycleIcc j i = 1 := by
  simp [cycleIcc, hij]

@[simp]
/-
**Fin.cycleIcc_def_gt'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_def_gt' (hij : ¬ j <= i) : cycleIcc j i = 1
参数：hij : ¬ j <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleIcc_def_gt' (hij : ¬ j ≤ i) : cycleIcc j i = 1 := by
  simp [cycleIcc, hij]
/-
**Fin.cycleIcc_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_of_lt (h : k < i) : (cycleIcc i j) k = k
参数：h : k < i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.cycleIcc_def_le`：cycleIcc_def_le {i j : Fin n} (hij : i <= j) : cycl
eIcc i j = (cycleRange ((j - i).castLT (sub_val_lt_sub hij))).extendDomain (natA
dd_castLE…
· 使用定理 `Equiv.Perm.extendDomain_apply_not_subtype`：∀ {α' : Type u_9} {β' : Type 
u_10} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Sub
type p)   {b : β'}, ¬p b → (e.e…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Fin.range_natAdd_castLEEmb`：range_natAdd_castLEEmb {n m : Nat} (hmn : n 
<= m) : Set.range (natAdd_castLEEmb hmn) = {i | m - n <= i.1}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.cycleIcc_def_gt'`：cycleIcc_def_gt' (hij : ¬ j <= i) : cycleIcc j i =
 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleIcc_of_lt (h : k < i) : (cycleIcc i j) k = k := by
  by_cases hij : i ≤ j
  · simpa [hij] using Perm.extendDomain_apply_not_subtype _ _ (by
      simp [range_natAdd_castLEEmb]; lia)
  · simp [hij]
/-
**Fin.cycleIcc_to_cycleRange** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_to_cycleRange (hij : i <= j) (kin : k in Set.range (natAdd_castLE
Emb (Nat.sub_le n i))) : (cycleIcc i j) k = (natAdd_castLEEmb (Nat.sub_le n i)) 
(((j - i).castLT (sub_val_lt_sub hij)).cycleRange ((natAdd_castLEEmb (Nat.sub_le
 n i)).toEquivRange.symm ⟨k, kin⟩))
参数：hij : i <= j；kin : k in Set.range (natAdd_castLEEmb (Nat.sub_le n i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.cycleIcc_def_le`：cycleIcc_def_le {i j : Fin n} (hij : i <= j) : cycl
eIcc i j = (cycleRange ((j - i).castLT (sub_val_lt_sub hij))).extendDomain (natA
dd_castLE…
· 使用定理 `Equiv.Perm.extendDomain_apply_subtype`：∀ {α' : Type u_9} {β' : Type u_10
} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype
 p)   {b : β'} (h : p b), (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cycleIcc_to_cycleRange (hij : i ≤ j)
    (kin : k ∈ Set.range (natAdd_castLEEmb (Nat.sub_le n i))) : (cycleIcc i j) k =
    (natAdd_castLEEmb (Nat.sub_le n i)) (((j - i).castLT (sub_val_lt_sub hij)).cycleRange
    ((natAdd_castLEEmb (Nat.sub_le n i)).toEquivRange.symm ⟨k, kin⟩)) := by
  simp [hij, ((j - i).castLT (sub_val_lt_sub hij)).cycleRange.extendDomain_apply_subtype
    (natAdd_castLEEmb _).toEquivRange kin]

set_option backward.isDefEq.respectTransparency false in
/-
**Fin.cycleIcc_of_gt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_of_gt (h : j < k) : (cycleIcc i j) k = k
参数：h : j < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Fin.range_natAdd_castLEEmb`：range_natAdd_castLEEmb {n m : Nat} (hmn : n 
<= m) : Set.range (natAdd_castLEEmb hmn) = {i | m - n <= i.1}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Fin.addNatEmb_apply`：∀ {n : ℕ} (m : ℕ) (x : Fin n), (Fin.addNatEmb m) x 
= x.addNat m
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Fin.eq_of_val_eq`：∀ {n : ℕ} {i j : Fin n}, ↑i = ↑j → i = j
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val
· 使用引理 `Fin.cycleIcc_to_cycleRange`：cycleIcc_to_cycleRange (hij : i <= j) (kin :
 k in Set.range (natAdd_castLEEmb (Nat.sub_le n i))) : (cycleIcc i j) k = (natAd
d_castLEEmb (Nat…
· 使用定理 `Fin.cycleRange_of_gt`：cycleRange_of_gt (h : i < j) : cycleRange i j = j
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用定理 `Fin.sub_val_of_le`：∀ {n : ℕ} {a b : Fin n}, b ≤ a → ↑(a - b) = ↑a - ↑b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.cycleIcc_def_gt'`：cycleIcc_def_gt' (hij : ¬ j <= i) : cycleIcc j i =
 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleIcc_of_gt (h : j < k) : (cycleIcc i j) k = k := by
  by_cases hij : i ≤ j
  · have kin : k ∈ Set.range (natAdd_castLEEmb (Nat.sub_le n i)) := by
      simp [range_natAdd_castLEEmb]; lia
    have : (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)
      = subNat i.1 (k.cast (by lia)) (by simp; lia) := by
      simpa [symm_apply_eq] using eq_of_val_eq (by simp; lia)
    simp only [cycleIcc_to_cycleRange hij kin, natAdd_castLEEmb, this,
      Function.Embedding.trans_apply, addNatEmb_apply, coe_toEmbedding, finCongr_apply]
    rw [cycleRange_of_gt]
    · exact eq_of_val_eq (by simp; lia)
    · exact lt_def.mpr (by simp [sub_val_of_le hij]; lia)
  · simp [hij]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.cycleIcc_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_of_le_of_le (hik : i <= k) (hkj : k <= j) [NeZero n] : (cycleIcc 
i j) k = if k = j then i else k + 1
参数：hik : i <= k；hkj : k <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Fin.range_natAdd_castLEEmb`：range_natAdd_castLEEmb {n m : Nat} (hmn : n 
<= m) : Set.range (natAdd_castLEEmb hmn) = {i | m - n <= i.1}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Fin.addNatEmb_apply`：∀ {n : ℕ} (m : ℕ) (x : Fin n), (Fin.addNatEmb m) x 
= x.addNat m
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Fin.eq_of_val_eq`：∀ {n : ℕ} {i j : Fin n}, ↑i = ↑j → i = j
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val
· 使用引理 `Fin.cycleIcc_to_cycleRange`：cycleIcc_to_cycleRange (hij : i <= j) (kin :
 k in Set.range (natAdd_castLEEmb (Nat.sub_le n i))) : (cycleIcc i j) k = (natAd
d_castLEEmb (Nat…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Fin.sub_val_of_le`：∀ {n : ℕ} {a b : Fin n}, b ≤ a → ↑(a - b) = ↑a - ↑b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.instNeZeroNatHSubVal_mathlib`：∀ {n : ℕ} {i : Fin n}, NeZero (n - ↑i)
· 使用定理 `Fin.cast.congr_simp`：∀ {n m : ℕ} (eq : n = m) (i i_1 : Fin n), i = i_1 →
 Fin.cast eq i = Fin.cast eq i_1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.subNat.congr_simp`：∀ {n : ℕ} (m : ℕ) (i i_1 : Fin (n + m)) (e_i : i 
= i_1) (h : m ≤ ↑i), Fin.subNat m i h = Fin.subNat m i_1 ⋯
· 使用定理 `Fin.cycleRange_of_eq`：cycleRange_of_eq [NeZero n] (h : i = j) : cycleRan
ge j i = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Fin.cycleRange_of_lt`：cycleRange_of_lt [NeZero n] (h : i < j) : cycleRan
ge j i = i + 1
（共 38 条，此处仅展示前 30 条）
-/
theorem cycleIcc_of_le_of_le (hik : i ≤ k) (hkj : k ≤ j) [NeZero n] :
    (cycleIcc i j) k = if k = j then i else k + 1 := by
  have hij : i ≤ j := le_trans hik hkj
  have kin : k ∈ Set.range (natAdd_castLEEmb (Nat.sub_le n i)) := by
    simp [range_natAdd_castLEEmb]; lia
  have : (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)
      = subNat i.1 (k.cast (by lia)) (by simp; lia) := by
    simpa [symm_apply_eq] using eq_of_val_eq (by simp; lia)
  simp only [cycleIcc_to_cycleRange hij kin, natAdd_castLEEmb, this, Function.Embedding.trans_apply,
    addNatEmb_apply, coe_toEmbedding, finCongr_apply]
  refine eq_of_val_eq ?_
  split_ifs with ch
  · have : subNat i.1 (j.cast (by lia)) (by simp [hij]) = (j - i).castLT (sub_val_lt_sub hij) :=
      eq_of_val_eq (by simp [sub_val_of_le hij])
    simp [ch, cycleRange_of_eq this]; lia
  · have : subNat i.1 (k.cast (by lia)) (by simp [hik]) < (j - i).castLT (sub_val_lt_sub hij) := by
      simp [lt_def, sub_val_of_le hij]; lia
    rw [cycleRange_of_lt this, subNat]
    simp only [val_cast, add_def, val_one', Nat.add_mod_mod, addNat_mk, cast_mk]
    rw [Nat.mod_eq_of_lt (by lia), Nat.mod_eq_of_lt (by lia)]
    lia
/-
**Fin.cycleIcc_of_ge_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_of_ge_of_lt (hik : i <= k) (hkj : k < j) [NeZero n] : (cycleIcc i
 j) k = k + 1
参数：hik : i <= k；hkj : k < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleIcc_of_le_of_le`：cycleIcc_of_le_of_le (hik : i <= k) (hkj : k <
= j) [NeZero n] : (cycleIcc i j) k = if k = j then i else k + 1
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleIcc_of_ge_of_lt (hik : i ≤ k) (hkj : k < j) [NeZero n] : (cycleIcc i j) k = k + 1 := by
  simp [cycleIcc_of_le_of_le hik (le_of_lt hkj), Fin.ne_of_lt hkj]
/-
**Fin.cycleIcc_of_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_of_last (hij : i <= j) [NeZero n] : (cycleIcc i j) j = i
参数：hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleIcc_of_le_of_le`：cycleIcc_of_le_of_le (hik : i <= k) (hkj : k <
= j) [NeZero n] : (cycleIcc i j) k = if k = j then i else k + 1
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleIcc_of_last (hij : i ≤ j) [NeZero n] : (cycleIcc i j) j = i := by
  simp [cycleIcc_of_le_of_le hij (ge_of_eq rfl)]
/-
**Fin.cycleIcc_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_eq [NeZero n] : cycleIcc i i = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleIcc_of_lt`：cycleIcc_of_lt (h : k < i) : (cycleIcc i j) k = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.cycleIcc_of_le_of_le`：cycleIcc_of_le_of_le (hik : i <= k) (hkj : k <
= j) [NeZero n] : (cycleIcc i j) k = if k = j then i else k + 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Fin.cycleIcc_of_gt`：cycleIcc_of_gt (h : j < k) : (cycleIcc i j) k = k
-/
theorem cycleIcc_eq [NeZero n] : cycleIcc i i = 1 := by
  ext k
  simp only [Perm.coe_one, id_eq]
  rcases lt_trichotomy k i with ch | ch | ch
  · simp [-cycleIcc_def_le, cycleIcc_of_lt, ch]
  · simp [-cycleIcc_def_le, ch]
  · simp [-cycleIcc_def_le, cycleIcc_of_gt, ch]

@[simp]
/-
**Fin.cycleIcc_ge** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_ge (hij : i <= j) [NeZero n] : cycleIcc j i = 1
参数：hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_or_eq_of_le`：∀ {n : ℕ} {a b : Fin n}, a ≤ b → a < b ∨ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleIcc_def_gt`：cycleIcc_def_gt (hij : i < j) : cycleIcc j i = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cycleIcc_eq`：cycleIcc_eq [NeZero n] : cycleIcc i i = 1
-/
theorem cycleIcc_ge (hij : i ≤ j) [NeZero n] : cycleIcc j i = 1 := by
  rcases Fin.lt_or_eq_of_le hij with hij | hij
  · simp [hij]
  · rw [hij, ← cycleIcc_eq]
/-
**Fin.sign_cycleIcc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：sign_cycleIcc_of_le (hij : i <= j) : Perm.sign (cycleIcc i j) = (-1) ^ (j 
- i : Nat)
参数：hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用引理 `Fin.cycleIcc_def_le`：cycleIcc_def_le {i j : Fin n} (hij : i <= j) : cycl
eIcc i j = (cycleRange ((j - i).castLT (sub_val_lt_sub hij))).extendDomain (natA
dd_castLE…
· 使用定理 `Equiv.Perm.sign_extendDomain`：sign_extendDomain (e : Perm α) {p : β -> P
rop} [DecidablePred p] (f : α ≃ Subtype p) : Equiv.Perm.sign (e.extendDomain f) 
= Equiv.Perm.sign …
· 使用定理 `Fin.sign_cycleRange`：sign_cycleRange (i : Fin n) : Perm.sign (cycleRange
 i) = (-1) ^ (i : Nat)
· 使用定理 `Fin.sub_val_of_le`：∀ {n : ℕ} {a b : Fin n}, b ≤ a → ↑(a - b) = ↑a - ↑b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sign_cycleIcc_of_le (hij : i ≤ j) : Perm.sign (cycleIcc i j) = (-1) ^ (j - i : ℕ) := by
  simp [hij, sub_val_of_le hij]
/-
**Fin.sign_cycleIcc_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：sign_cycleIcc_of_eq : Perm.sign (cycleIcc i i) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.sign_cycleIcc_of_le`：sign_cycleIcc_of_le (hij : i <= j) : Perm.sign 
(cycleIcc i j) = (-1) ^ (j - i : Nat)
· 使用定理 `Fin.ge_of_eq`：∀ {n : ℕ} {a b : Fin n}, a = b → b ≤ a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem sign_cycleIcc_of_eq : Perm.sign (cycleIcc i i) = 1 := by
  rw [sign_cycleIcc_of_le (Fin.ge_of_eq rfl), tsub_self, pow_zero]
/-
**Fin.sign_cycleIcc_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：sign_cycleIcc_of_ge (hij : i <= j) : Perm.sign (cycleIcc j i) = 1
参数：hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.lt_or_eq_of_le`：∀ {n : ℕ} {a b : Fin n}, a ≤ b → a < b ∨ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleIcc_def_gt'`：cycleIcc_def_gt' (hij : ¬ j <= i) : cycleIcc j i =
 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.not_le`：∀ {n : ℕ} {a b : Fin n}, ¬a ≤ b ↔ b < a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.sign_cycleIcc_of_eq`：sign_cycleIcc_of_eq : Perm.sign (cycleIcc i i) 
= 1
-/
theorem sign_cycleIcc_of_ge (hij : i ≤ j) : Perm.sign (cycleIcc j i) = 1 := by
  rcases Fin.lt_or_eq_of_le hij with hij | hij
  · simp [Fin.not_le.mpr hij]
  · rw [hij, sign_cycleIcc_of_eq]
/-
**Fin.isCycle_cycleIcc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：isCycle_cycleIcc (hij : i < j) : (cycleIcc i j).IsCycle
参数：hij : i < j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.cycleIcc_def_le`：cycleIcc_def_le {i j : Fin n} (hij : i <= j) : cycl
eIcc i j = (cycleRange ((j - i).castLT (sub_val_lt_sub hij))).extendDomain (natA
dd_castLE…
· 使用定理 `Equiv.Perm.IsCycle.extendDomain`：∀ {α : Type u_2} {β : Type u_3} {g : Eq
uiv.Perm α} {p : β → Prop} [inst : DecidablePred p] (f : α ≃ Subtype p),   g.IsC
ycle → (g.extendDomai…
· 使用定理 `Fin.le_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≤ b
· 使用定理 `Fin.isCycle_cycleRange`：isCycle_cycleRange [NeZero n] (h0 : i != 0) : Is
Cycle (cycleRange i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neZero_iff`：∀ {R : Type u_1} [inst : Zero R] {n : R}, NeZero n ↔ n ≠ 0
· 使用引理 `Fin.castLT_sub_nezero`：castLT_sub_nezero {n : Nat} {i j : Fin n} (hij : 
i < j) : haveI : NeZero (n - i.1)
-/
theorem isCycle_cycleIcc (hij : i < j) : (cycleIcc i j).IsCycle := by
  simpa [le_of_lt hij] using Equiv.Perm.IsCycle.extendDomain
    (natAdd_castLEEmb _).toEquivRange (isCycle_cycleRange (castLT_sub_nezero hij))
/-
**Fin.cycleType_cycleIcc_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleType_cycleIcc_of_lt (hij : i < j) : Perm.cycleType (cycleIcc i j) = {
(j - i + 1: Nat)}
参数：hij : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.sub_val_lt_sub`：sub_val_lt_sub {n : Nat} {i j : Fin n} (hij : i <= j
) : (j - i).val < n - i.val
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fin.le_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≤ b
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `Equiv.Perm.cycleType.congr_simp`：∀ {α : Type u_1} [inst : Fintype α] {in
st_1 : DecidableEq α} [inst_2 : DecidableEq α] (σ σ_1 : Equiv.Perm α),   σ = σ_1
 → σ.cycleType = σ_1.…
· 使用引理 `Fin.cycleIcc_def_le`：cycleIcc_def_le {i j : Fin n} (hij : i <= j) : cycl
eIcc i j = (cycleRange ((j - i).castLT (sub_val_lt_sub hij))).extendDomain (natA
dd_castLE…
· 使用定理 `Equiv.Perm.cycleType_extendDomain`：cycleType_extendDomain {β : Type*} [F
intype β] [DecidableEq β] {p : β -> Prop} [DecidablePred p] (f : α ≃ Subtype p) 
{g : Perm α} : cycleTyp…
· 使用定理 `Fin.cycleType_cycleRange`：cycleType_cycleRange [NeZero n] (h0 : i != 0) 
: cycleType (cycleRange i) = {(i + 1 : Nat)}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neZero_iff`：∀ {R : Type u_1} [inst : Zero R] {n : R}, NeZero n ↔ n ≠ 0
· 使用引理 `Fin.castLT_sub_nezero`：castLT_sub_nezero {n : Nat} {i j : Fin n} (hij : 
i < j) : haveI : NeZero (n - i.1)
· 使用定理 `Fin.sub_val_of_le`：∀ {n : ℕ} {a b : Fin n}, b ≤ a → ↑(a - b) = ↑a - ↑b
-/
theorem cycleType_cycleIcc_of_lt (hij : i < j) :
    Perm.cycleType (cycleIcc i j) = {(j - i + 1: ℕ)} := by
  simpa [le_of_lt hij, cycleType_cycleRange (castLT_sub_nezero hij)] using sub_val_of_le
    (le_of_lt hij)
/-
**Fin.cycleType_cycleIcc_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleType_cycleIcc_of_ge (hij : i <= j) [NeZero n] : Perm.cycleType (cycle
Icc j i) = ∅
参数：hij : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.cycleIcc_ge`：cycleIcc_ge (hij : i <= j) [NeZero n] : cycleIcc j i = 
1
-/
theorem cycleType_cycleIcc_of_ge (hij : i ≤ j) [NeZero n] : Perm.cycleType (cycleIcc j i) = ∅ := by
  simpa using cycleIcc_ge hij
/-
**Fin.cycleIcc_zero_eq_cycleRange** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_zero_eq_cycleRange (i : Fin n) [NeZero n] : cycleIcc 0 i = cycleR
ange i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleIcc_of_ge_of_lt`：cycleIcc_of_ge_of_lt (hik : i <= k) (hkj : k <
 j) [NeZero n] : (cycleIcc i j) k = k + 1
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用定理 `Fin.cycleRange_of_lt`：cycleRange_of_lt [NeZero n] (h : i < j) : cycleRan
ge j i = i + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.cycleIcc_of_le_of_le`：cycleIcc_of_le_of_le (hik : i <= k) (hkj : k <
= j) [NeZero n] : (cycleIcc i j) k = if k = j then i else k + 1
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Fin.cycleRange_self`：cycleRange_self [NeZero n] (i : Fin n) : cycleRange
 i i = 0
· 使用定理 `Fin.cycleIcc_of_gt`：cycleIcc_of_gt (h : j < k) : (cycleIcc i j) k = k
· 使用定理 `Fin.cycleRange_of_gt`：cycleRange_of_gt (h : i < j) : cycleRange i j = j
-/
theorem cycleIcc_zero_eq_cycleRange (i : Fin n) [NeZero n] : cycleIcc 0 i = cycleRange i := by
  ext x
  rcases lt_trichotomy x i with ch | ch | ch
  · simp [-cycleIcc_def_le, cycleIcc_of_ge_of_lt (zero_le x) ch, cycleRange_of_lt ch]
  · simp [-cycleIcc_def_le, ch]
  · simp [-cycleIcc_def_le, cycleIcc_of_gt ch, cycleRange_of_gt ch]
/-
**Fin.cycleIcc_comp_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cycleIcc_comp_succAbove {n : Nat} (i j : Fin (n + 1)) (hij : i <= j) : (cy
cleIcc i j) ∘ j.succAbove = i.succAbove
参数：i j : Fin (n + 1)；hij : i <= j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cycleIcc_comp_succAbove {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    (cycleIcc i j) ∘ j.succAbove = i.succAbove := by
  grind [cycleIcc_of_lt, succAbove_of_castSucc_lt, cycleIcc_of_ge_of_lt,
    succAbove_of_le_castSucc, coeSucc_eq_succ, cycleIcc_of_gt]
/-
**Fin.cycleIcc.trans** 是 Mathlib 中的一个定理，位于命名空间 `Fin.cycleIcc`。
形式化陈述：∀ {n : ℕ} {i j k : Fin n} [NeZero n], i ≤ j → j ≤ k → ⇑(i.cycleIcc j) ∘ ⇑(
j.cycleIcc k) = ⇑(i.cycleIcc k)
参数：i.cycleIcc j；j.cycleIcc k；i.cycleIcc k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleIcc_of_lt`：cycleIcc_of_lt (h : k < i) : (cycleIcc i j) k = k
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.cycleIcc_of_gt`：cycleIcc_of_gt (h : j < k) : (cycleIcc i j) k = k
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Fin.cycleIcc_of_le_of_le`：cycleIcc_of_le_of_le (hik : i <= k) (hkj : k <
= j) [NeZero n] : (cycleIcc i j) k = if k = j then i else k + 1
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Fin.val_eq_of_eq`：∀ {n : ℕ} {i j : Fin n}, i = j → ↑i = ↑j
· 使用定理 `Fin.cycleIcc_of_last`：cycleIcc_of_last (hij : i <= j) [NeZero n] : (cycl
eIcc i j) j = i
· 使用引理 `Fin.lt_add_one_of_succ_lt`：lt_add_one_of_succ_lt {n : Nat} [NeZero n] {a
 : Fin n} (ha : a + 1 < n) : a < a + 1
-/
theorem cycleIcc.trans [NeZero n] (hij : i ≤ j) (hjk : j ≤ k) :
    (cycleIcc i j) ∘ (cycleIcc j k) = (cycleIcc i k) := by
  ext x
  rcases lt_or_ge x i with ch | ch
  · simp [cycleIcc_of_lt (lt_of_lt_of_le ch hij), cycleIcc_of_lt ch]
  rcases lt_or_ge k x with ch | ch1
  · simp [cycleIcc_of_gt (lt_of_le_of_lt hjk ch), cycleIcc_of_gt ch]
  rcases lt_or_ge x j with ch2 | ch2
  · simp [cycleIcc_of_lt ch2, cycleIcc_of_le_of_le ch ch1, cycleIcc_of_le_of_le ch (le_of_lt ch2)]
    split_ifs
    repeat lia
  · simp only [Function.comp_apply, cycleIcc_of_le_of_le ch2 ch1, cycleIcc_of_le_of_le ch ch1]
    split_ifs with h
    · exact val_eq_of_eq (cycleIcc_of_last hij)
    · simp [cycleIcc_of_gt (lt_of_le_of_lt ch2 (lt_add_one_of_succ_lt (by lia)))]
/-
**Fin.cycleIcc.trans_left_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin.cycleIcc`。
形式化陈述：∀ {n : ℕ} {i j k : Fin n} [NeZero n], i ≤ j → ⇑(j.cycleIcc i) ∘ ⇑(i.cycleI
cc k) = ⇑(i.cycleIcc k)
参数：j.cycleIcc i；i.cycleIcc k；i.cycleIcc k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleIcc_ge`：cycleIcc_ge (hij : i <= j) [NeZero n] : cycleIcc j i = 
1
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleIcc.trans_left_one [NeZero n] (hij : i ≤ j) :
    (cycleIcc j i) ∘ (cycleIcc i k) = cycleIcc i k := by
  simp [hij]
/-
**Fin.cycleIcc.trans_right_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin.cycleIcc`。
形式化陈述：∀ {n : ℕ} {i j k : Fin n} [NeZero n], j ≤ k → ⇑(i.cycleIcc k) ∘ ⇑(k.cycleI
cc j) = ⇑(i.cycleIcc k)
参数：i.cycleIcc k；k.cycleIcc j；i.cycleIcc k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cycleIcc_ge`：cycleIcc_ge (hij : i <= j) [NeZero n] : cycleIcc j i = 
1
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleIcc.trans_right_one [NeZero n] (hjk : j ≤ k) :
    (cycleIcc i k) ∘ (cycleIcc k j) = cycleIcc i k := by
  simp [hjk]

end Fin

end cycleIcc

section Sign

variable {n : ℕ}

/-
**Equiv.Perm.sign_eq_prod_prod_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.sign_eq_prod_prod_Iio (σ : Equiv.Perm (Fin n)) : σ.sign = ∏ j, 
∏ i in Finset.Iio j, (if σ i < σ j then 1 else -1)
参数：σ : Equiv.Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.swap_induction_on`：swap_induction_on [Finite α] {motive : Per
m α -> Prop} (f : Perm α) (one : motive 1) (swap_mul : forall f x y, x != y -> m
otive f -> motive …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用定理 `Equiv.Perm.signAux_one`：signAux_one (n : Nat) : signAux (1 : Perm (Fin n
)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.signAux_mul`：signAux_mul {n : Nat} (f g : Perm (Fin n)) : sig
nAux (f * g) = signAux f * signAux g
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `Equiv.Perm.sign_swap`：sign_swap {x y : α} (h : x != y) : sign (swap x y)
 = -1
· 使用定理 `Equiv.Perm.signAux_swap`：signAux_swap : forall {n : Nat} {x y : Fin n} (
_hxy : x != y), signAux (swap x y) = -1 | 0, x, y => by intro; exact Fin.elim0 x
 | 1, x, y =>…
· 使用定理 `Finset.prod_sigma'`：prod_sigma' {σ : α -> Type*} (s : Finset α) (t : for
all a, Finset (σ a)) (f : forall a, σ a -> β) : (∏ a in s, ∏ s in t a, f a s) = 
∏ x in s…
· 使用定理 `Equiv.Perm.signAux.eq_1`：∀ {n : ℕ} (a : Equiv.Perm (Fin n)), a.signAux =
 ∏ x ∈ Equiv.Perm.finPairsLT n, if a x.fst ≤ a x.snd then -1 else 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
theorem Equiv.Perm.sign_eq_prod_prod_Iio (σ : Equiv.Perm (Fin n)) :
    σ.sign = ∏ j, ∏ i ∈ Finset.Iio j, (if σ i < σ j then 1 else -1) := by
  suffices h : σ.sign = σ.signAux by
    rw [h, Finset.prod_sigma', Equiv.Perm.signAux]
    convert! rfl using 2 with x hx
    · simp [Finset.ext_iff, Equiv.Perm.mem_finPairsLT]
    simp [← ite_not (p := _ ≤ _)]
  refine σ.swap_induction_on (by simp) fun π i j hne h_eq ↦ ?_
  rw [Equiv.Perm.signAux_mul, Equiv.Perm.sign_mul, h_eq, Equiv.Perm.sign_swap hne,
    Equiv.Perm.signAux_swap hne]
/-
**Equiv.Perm.sign_eq_prod_prod_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.sign_eq_prod_prod_Ioi (σ : Equiv.Perm (Fin n)) : σ.sign = ∏ i, 
∏ j in Finset.Ioi i, (if σ i < σ j then 1 else -1)
参数：σ : Equiv.Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_eq_prod_prod_Iio`：Equiv.Perm.sign_eq_prod_prod_Iio (σ : 
Equiv.Perm (Fin n)) : σ.sign = ∏ j, ∏ i in Finset.Iio j, (if σ i < σ j then 1 el
se -1)
· 使用定理 `Finset.prod_comm'`：prod_comm' {s : Finset γ} {t : γ -> Finset α} {t' : F
inset α} {s' : α -> Finset γ} (h : forall x y, x in s ∧ y in t x ↔ x in s' y ∧ y
 in t')…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Equiv.Perm.sign_eq_prod_prod_Ioi (σ : Equiv.Perm (Fin n)) :
    σ.sign = ∏ i, ∏ j ∈ Finset.Ioi i, (if σ i < σ j then 1 else -1) := by
  rw [σ.sign_eq_prod_prod_Iio]
  apply Finset.prod_comm' (by simp)
/-
**Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod {R : Type*} [CommRing R] (σ : Eq
uiv.Perm (Fin n)) {f : Fin n -> Fin n -> R} (hf : forall i j, f i j = -f j i) : 
∏ j, ∏ i in Finset.Iio j, f (σ i) (σ j) = σ.sign * ∏ j, ∏ i in Finset.Iio j, f i
 j
参数：σ : Equiv.Perm (Fin n)；hf : forall i j, f i j = -f j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sign_inv`：sign_inv (f : Perm α) : sign f⁻¹ = sign f
· 使用定理 `Equiv.Perm.sign_eq_prod_prod_Iio`：Equiv.Perm.sign_eq_prod_prod_Iio (σ : 
Equiv.Perm (Fin n)) : σ.sign = ∏ j, ∏ i in Finset.Iio j, (if σ i < σ j then 1 el
se -1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_sigma'`：prod_sigma' {σ : α -> Type*} (s : Finset α) (t : for
all a, Finset (σ a)) (f : forall a, σ a -> β) : (∏ a in s, ∏ s in t a, f a s) = 
∏ x in s…
· 使用定理 `Units.coe_prod`：Units.coe_prod [CommMonoid M] (f : α -> Mˣ) (s : Finset 
α) : (↑(∏ i in s, f i) : M) = ∏ i in s, (f i : M)
· 使用引理 `Int.cast_prod`：cast_prod {R : Type*} [CommRing R] (f : ι -> Int) (s : Fi
nset ι) : (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `inf_le_sup`：inf_le_sup : a ⊓ b <= a ⊔ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 50 条，此处仅展示前 30 条）
-/
theorem Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod {R : Type*} [CommRing R]
    (σ : Equiv.Perm (Fin n)) {f : Fin n → Fin n → R} (hf : ∀ i j, f i j = -f j i) :
    ∏ j, ∏ i ∈ Finset.Iio j, f (σ i) (σ j) = σ.sign * ∏ j, ∏ i ∈ Finset.Iio j, f i j := by
  simp_rw [← σ.sign_inv, σ⁻¹.sign_eq_prod_prod_Iio, Finset.prod_sigma', Units.coe_prod,
    Int.cast_prod, ← Finset.prod_mul_distrib]
  set D := (Finset.univ : Finset (Fin n)).sigma Finset.Iio with hD
  have hφD : D.image (fun x ↦ ⟨σ x.1 ⊔ σ x.2, σ x.1 ⊓ σ x.2⟩) = D := by
    ext ⟨x1, x2⟩
    suffices (∃ a, ∃ b < a, σ a ⊔ σ b = x1 ∧ σ a ⊓ σ b = x2) ↔ x2 < x1 by simpa [hD]
    refine ⟨?_, fun hlt ↦ ?_⟩
    · rintro ⟨i, j, hij, rfl, rfl⟩
      exact inf_le_sup.lt_of_ne <| by simp [hij.ne.symm]
    obtain hlt' | hle := lt_or_ge (σ.symm x1) (σ.symm x2)
    · exact ⟨_, _, hlt', by simp [hlt.le]⟩
    exact ⟨_, _, hle.lt_of_ne (by simp [hlt.ne]), by simp [hlt.le]⟩
  nth_rw 2 [← hφD]
  rw [Finset.prod_image fun x hx y hy ↦ Finset.injOn_of_card_image_eq (by rw [hφD]) hx hy]
  refine Finset.prod_congr rfl fun ⟨x₁, x₂⟩ hx ↦ ?_
  replace hx : x₂ < x₁ := by simpa [hD] using hx
  obtain hlt | hle := lt_or_ge (σ x₁) (σ x₂)
  · simp [inf_eq_left.2 hlt.le, sup_eq_right.2 hlt.le, hx.not_gt, ← hf]
  simp [inf_eq_right.2 hle, sup_eq_left.2 hle, hx]
/-
**Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod {R : Type*} [CommRing R] (σ : Eq
uiv.Perm (Fin n)) {f : Fin n -> Fin n -> R} (hf : forall i j, f i j = -f j i) : 
∏ i, ∏ j in Finset.Ioi i, f (σ i) (σ j) = σ.sign * ∏ i, ∏ j in Finset.Ioi i, f i
 j
参数：σ : Equiv.Perm (Fin n)；hf : forall i j, f i j = -f j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_comm'`：prod_comm' {s : Finset γ} {t : γ -> Finset α} {t' : F
inset α} {s' : α -> Finset γ} (h : forall x y, x in s ∧ y in t x ↔ x in s' y ∧ y
 in t')…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod`：Equiv.Perm.prod_Iio_comp_eq_s
ign_mul_prod {R : Type*} [CommRing R] (σ : Equiv.Perm (Fin n)) {f : Fin n -> Fin
 n -> R} (hf : forall i j, f i …
-/
theorem Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod {R : Type*} [CommRing R]
    (σ : Equiv.Perm (Fin n)) {f : Fin n → Fin n → R} (hf : ∀ i j, f i j = -f j i) :
    ∏ i, ∏ j ∈ Finset.Ioi i, f (σ i) (σ j) = σ.sign * ∏ i, ∏ j ∈ Finset.Ioi i, f i j := by
  convert! σ.prod_Iio_comp_eq_sign_mul_prod hf using 1
  · apply Finset.prod_comm' (by simp)
  convert! rfl using 2
  apply Finset.prod_comm' (by simp)

end Sign

