/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Translations

/-!
# Stabilisation of gcf Computations Under Termination

## Summary

We show that the continuants and convergents of a gcf stabilise once the gcf terminates.
-/

public section


namespace GenContFract

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

/-- If a gcf terminated at position `n`, it also terminated at `m ≥ n`. -/
/-
**GenContFract.terminated_stable** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：terminated_stable (n_le_m : n <= m) (terminatedAt_n : g.TerminatedAt n) : 
g.TerminatedAt m
参数：n_le_m : n <= m；terminatedAt_n : g.TerminatedAt n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.terminated_stable`：terminated_stable : forall (s : Seq α) {m
 n : Nat}, m <= n -> s.TerminatedAt m -> s.TerminatedAt n

--- 原说明 ---
If a gcf terminated at position `n`, it also terminated at `m ≥ n`.
-/
theorem terminated_stable (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.TerminatedAt m :=
  g.s.terminated_stable n_le_m terminatedAt_n

variable [DivisionRing K]
/-
**GenContFract.contsAux_stable_step_of_terminated** 是 Mathlib 中的一个定理，位于命名空间 `Gen
ContFract`。
形式化陈述：contsAux_stable_step_of_terminated (terminatedAt_n : g.TerminatedAt n) : g
.contsAux (n + 2) = g.contsAux (n + 1)
参数：terminatedAt_n : g.TerminatedAt n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.terminatedAt_iff_s_none`：terminatedAt_iff_s_none : g.Termin
atedAt n ↔ g.s.get? n = none
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem contsAux_stable_step_of_terminated (terminatedAt_n : g.TerminatedAt n) :
    g.contsAux (n + 2) = g.contsAux (n + 1) := by
  rw [terminatedAt_iff_s_none] at terminatedAt_n
  simp only [contsAux, terminatedAt_n]
/-
**GenContFract.contsAux_stable_of_terminated** 是 Mathlib 中的一个定理，位于命名空间 `GenContF
ract`。
形式化陈述：contsAux_stable_of_terminated (n_lt_m : n < m) (terminatedAt_n : g.Termina
tedAt n) : g.contsAux m = g.contsAux (n + 1)
参数：n_lt_m : n < m；terminatedAt_n : g.TerminatedAt n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `Nat.exists_eq_add_of_lt`：∀ {m n : ℕ}, m < n → ∃ k, n = m + k + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GenContFract.contsAux_stable_step_of_terminated`：contsAux_stable_step_of
_terminated (terminatedAt_n : g.TerminatedAt n) : g.contsAux (n + 2) = g.contsAu
x (n + 1)
· 使用定理 `GenContFract.terminated_stable`：terminated_stable (n_le_m : n <= m) (ter
minatedAt_n : g.TerminatedAt n) : g.TerminatedAt m
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem contsAux_stable_of_terminated (n_lt_m : n < m) (terminatedAt_n : g.TerminatedAt n) :
    g.contsAux m = g.contsAux (n + 1) := by
  refine Nat.le_induction rfl (fun k hnk hk => ?_) _ n_lt_m
  rcases Nat.exists_eq_add_of_lt hnk with ⟨k, rfl⟩
  refine (contsAux_stable_step_of_terminated ?_).trans hk
  exact terminated_stable (Nat.le_add_right _ _) terminatedAt_n
/-
**GenContFract.convs'Aux_stable_step_of_terminated** 是 Mathlib 中的一个定理，位于命名空间 `Ge
nContFract`。
形式化陈述：∀ {K : Type u_1} {n : ℕ} [inst : DivisionRing K] {s : Stream'.Seq (GenCont
Fract.Pair K)},   s.TerminatedAt n → GenContFract.convs'Aux s (n + 1) = GenContF
ract.convs'Aux s n
参数：GenContFract.Pair K；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GenContFract.convs'Aux.eq_2`：∀ {K : Type u_2} [inst : DivisionRing K] (x
 : Stream'.Seq (GenContFract.Pair K)) (n : ℕ),   GenContFract.convs'Aux x n.succ
 =     match x.he…
-/
theorem convs'Aux_stable_step_of_terminated {s : Stream'.Seq <| Pair K}
    (terminatedAt_n : s.TerminatedAt n) : convs'Aux s (n + 1) = convs'Aux s n := by
  change s.get? n = none at terminatedAt_n
  induction n generalizing s with
  | zero => simp only [convs'Aux, terminatedAt_n, Stream'.Seq.head]
  | succ n IH =>
    cases s_head_eq : s.head with
    | none => simp only [convs'Aux, s_head_eq]
    | some gp_head =>
      have : s.tail.TerminatedAt n := by
        simp only [Stream'.Seq.TerminatedAt, s.get?_tail, terminatedAt_n]
      have := IH this
      rw [convs'Aux] at this
      simp [this, convs'Aux, s_head_eq]
/-
**GenContFract.convs'Aux_stable_of_terminated** 是 Mathlib 中的一个定理，位于命名空间 `GenCont
Fract`。
形式化陈述：∀ {K : Type u_1} {n m : ℕ} [inst : DivisionRing K] {s : Stream'.Seq (GenCo
ntFract.Pair K)},   n ≤ m → s.TerminatedAt n → GenContFract.convs'Aux s m = GenC
ontFract.convs'Aux s n
参数：GenContFract.Pair K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GenContFract.convs'Aux_stable_step_of_terminated`：∀ {K : Type u_1} {n : 
ℕ} [inst : DivisionRing K] {s : Stream'.Seq (GenContFract.Pair K)},   s.Terminat
edAt n → GenContFract.convs'Aux s (n +…
· 使用定理 `Stream'.Seq.terminated_stable`：terminated_stable : forall (s : Seq α) {m
 n : Nat}, m <= n -> s.TerminatedAt m -> s.TerminatedAt n
-/
theorem convs'Aux_stable_of_terminated {s : Stream'.Seq <| Pair K} (n_le_m : n ≤ m)
    (terminatedAt_n : s.TerminatedAt n) : convs'Aux s m = convs'Aux s n := by
  induction n_le_m with
  | refl => rfl
  | step n_le_m IH =>
    refine (convs'Aux_stable_step_of_terminated (?_)).trans IH
    exact s.terminated_stable n_le_m terminatedAt_n
/-
**GenContFract.conts_stable_of_terminated** 是 Mathlib 中的一个定理，位于命名空间 `GenContFrac
t`。
形式化陈述：conts_stable_of_terminated (n_le_m : n <= m) (terminatedAt_n : g.Terminate
dAt n) : g.conts m = g.conts n
参数：n_le_m : n <= m；terminatedAt_n : g.TerminatedAt n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.contsAux_stable_of_terminated`：contsAux_stable_of_terminate
d (n_lt_m : n < m) (terminatedAt_n : g.TerminatedAt n) : g.contsAux m = g.contsA
ux (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pred_le_iff`：∀ {n : ℕ} {m : ℕ}, n.pred ≤ m ↔ n ≤ m.succ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conts_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.conts m = g.conts n := by
  simp only [nth_cont_eq_succ_nth_contAux,
    contsAux_stable_of_terminated (Nat.pred_le_iff.mp n_le_m) terminatedAt_n]
/-
**GenContFract.nums_stable_of_terminated** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract
`。
形式化陈述：nums_stable_of_terminated (n_le_m : n <= m) (terminatedAt_n : g.Terminated
At n) : g.nums m = g.nums n
参数：n_le_m : n <= m；terminatedAt_n : g.TerminatedAt n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.conts_stable_of_terminated`：conts_stable_of_terminated (n_l
e_m : n <= m) (terminatedAt_n : g.TerminatedAt n) : g.conts m = g.conts n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nums_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.nums m = g.nums n := by
  simp only [num_eq_conts_a, conts_stable_of_terminated n_le_m terminatedAt_n]
/-
**GenContFract.dens_stable_of_terminated** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract
`。
形式化陈述：dens_stable_of_terminated (n_le_m : n <= m) (terminatedAt_n : g.Terminated
At n) : g.dens m = g.dens n
参数：n_le_m : n <= m；terminatedAt_n : g.TerminatedAt n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.conts_stable_of_terminated`：conts_stable_of_terminated (n_l
e_m : n <= m) (terminatedAt_n : g.TerminatedAt n) : g.conts m = g.conts n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dens_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.dens m = g.dens n := by
  simp only [den_eq_conts_b, conts_stable_of_terminated n_le_m terminatedAt_n]
/-
**GenContFract.convs_stable_of_terminated** 是 Mathlib 中的一个定理，位于命名空间 `GenContFrac
t`。
形式化陈述：convs_stable_of_terminated (n_le_m : n <= m) (terminatedAt_n : g.Terminate
dAt n) : g.convs m = g.convs n
参数：n_le_m : n <= m；terminatedAt_n : g.TerminatedAt n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `GenContFract.nums_stable_of_terminated`：nums_stable_of_terminated (n_le_
m : n <= m) (terminatedAt_n : g.TerminatedAt n) : g.nums m = g.nums n
· 使用定理 `GenContFract.dens_stable_of_terminated`：dens_stable_of_terminated (n_le_
m : n <= m) (terminatedAt_n : g.TerminatedAt n) : g.dens m = g.dens n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convs_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.convs m = g.convs n := by
  simp only [convs, dens_stable_of_terminated n_le_m terminatedAt_n,
    nums_stable_of_terminated n_le_m terminatedAt_n]
/-
**GenContFract.convs'_stable_of_terminated** 是 Mathlib 中的一个定理，位于命名空间 `GenContFra
ct`。
形式化陈述：∀ {K : Type u_1} {g : GenContFract K} {n m : ℕ} [inst : DivisionRing K],  
 n ≤ m → g.TerminatedAt n → g.convs' m = g.convs' n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.convs'Aux_stable_of_terminated`：∀ {K : Type u_1} {n m : ℕ} 
[inst : DivisionRing K] {s : Stream'.Seq (GenContFract.Pair K)},   n ≤ m → s.Ter
minatedAt n → GenContFract.convs'…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convs'_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.convs' m = g.convs' n := by
  simp only [convs', convs'Aux_stable_of_terminated n_le_m terminatedAt_n]

end GenContFract

