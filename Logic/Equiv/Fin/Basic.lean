/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Embedding.Set
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Data.Int.Init
public import Batteries.Data.Fin.Lemmas

/-!
# Equivalences for `Fin n`
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u

variable {m n : ℕ}

/-!
### Miscellaneous

This is currently not very sorted. PRs welcome!
-/

set_option backward.isDefEq.respectTransparency false in
/-
**Fin.preimage_apply_01_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.preimage_apply_01_prod {α : Fin 2 -> Type u} (s : Set (α 0)) (t : Set 
(α 1)) : (fun f : forall i, α i => (f 0, f 1)) ⁻¹' s ×ˢ t = Set.pi Set.univ (Fin
.cons s <| Fin.cons t finZeroElim)
参数：s : Set (α 0)；t : Set (α 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.cons_one`：cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall 
i : Fin n.succ, α i.succ) : cons x p 1 = p 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Miscellaneous

This is currently not very sorted. PRs welcome!
-/
theorem Fin.preimage_apply_01_prod {α : Fin 2 → Type u} (s : Set (α 0)) (t : Set (α 1)) :
    (fun f : ∀ i, α i => (f 0, f 1)) ⁻¹' s ×ˢ t =
      Set.pi Set.univ (Fin.cons s <| Fin.cons t finZeroElim) := by
  ext f
  simp [Fin.forall_fin_two]
/-
**Fin.preimage_apply_01_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.preimage_apply_01_prod' {α : Type u} (s t : Set α) : (fun f : Fin 2 ->
 α => (f 0, f 1)) ⁻¹' s ×ˢ t = Set.pi Set.univ ![s, t]
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.preimage_apply_01_prod`：Fin.preimage_apply_01_prod {α : Fin 2 -> Typ
e u} (s : Set (α 0)) (t : Set (α 1)) : (fun f : forall i, α i => (f 0, f 1)) ⁻¹'
 s ×ˢ t = Set.pi…
-/
theorem Fin.preimage_apply_01_prod' {α : Type u} (s t : Set α) :
    (fun f : Fin 2 → α => (f 0, f 1)) ⁻¹' s ×ˢ t = Set.pi Set.univ ![s, t] :=
  @Fin.preimage_apply_01_prod (fun _ => α) s t

/-- A product space `α × β` is equivalent to the space `Π i : Fin 2, γ i`, where
`γ = Fin.cons α (Fin.cons β finZeroElim)`. See also `piFinTwoEquiv` and
`finTwoArrowEquiv`. -/
@[simps! -fullyApplied]
/-
**prodEquivPiFinTwo** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：prodEquivPiFinTwo (α β : Type u) : α × β ≃ forall i : Fin 2, ![α, β] i
参数：α β : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A product space `α × β` is equivalent to the space `Π i : Fin 2, γ i`, where
`γ = Fin.cons α (Fin.cons β finZeroElim)`. See also `piFinTwoEquiv` and
`finTwoArrowEquiv`.
-/
def prodEquivPiFinTwo (α β : Type u) : α × β ≃ ∀ i : Fin 2, ![α, β] i :=
  (piFinTwoEquiv (Fin.cons α (Fin.cons β finZeroElim))).symm

/-- The space of functions `Fin 2 → α` is equivalent to `α × α`. See also `piFinTwoEquiv` and
`prodEquivPiFinTwo`. -/
@[simps -fullyApplied]
/-
**finTwoArrowEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finTwoArrowEquiv (α : Type*) : (Fin 2 -> α) ≃ α × α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of functions `Fin 2 → α` is equivalent to `α × α`. See also `piFinTwoE
quiv` and
`prodEquivPiFinTwo`.
-/
def finTwoArrowEquiv (α : Type*) : (Fin 2 → α) ≃ α × α :=
  { piFinTwoEquiv fun _ => α with invFun := fun x => ![x.1, x.2] }

/-- An equivalence that removes `i` and maps it to `none`.
This is a version of `Fin.predAbove` that produces `Option (Fin n)` instead of
mapping both `i.castSucc` and `i.succ` to `i`. -/
/-
**finSuccEquiv'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finSuccEquiv' (i : Fin (n + 1)) : Fin (n + 1) ≃ Option (Fin n) where toFun
参数：i : Fin (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Option.casesOn'`：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f 
= x

--- 原说明 ---
An equivalence that removes `i` and maps it to `none`.
This is a version of `Fin.predAbove` that produces `Option (Fin n)` instead of
mapping both `i.castSucc` and `i.succ` to `i`.
-/
def finSuccEquiv' (i : Fin (n + 1)) : Fin (n + 1) ≃ Option (Fin n) where
  toFun := i.insertNth none some
  invFun x := x.casesOn' i (Fin.succAbove i)
  left_inv x := Fin.succAboveCases i (by simp) (fun j => by simp) x
  right_inv x := by cases x <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**finSuccEquiv'_at** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} (i : Fin (n + 1)), (finSuccEquiv' i) i = none
参数：i : Fin (n + 1)；finSuccEquiv' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSuccEquiv'_at (i : Fin (n + 1)) : (finSuccEquiv' i) i = none := by
  simp [finSuccEquiv']

@[simp]
/-
**finSuccEquiv'_succAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), (finSuccEquiv' i) (i.succAbove j)
 = some j
参数：i : Fin (n + 1)；j : Fin n；finSuccEquiv' i；i.succAbove j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
-/
theorem finSuccEquiv'_succAbove (i : Fin (n + 1)) (j : Fin n) :
    finSuccEquiv' i (i.succAbove j) = some j :=
  @Fin.insertNth_apply_succAbove n (fun _ => Option (Fin n)) i _ _ _
/-
**finSuccEquiv'_below** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, m.castSucc < i → (finSuccEquiv' i
) m.castSucc = some m
参数：n + 1；finSuccEquiv' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `finSuccEquiv'_succAbove`：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), (finSu
ccEquiv' i) (i.succAbove j) = some j
-/
theorem finSuccEquiv'_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i) (Fin.castSucc m) = m := by
  rw [← Fin.succAbove_of_castSucc_lt _ _ h, finSuccEquiv'_succAbove]
/-
**finSuccEquiv'_above** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, i ≤ m.castSucc → (finSuccEquiv' i
) m.succ = some m
参数：n + 1；finSuccEquiv' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `finSuccEquiv'_succAbove`：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), (finSu
ccEquiv' i) (i.succAbove j) = some j
-/
theorem finSuccEquiv'_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i) m.succ = some m := by
  rw [← Fin.succAbove_of_le_castSucc _ _ h, finSuccEquiv'_succAbove]

@[simp]
/-
**finSuccEquiv'_symm_none** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} (i : Fin (n + 1)), (finSuccEquiv' i).symm none = i
参数：i : Fin (n + 1)；finSuccEquiv' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem finSuccEquiv'_symm_none (i : Fin (n + 1)) : (finSuccEquiv' i).symm none = i :=
  rfl

@[simp]
/-
**finSuccEquiv'_symm_some** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), (finSuccEquiv' i).symm (some j) =
 i.succAbove j
参数：i : Fin (n + 1)；j : Fin n；finSuccEquiv' i；some j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem finSuccEquiv'_symm_some (i : Fin (n + 1)) (j : Fin n) :
    (finSuccEquiv' i).symm (some j) = i.succAbove j :=
  rfl

@[simp]
/-
**finSuccEquiv'_eq_some** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} {i j : Fin (n + 1)} {k : Fin n}, (finSuccEquiv' i) j = some k ↔ 
j = i.succAbove k
参数：n + 1；finSuccEquiv' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem finSuccEquiv'_eq_some {i j : Fin (n + 1)} {k : Fin n} :
    finSuccEquiv' i j = k ↔ j = i.succAbove k :=
  (finSuccEquiv' i).eq_symm_apply.symm

@[simp]
/-
**finSuccEquiv'_eq_none** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} {i j : Fin (n + 1)}, (finSuccEquiv' i) j = none ↔ i = j
参数：n + 1；finSuccEquiv' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem finSuccEquiv'_eq_none {i j : Fin (n + 1)} : finSuccEquiv' i j = none ↔ i = j :=
  (finSuccEquiv' i).eq_symm_apply.symm.trans eq_comm
/-
**finSuccEquiv'_symm_some_below** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, m.castSucc < i → (finSuccEquiv' i
).symm (some m) = m.castSucc
参数：n + 1；finSuccEquiv' i；some m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
-/
theorem finSuccEquiv'_symm_some_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i).symm (some m) = Fin.castSucc m :=
  Fin.succAbove_of_castSucc_lt i m h
/-
**finSuccEquiv'_symm_some_above** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, i ≤ m.castSucc → (finSuccEquiv' i
).symm (some m) = m.succ
参数：n + 1；finSuccEquiv' i；some m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
-/
theorem finSuccEquiv'_symm_some_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i).symm (some m) = m.succ :=
  Fin.succAbove_of_le_castSucc i m h
/-
**finSuccEquiv'_symm_coe_below** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, m.castSucc < i → (finSuccEquiv' i
).symm (some m) = m.castSucc
参数：n + 1；finSuccEquiv' i；some m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finSuccEquiv'_symm_some_below`：∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, 
m.castSucc < i → (finSuccEquiv' i).symm (some m) = m.castSucc
-/
theorem finSuccEquiv'_symm_coe_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i).symm m = Fin.castSucc m :=
  finSuccEquiv'_symm_some_below h
/-
**finSuccEquiv'_symm_coe_above** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, i ≤ m.castSucc → (finSuccEquiv' i
).symm (some m) = m.succ
参数：n + 1；finSuccEquiv' i；some m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finSuccEquiv'_symm_some_above`：∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, 
i ≤ m.castSucc → (finSuccEquiv' i).symm (some m) = m.succ
-/
theorem finSuccEquiv'_symm_coe_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i).symm m = m.succ :=
  finSuccEquiv'_symm_some_above h

/-- Equivalence between `Fin (n + 1)` and `Option (Fin n)`.
This is a version of `Fin.pred` that produces `Option (Fin n)` instead of
requiring a proof that the input is not `0`. -/
/-
**finSuccEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finSuccEquiv (n : Nat) : Fin (n + 1) ≃ Option (Fin n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `Fin (n + 1)` and `Option (Fin n)`.
This is a version of `Fin.pred` that produces `Option (Fin n)` instead of
requiring a proof that the input is not `0`.
-/
def finSuccEquiv (n : ℕ) : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' 0

@[simp]
/-
**finSuccEquiv_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccEquiv_zero : (finSuccEquiv n) 0 = none
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem finSuccEquiv_zero : (finSuccEquiv n) 0 = none :=
  rfl

@[simp]
/-
**finSuccEquiv_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccEquiv_succ (m : Fin n) : (finSuccEquiv n) m.succ = some m
参数：m : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finSuccEquiv'_above`：∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, i ≤ m.cast
Succ → (finSuccEquiv' i) m.succ = some m
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
-/
theorem finSuccEquiv_succ (m : Fin n) : (finSuccEquiv n) m.succ = some m :=
  finSuccEquiv'_above (Fin.zero_le _)

@[simp]
/-
**finSuccEquiv_last** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccEquiv_last (n : Nat) : finSuccEquiv (n + 1) (Fin.last (n + 1)) = Fi
n.last n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finSuccEquiv_last (n : ℕ) : finSuccEquiv (n + 1) (Fin.last (n + 1)) = Fin.last n := rfl

@[simp]
/-
**finSuccEquiv_symm_none** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccEquiv_symm_none : (finSuccEquiv n).symm none = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finSuccEquiv'_symm_none`：∀ {n : ℕ} (i : Fin (n + 1)), (finSuccEquiv' i).
symm none = i
-/
theorem finSuccEquiv_symm_none : (finSuccEquiv n).symm none = 0 :=
  finSuccEquiv'_symm_none _

@[simp]
/-
**finSuccEquiv_symm_some** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccEquiv_symm_some (m : Fin n) : (finSuccEquiv n).symm (some m) = m.su
cc
参数：m : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.succAbove_zero`：∀ {n : ℕ}, Fin.succAbove 0 = Fin.succ
-/
theorem finSuccEquiv_symm_some (m : Fin n) : (finSuccEquiv n).symm (some m) = m.succ :=
  congr_fun Fin.succAbove_zero m

@[simp]
/-
**finSuccEquiv_eq_some** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccEquiv_eq_some {i : Fin (n + 1)} {j : Fin n} : finSuccEquiv n i = j 
↔ i = j.succ
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem finSuccEquiv_eq_some {i : Fin (n + 1)} {j : Fin n} :
    finSuccEquiv n i = j ↔ i = j.succ :=
  (finSuccEquiv n).eq_symm_apply.symm

@[simp]
/-
**finSuccEquiv_eq_none** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccEquiv_eq_none {i : Fin (n + 1)} : finSuccEquiv n i = none ↔ i = 0
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem finSuccEquiv_eq_none {i : Fin (n + 1)} : finSuccEquiv n i = none ↔ i = 0 :=
  (finSuccEquiv n).eq_symm_apply.symm

/-- The equiv version of `Fin.predAbove_zero`. -/
/-
**finSuccEquiv'_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ}, finSuccEquiv' 0 = finSuccEquiv n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
The equiv version of `Fin.predAbove_zero`.
-/
theorem finSuccEquiv'_zero : finSuccEquiv' (0 : Fin (n + 1)) = finSuccEquiv n :=
  rfl
/-
**finSuccEquiv'_last_apply_castSucc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} (i : Fin n), (finSuccEquiv' (Fin.last n)) i.castSucc = some i
参数：i : Fin n；finSuccEquiv' (Fin.last n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succAbove_last`：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
· 使用定理 `finSuccEquiv'_succAbove`：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), (finSu
ccEquiv' i) (i.succAbove j) = some j
-/
theorem finSuccEquiv'_last_apply_castSucc (i : Fin n) :
    finSuccEquiv' (Fin.last n) (Fin.castSucc i) = i := by
  rw [← Fin.succAbove_last, finSuccEquiv'_succAbove]
/-
**finSuccEquiv'_last_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} {i : Fin (n + 1)} (h : i ≠ Fin.last n), (finSuccEquiv' (Fin.last
 n)) i = some (i.castLT ⋯)
参数：n + 1；h : i ≠ Fin.last n；finSuccEquiv' (Fin.last n)；i.castLT ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.val_lt_last`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n → ↑i < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.succAbove_last`：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSuccEquiv'_last_apply {i : Fin (n + 1)} (h : i ≠ Fin.last n) :
    finSuccEquiv' (Fin.last n) i = Fin.castLT i (Fin.val_lt_last h) := by
  simp
/-
**finSuccEquiv'_ne_last_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} {i j : Fin (n + 1)} (hi : i ≠ Fin.last n), j ≠ i → (finSuccEquiv
' i) j = some ((i.castLT ⋯).predAbove j)
参数：n + 1；hi : i ≠ Fin.last n；finSuccEquiv' i；(i.castLT ⋯).predAbove j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.val_lt_last`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n → ↑i < n
· 使用引理 `Fin.exists_succAbove_eq`：exists_succAbove_eq {x y : Fin (n + 1)} (h : x 
!= y) : exists z, y.succAbove z = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.exists_castSucc_eq`：∀ {n : ℕ} {i : Fin (n + 1)}, (∃ j, j.castSucc = 
i) ↔ i ≠ Fin.last n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finSuccEquiv'_succAbove`：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), (finSu
ccEquiv' i) (i.succAbove j) = some j
· 使用引理 `Fin.predAbove_succAbove`：predAbove_succAbove (p : Fin n) (i : Fin n) : p
.predAbove ((castSucc p).succAbove i) = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSuccEquiv'_ne_last_apply {i j : Fin (n + 1)} (hi : i ≠ Fin.last n) (hj : j ≠ i) :
    finSuccEquiv' i j = (i.castLT (Fin.val_lt_last hi)).predAbove j := by
  rcases Fin.exists_succAbove_eq hj with ⟨j, rfl⟩
  rcases Fin.exists_castSucc_eq.2 hi with ⟨i, rfl⟩
  simp

/-- `Fin.succAbove` as a bijection between `Fin n` and `{x : Fin (n + 1) // x ≠ p}`. -/
/-
**finSuccAboveEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finSuccAboveEquiv (p : Fin (n + 1)) : Fin n ≃ { x : Fin (n + 1) // x != p 
}
参数：p : Fin (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`Fin.succAbove` as a bijection between `Fin n` and `{x : Fin (n + 1) // x ≠ p}`.
-/
def finSuccAboveEquiv (p : Fin (n + 1)) : Fin n ≃ { x : Fin (n + 1) // x ≠ p } :=
  .optionSubtype p ⟨(finSuccEquiv' p).symm, rfl⟩
/-
**finSuccAboveEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccAboveEquiv_apply (p : Fin (n + 1)) (i : Fin n) : finSuccAboveEquiv 
p i = ⟨p.succAbove i, p.succAbove_ne i⟩
参数：p : Fin (n + 1)；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finSuccAboveEquiv_apply (p : Fin (n + 1)) (i : Fin n) :
    finSuccAboveEquiv p i = ⟨p.succAbove i, p.succAbove_ne i⟩ :=
  rfl
/-
**finSuccAboveEquiv_symm_apply_last** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccAboveEquiv_symm_apply_last (x : { x : Fin (n + 1) // x != Fin.last 
n }) : (finSuccAboveEquiv (Fin.last n)).symm x = Fin.castLT x.1 (Fin.val_lt_last
 x.2)
参数：x : { x : Fin (n + 1) // x != Fin.last n }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Fin.val_lt_last`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n → ↑i < n
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.optionSubtype_apply_symm_apply`：optionSubtype_apply_symm_apply [De
cidableEq β] (x : β) (e : { e : Option α ≃ β // e none = x }) (b : { y : β // y 
!= x }) : ↑((optionSubtype…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.succAbove_last`：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSuccAboveEquiv_symm_apply_last (x : { x : Fin (n + 1) // x ≠ Fin.last n }) :
    (finSuccAboveEquiv (Fin.last n)).symm x = Fin.castLT x.1 (Fin.val_lt_last x.2) := by
  rw [← Option.some_inj]
  simp [finSuccAboveEquiv]
/-
**finSuccAboveEquiv_symm_apply_ne_last** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccAboveEquiv_symm_apply_ne_last {p : Fin (n + 1)} (h : p != Fin.last 
n) (x : { x : Fin (n + 1) // x != p }) : (finSuccAboveEquiv p).symm x = (p.castL
T (Fin.val_lt_last h)).predAbove x
参数：n + 1；h : p != Fin.last n；x : { x : Fin (n + 1) // x != p }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Fin.val_lt_last`：∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ Fin.last n → ↑i < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.optionSubtype_apply_symm_apply`：optionSubtype_apply_symm_apply [De
cidableEq β] (x : β) (e : { e : Option α ≃ β // e none = x }) (b : { y : β // y 
!= x }) : ↑((optionSubtype…
· 使用定理 `finSuccEquiv'_ne_last_apply`：∀ {n : ℕ} {i j : Fin (n + 1)} (hi : i ≠ Fin
.last n), j ≠ i → (finSuccEquiv' i) j = some ((i.castLT ⋯).predAbove j)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem finSuccAboveEquiv_symm_apply_ne_last {p : Fin (n + 1)} (h : p ≠ Fin.last n)
    (x : { x : Fin (n + 1) // x ≠ p }) :
    (finSuccAboveEquiv p).symm x = (p.castLT (Fin.val_lt_last h)).predAbove x := by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv] using finSuccEquiv'_ne_last_apply h x.property

/-- `Equiv` between `Fin (n + 1)` and `Option (Fin n)` sending `Fin.last n` to `none` -/
/-
**finSuccEquivLast** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finSuccEquivLast : Fin (n + 1) ≃ Option (Fin n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv` between `Fin (n + 1)` and `Option (Fin n)` sending `Fin.last n` to `none
`
-/
def finSuccEquivLast : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' (Fin.last n)

@[simp]
/-
**finSuccEquivLast_castSucc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccEquivLast_castSucc (i : Fin n) : finSuccEquivLast (Fin.castSucc i) 
= some i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finSuccEquiv'_below`：∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, m.castSucc
 < i → (finSuccEquiv' i) m.castSucc = some m
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem finSuccEquivLast_castSucc (i : Fin n) : finSuccEquivLast (Fin.castSucc i) = some i :=
  finSuccEquiv'_below i.2

@[simp]
/-
**finSuccEquivLast_last** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccEquivLast_last : finSuccEquivLast (Fin.last n) = none
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finSuccEquiv'_at`：∀ {n : ℕ} (i : Fin (n + 1)), (finSuccEquiv' i) i = non
e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSuccEquivLast_last : finSuccEquivLast (Fin.last n) = none := by
  simp [finSuccEquivLast]

@[simp]
/-
**finSuccEquivLast_symm_some** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSuccEquivLast_symm_some (i : Fin n) : finSuccEquivLast.symm (some i) = 
Fin.castSucc i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finSuccEquiv'_symm_some_below`：∀ {n : ℕ} {i : Fin (n + 1)} {m : Fin n}, 
m.castSucc < i → (finSuccEquiv' i).symm (some m) = m.castSucc
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem finSuccEquivLast_symm_some (i : Fin n) :
    finSuccEquivLast.symm (some i) = Fin.castSucc i :=
  finSuccEquiv'_symm_some_below i.2
/-
**finSuccEquivLast_symm_none** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ}, finSuccEquivLast.symm none = Fin.last n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finSuccEquiv'_symm_none`：∀ {n : ℕ} (i : Fin (n + 1)), (finSuccEquiv' i).
symm none = i
-/
@[simp] theorem finSuccEquivLast_symm_none : finSuccEquivLast.symm none = Fin.last n :=
  finSuccEquiv'_symm_none _

/-- An embedding `e : Fin (n+1) ↪ ι` corresponds to an embedding `f : Fin n ↪ ι` (corresponding
the last `n` coordinates of `e`) together with a value not taken by `f` (corresponding to `e 0`). -/
/-
**Equiv.embeddingFinSucc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.embeddingFinSucc (n : Nat) (ι : Type*) : (Fin (n + 1) ↪ ι) ≃ (Σ (e :
 Fin n ↪ ι), {i // i ∉ Set.range e})
参数：n : Nat；ι : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
An embedding `e : Fin (n+1) ↪ ι` corresponds to an embedding `f : Fin n ↪ ι` (co
rresponding
the last `n` coordinates of `e`) together with a value not taken by `f` (corresp
onding to `e 0`).
-/
def Equiv.embeddingFinSucc (n : ℕ) (ι : Type*) :
    (Fin (n + 1) ↪ ι) ≃ (Σ (e : Fin n ↪ ι), {i // i ∉ Set.range e}) :=
  ((finSuccEquiv n).embeddingCongr (Equiv.refl ι)).trans
    (Function.Embedding.optionEmbeddingEquiv (Fin n) ι)
/-
**Equiv.embeddingFinSucc_fst** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {n : ℕ} {ι : Type u_1} (e : Fin (n + 1) ↪ ι), ⇑((Equiv.embeddingFinSucc 
n ι) e).fst = ⇑e ∘ Fin.succ
参数：e : Fin (n + 1) ↪ ι；(Equiv.embeddingFinSucc n ι) e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Equiv.embeddingFinSucc_fst {n : ℕ} {ι : Type*} (e : Fin (n + 1) ↪ ι) :
    ((Equiv.embeddingFinSucc n ι e).1 : Fin n → ι) = e ∘ Fin.succ := rfl
/-
**Equiv.embeddingFinSucc_snd** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {n : ℕ} {ι : Type u_1} (e : Fin (n + 1) ↪ ι), ↑((Equiv.embeddingFinSucc 
n ι) e).snd = e 0
参数：e : Fin (n + 1) ↪ ι；(Equiv.embeddingFinSucc n ι) e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Equiv.embeddingFinSucc_snd {n : ℕ} {ι : Type*} (e : Fin (n + 1) ↪ ι) :
    ((Equiv.embeddingFinSucc n ι e).2 : ι) = e 0 := rfl
/-
**Equiv.coe_embeddingFinSucc_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {n : ℕ} {ι : Type u_1} (f : (e : Fin n ↪ ι) × { i // i ∉ Set.range ⇑e })
,   ⇑((Equiv.embeddingFinSucc n ι).symm f) = Fin.cons ↑f.snd ⇑f.fst
参数：f : (e : Fin n ↪ ι) × { i // i ∉ Set.range ⇑e }；(Equiv.embeddingFinSucc n ι).
symm f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma Equiv.coe_embeddingFinSucc_symm {n : ℕ} {ι : Type*}
    (f : Σ (e : Fin n ↪ ι), {i // i ∉ Set.range e}) :
    ((Equiv.embeddingFinSucc n ι).symm f : Fin (n + 1) → ι) = Fin.cons f.2.1 f.1 := by
  ext i
  exact Fin.cases rfl (fun j ↦ rfl) i

/-- Equivalence between `Fin m ⊕ Fin n` and `Fin (m + n)` -/
/-
**finSumFinEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finSumFinEquiv : Fin m oplus Fin n ≃ Fin (m + n) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `Fin m ⊕ Fin n` and `Fin (m + n)`
-/
def finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n) where
  toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := @Fin.addCases m n (fun _ => Fin m ⊕ Fin n) Sum.inl Sum.inr i
  left_inv x := by rcases x with y | y <;> simp
  right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp

@[simp]
/-
**finSumFinEquiv_apply_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSumFinEquiv_apply_left (i : Fin m) : (finSumFinEquiv (Sum.inl i) : Fin 
(m + n)) = Fin.castAdd n i
参数：i : Fin m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finSumFinEquiv_apply_left (i : Fin m) :
    (finSumFinEquiv (Sum.inl i) : Fin (m + n)) = Fin.castAdd n i :=
  rfl

@[simp]
/-
**finSumFinEquiv_apply_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSumFinEquiv_apply_right (i : Fin n) : (finSumFinEquiv (Sum.inr i) : Fin
 (m + n)) = Fin.natAdd m i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finSumFinEquiv_apply_right (i : Fin n) :
    (finSumFinEquiv (Sum.inr i) : Fin (m + n)) = Fin.natAdd m i :=
  rfl

@[simp]
/-
**finSumFinEquiv_symm_apply_castAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSumFinEquiv_symm_apply_castAdd (x : Fin m) : finSumFinEquiv.symm (Fin.c
astAdd n x) = Sum.inl x
参数：x : Fin m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem finSumFinEquiv_symm_apply_castAdd (x : Fin m) :
    finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x :=
  finSumFinEquiv.symm_apply_apply (Sum.inl x)

@[simp]
/-
**finSumFinEquiv_symm_apply_castSucc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSumFinEquiv_symm_apply_castSucc (x : Fin m) : finSumFinEquiv.symm (Fin.
castSucc x) = Sum.inl x
参数：x : Fin m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finSumFinEquiv_symm_apply_castAdd`：finSumFinEquiv_symm_apply_castAdd (x 
: Fin m) : finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x
-/
theorem finSumFinEquiv_symm_apply_castSucc (x : Fin m) :
    finSumFinEquiv.symm (Fin.castSucc x) = Sum.inl x :=
  finSumFinEquiv_symm_apply_castAdd x

@[simp]
/-
**finSumFinEquiv_symm_apply_natAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSumFinEquiv_symm_apply_natAdd (x : Fin n) : finSumFinEquiv.symm (Fin.na
tAdd m x) = Sum.inr x
参数：x : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem finSumFinEquiv_symm_apply_natAdd (x : Fin n) :
    finSumFinEquiv.symm (Fin.natAdd m x) = Sum.inr x :=
  finSumFinEquiv.symm_apply_apply (Sum.inr x)

@[simp]
/-
**finSumFinEquiv_symm_last** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSumFinEquiv_symm_last : finSumFinEquiv.symm (Fin.last n) = Sum.inr 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finSumFinEquiv_symm_apply_natAdd`：finSumFinEquiv_symm_apply_natAdd (x : 
Fin n) : finSumFinEquiv.symm (Fin.natAdd m x) = Sum.inr x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem finSumFinEquiv_symm_last : finSumFinEquiv.symm (Fin.last n) = Sum.inr 0 :=
  finSumFinEquiv_symm_apply_natAdd 0

/-- Equivalence between `Fin n ⊕ ℕ` and `ℕ` that sends `inl (a : Fin n)` to
`(a : ℕ)` and `inr a` to `n + a`. -/
/-
**finSumNatEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finSumNatEquiv (n : Nat) : Fin n oplus Nat ≃ Nat where toFun
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `Fin n ⊕ ℕ` and `ℕ` that sends `inl (a : Fin n)` to
`(a : ℕ)` and `inr a` to `n + a`.
-/
def finSumNatEquiv (n : ℕ) : Fin n ⊕ ℕ ≃ ℕ where
  toFun := Sum.elim Fin.val (n + ·)
  invFun i := if hi : i < n then .inl ⟨i, hi⟩ else .inr (i - n)
  left_inv i := (i.casesOn
    (fun _ => dif_pos (Fin.is_lt _))
    (fun _ => (dif_neg (Nat.le_add_right _ _).not_gt).trans <|
      congrArg _ (Nat.add_sub_cancel_left _ _)))
  right_inv i := (apply_dite _ _ _ _).trans <| (i.lt_or_ge n).by_cases
    (fun hi => dif_pos hi)
    (fun hi => (dif_neg hi.not_gt).trans <| Nat.add_sub_cancel' hi)
/-
**finSumNatEquiv_apply_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} (i : Fin n), (finSumNatEquiv n) (Sum.inl i) = ↑i
参数：i : Fin n；finSumNatEquiv n；Sum.inl i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem finSumNatEquiv_apply_left (i : Fin n) :
    finSumNatEquiv n (.inl i) = i := rfl
/-
**finSumNatEquiv_apply_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} (i : ℕ), (finSumNatEquiv n) (Sum.inr i) = n + i
参数：i : ℕ；finSumNatEquiv n；Sum.inr i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem finSumNatEquiv_apply_right (i : ℕ) :
    finSumNatEquiv n (.inr i) = n + i := rfl
/-
**finSumNatEquiv_symm_apply_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n i : ℕ} (hi : i < n), (finSumNatEquiv n).symm i = Sum.inl ⟨i, hi⟩
参数：hi : i < n；finSumNatEquiv n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
@[simp] theorem finSumNatEquiv_symm_apply_of_lt {i : ℕ} (hi : i < n) :
    (finSumNatEquiv n).symm i = .inl ⟨i, hi⟩ := dif_pos hi
/-
**finSumNatEquiv_symm_apply_of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n i : ℕ}, n ≤ i → (finSumNatEquiv n).symm i = Sum.inr (i - n)
参数：finSumNatEquiv n；i - n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.not_lt_of_ge`：∀ {a b : ℕ}, b ≥ a → ¬b < a
-/
@[simp] theorem finSumNatEquiv_symm_apply_of_ge {i : ℕ} (hi : n ≤ i) :
    (finSumNatEquiv n).symm i = .inr (i - n) := dif_neg (Nat.not_lt_of_ge hi)
/-
**finSumNatEquiv_symm_apply_fin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSumNatEquiv_symm_apply_fin (i : Fin n) : (finSumNatEquiv n).symm i = .i
nl i
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finSumNatEquiv_symm_apply_of_lt`：∀ {n i : ℕ} (hi : i < n), (finSumNatEqu
iv n).symm i = Sum.inl ⟨i, hi⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSumNatEquiv_symm_apply_fin (i : Fin n) :
    (finSumNatEquiv n).symm i = .inl i := by simp
/-
**finSumNatEquiv_symm_apply_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSumNatEquiv_symm_apply_add_left (i : Nat) : (finSumNatEquiv n).symm (i 
+ n) = .inr i
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finSumNatEquiv_symm_apply_of_ge`：∀ {n i : ℕ}, n ≤ i → (finSumNatEquiv n)
.symm i = Sum.inr (i - n)
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSumNatEquiv_symm_apply_add_left (i : ℕ) :
    (finSumNatEquiv n).symm (i + n) = .inr i := by simp
/-
**finSumNatEquiv_symm_apply_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSumNatEquiv_symm_apply_add_right (i : Nat) : (finSumNatEquiv n).symm (n
 + i) = .inr i
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finSumNatEquiv_symm_apply_of_ge`：∀ {n i : ℕ}, n ≤ i → (finSumNatEquiv n)
.symm i = Sum.inr (i - n)
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finSumNatEquiv_symm_apply_add_right (i : ℕ) :
    (finSumNatEquiv n).symm (n + i) = .inr i := by simp
/-
**isLeft_finSumNatEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} (i : ℕ), ((finSumNatEquiv n).symm i).isLeft = decide (i < n)
参数：i : ℕ；(finSumNatEquiv n).symm i；i < n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finSumNatEquiv_symm_apply_of_lt`：∀ {n i : ℕ} (hi : i < n), (finSumNatEqu
iv n).symm i = Sum.inl ⟨i, hi⟩
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finSumNatEquiv_symm_apply_of_ge`：∀ {n i : ℕ}, n ≤ i → (finSumNatEquiv n)
.symm i = Sum.inr (i - n)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
-/
@[simp] theorem isLeft_finSumNatEquiv_symm_apply (i : ℕ) :
    ((finSumNatEquiv n).symm i).isLeft = decide (i < n) := by
  rcases i.lt_or_ge n with hi | hi
  · simp_rw [finSumNatEquiv_symm_apply_of_lt hi, hi, Sum.isLeft_inl, decide_true]
  · simp_rw [finSumNatEquiv_symm_apply_of_ge hi, hi.not_gt, Sum.isLeft_inr, decide_false]
/-
**isRight_finSumNatEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {n : ℕ} (i : ℕ), ((finSumNatEquiv n).symm i).isRight = decide (n ≤ i)
参数：i : ℕ；(finSumNatEquiv n).symm i；n ≤ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem isRight_finSumNatEquiv_symm_apply (i : ℕ) :
    ((finSumNatEquiv n).symm i).isRight = decide (n ≤ i) := by
  simp_rw [← not_lt, decide_not, ← isLeft_finSumNatEquiv_symm_apply]
  cases (finSumNatEquiv n).symm i <;> rfl

/-- The equivalence between `Fin (m + n)` and `Fin (n + m)` which rotates by `n`. -/
/-
**finAddFlip** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finAddFlip : Fin (m + n) ≃ Fin (n + m)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The equivalence between `Fin (m + n)` and `Fin (n + m)` which rotates by `n`.
-/
def finAddFlip : Fin (m + n) ≃ Fin (n + m) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv

@[simp]
/-
**finAddFlip_apply_castAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finAddFlip_apply_castAdd (k : Fin m) (n : Nat) : finAddFlip (Fin.castAdd n
 k) = Fin.natAdd n k
参数：k : Fin m；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `finSumFinEquiv_symm_apply_castAdd`：finSumFinEquiv_symm_apply_castAdd (x 
: Fin m) : finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finAddFlip_apply_castAdd (k : Fin m) (n : ℕ) :
    finAddFlip (Fin.castAdd n k) = Fin.natAdd n k := by simp [finAddFlip]

@[simp]
/-
**finAddFlip_apply_natAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finAddFlip_apply_natAdd (k : Fin n) (m : Nat) : finAddFlip (Fin.natAdd m k
) = Fin.castAdd m k
参数：k : Fin n；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `finSumFinEquiv_symm_apply_natAdd`：finSumFinEquiv_symm_apply_natAdd (x : 
Fin n) : finSumFinEquiv.symm (Fin.natAdd m x) = Sum.inr x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finAddFlip_apply_natAdd (k : Fin n) (m : ℕ) :
    finAddFlip (Fin.natAdd m k) = Fin.castAdd m k := by simp [finAddFlip]

@[simp]
/-
**finAddFlip_apply_mk_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finAddFlip_apply_mk_left {k : Nat} (h : k < m) (hk : k < m + n
参数：h : k < m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `finAddFlip_apply_castAdd`：finAddFlip_apply_castAdd (k : Fin m) (n : Nat)
 : finAddFlip (Fin.castAdd n k) = Fin.natAdd n k
-/
theorem finAddFlip_apply_mk_left {k : ℕ} (h : k < m) (hk : k < m + n := Nat.lt_add_right n h)
    (hnk : n + k < n + m := Nat.add_lt_add_left h n) :
    finAddFlip (⟨k, hk⟩ : Fin (m + n)) = ⟨n + k, hnk⟩ := by
  convert! finAddFlip_apply_castAdd ⟨k, h⟩ n

@[simp]
/-
**finAddFlip_apply_mk_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finAddFlip_apply_mk_right {k : Nat} (h₁ : m <= k) (h₂ : k < m + n) : finAd
dFlip (⟨k, h₂⟩ : Fin (m + n)) = ⟨k - m, by lia⟩
参数：h₁ : m <= k；h₂ : k < m + n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `finAddFlip_apply_natAdd`：finAddFlip_apply_natAdd (k : Fin n) (m : Nat) :
 finAddFlip (Fin.natAdd m k) = Fin.castAdd m k
-/
theorem finAddFlip_apply_mk_right {k : ℕ} (h₁ : m ≤ k) (h₂ : k < m + n) :
    finAddFlip (⟨k, h₂⟩ : Fin (m + n)) = ⟨k - m, by lia⟩ := by
  convert! @finAddFlip_apply_natAdd n ⟨k - m, by lia⟩ m
  simp [Nat.add_sub_cancel' h₁]

/-- Equivalence between `Fin m × Fin n` and `Fin (m * n)` -/
@[simps]
/-
**finProdFinEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `Fin m × Fin n` and `Fin (m * n)`
-/
def finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n) where
  toFun x :=
    ⟨x.2 + n * x.1,
      calc
        x.2.1 + n * x.1.1 + 1 = x.1.1 * n + x.2.1 + 1 := by ac_rfl
        _ ≤ x.1.1 * n + n := Nat.add_le_add_left x.2.2 _
        _ = (x.1.1 + 1) * n := Eq.symm <| Nat.succ_mul _ _
        _ ≤ m * n := Nat.mul_le_mul_right _ x.1.2
        ⟩
  invFun x := (x.divNat, x.modNat)
  left_inv := fun ⟨x, y⟩ =>
    have H : 0 < n := Nat.pos_of_ne_zero fun H => Nat.not_lt_zero y.1 <| H ▸ y.2
    Prod.ext
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) / n = y.1 / n + x.1 := Nat.add_mul_div_left _ _ H
          _ = 0 + x.1 := by rw [Nat.div_eq_of_lt y.2]
          _ = x.1 := Nat.zero_add x.1)
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) % n = y.1 % n := Nat.add_mul_mod_self_left _ _ _
          _ = y.1 := Nat.mod_eq_of_lt y.2)
  right_inv _ := Fin.eq_of_val_eq <| Nat.mod_add_div _ _

/-- The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
This is like `finProdFinEquiv.symm` but with `m` infinite.
See `Nat.div_mod_unique` for a similar propositional statement. -/
@[simps]
/-
**Nat.divModEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Nat.divModEquiv (n : Nat) [NeZero n] : Nat ≃ Nat × Fin n where toFun a
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_add_mod'`：∀ (a b : ℕ), a / b * b + a % b = a

--- 原说明 ---
The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
This is like `finProdFinEquiv.symm` but with `m` infinite.
See `Nat.div_mod_unique` for a similar propositional statement.
-/
def Nat.divModEquiv (n : ℕ) [NeZero n] : ℕ ≃ ℕ × Fin n where
  toFun a := (a / n, Fin.ofNat n a)
  invFun p := p.1 * n + ↑p.2
  -- TODO: is there a canonical order of `*` and `+` here?
  left_inv _ := Nat.div_add_mod' _ _
  right_inv p := by
    refine Prod.ext ?_ (Fin.ext <| Nat.mul_add_mod_of_lt p.2.is_lt)
    dsimp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ n.pos_of_neZero, Nat.div_eq_of_lt p.2.is_lt,
      Nat.zero_add]

/-- The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
See `Int.ediv_emod_unique` for a similar propositional statement. -/
@[simps]
/-
**Int.divModEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Int.divModEquiv (n : Nat) [NeZero n] : Int ≃ Int × Fin n where -- TODO: co
uld cast from int directly if we import `Data.ZMod.Defs`, though there are few l
emmas -- about that coercion. toFun a
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
See `Int.ediv_emod_unique` for a similar propositional statement.
-/
def Int.divModEquiv (n : ℕ) [NeZero n] : ℤ ≃ ℤ × Fin n where
  -- TODO: could cast from int directly if we import `Data.ZMod.Defs`, though there are few lemmas
  -- about that coercion.
  toFun a := (a / n, Fin.ofNat n (a.natMod n))
  invFun p := p.1 * n + ↑p.2
  left_inv a := by
    simp_rw [Fin.val_ofNat, natCast_mod, natMod,
      toNat_of_nonneg (emod_nonneg _ <| natCast_eq_zero.not.2 (NeZero.ne n)), emod_emod,
      ediv_mul_add_emod]
  right_inv := fun ⟨q, r, hrn⟩ => by
    simp only [Prod.mk_inj, Fin.ext_iff]
    obtain ⟨h1, h2⟩ := Int.natCast_nonneg r, Int.ofNat_lt.2 hrn
    rw [Int.add_comm, add_mul_ediv_right _ _ (natCast_eq_zero.not.2 (NeZero.ne n)),
      ediv_eq_zero_of_lt h1 h2, natMod, add_mul_emod_self_right, emod_eq_of_lt h1 h2, toNat_natCast]
    exact ⟨q.zero_add, Fin.val_cast_of_lt hrn⟩

/-- Promote a `Fin n` into a larger `Fin m`, as a subtype where the underlying
values are retained.

This is the `Equiv` version of `Fin.castLE`. -/
@[simps apply symm_apply]
/-
**Fin.castLEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fin.castLEquiv {n m : Nat} (h : n <= m) : Fin n ≃ { i : Fin m // (i : Nat)
 < n } where toFun i
参数：h : n <= m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote a `Fin n` into a larger `Fin m`, as a subtype where the underlying
values are retained.

This is the `Equiv` version of `Fin.castLE`.
-/
def Fin.castLEquiv {n m : ℕ} (h : n ≤ m) : Fin n ≃ { i : Fin m // (i : ℕ) < n } where
  toFun i := ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- The natural `Equiv` between `(Fin m → α) × (Fin n → α)` and `Fin (m + n) → α` -/
@[simps]
/-
**Fin.appendEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fin.appendEquiv {α : Type*} (m n : Nat) : (Fin m -> α) × (Fin n -> α) ≃ (F
in (m + n) -> α) where toFun fg
参数：m n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `Equiv` between `(Fin m → α) × (Fin n → α)` and `Fin (m + n) → α`
-/
def Fin.appendEquiv {α : Type*} (m n : ℕ) :
    (Fin m → α) × (Fin n → α) ≃ (Fin (m + n) → α) where
  toFun fg := Fin.append fg.1 fg.2
  invFun f := ⟨fun i ↦ f (Fin.castAdd n i), fun i ↦ f (Fin.natAdd m i)⟩
  left_inv fg := by simp
  right_inv f := by simp [Fin.append_castAdd_natAdd]

/-- `Fin (n + 1) → α` and `(Fin n → α) × α` are equivalent. -/
@[simps!]
/-
**Fin.succFunEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fin.succFunEquiv (α : Type*) (n : Nat) : (Fin (n + 1) -> α) ≃ (Fin n -> α)
 × α
参数：α : Type*；n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`Fin (n + 1) → α` and `(Fin n → α) × α` are equivalent.
-/
def Fin.succFunEquiv (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ (Fin n → α) × α :=
  (appendEquiv n 1).symm.trans (Equiv.prodCongrRight fun _ ↦ Equiv.funUnique (Fin 1) α)
