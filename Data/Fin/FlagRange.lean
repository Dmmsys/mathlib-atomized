/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Preorder.Chain

/-!
# Range of `f : Fin (n + 1) → α` as a `Flag`

Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.

Then the range of `f` is a maximal chain.

We formulate this result in terms of `IsMaxChain` and `Flag`.
-/

@[expose] public section

open Set

variable {α : Type*} [PartialOrder α] [BoundedOrder α] {n : ℕ} {f : Fin (n + 1) → α}

/-- Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.

Then the range of `f` is a maximal chain. -/
/-
**IsMaxChain.range_fin_of_covBy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxChain.range_fin_of_covBy (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤) (hc
ovBy : forall k : Fin n, f k.castSucc ⩿ f k.succ) : IsMaxChain (· <= ·) (range f
)
参数：h0 : f 0 = ⊥；hlast : f (.last n) = ⊤；hcovBy : forall k : Fin n, f k.castSucc 
⩿ f k.succ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Fin.monotone_iff_le_succ`：monotone_iff_le_succ : Monotone f ↔ forall i :
 Fin n, f (castSucc i) <= f i.succ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Monotone.isChain_range`：Monotone.isChain_range [LinearOrder α] [Preorder
 β] {f : α -> β} (hf : Monotone f) : IsChain (· <= ·) (range f)
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `IsChain.lt_of_le`：IsChain.lt_of_le [PartialOrder α] {s : Set α} (h : IsC
hain (· <= ·) s) : IsChain (· < ·) s
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.

Then the range of `f` is a maximal chain.
-/
theorem IsMaxChain.range_fin_of_covBy (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
    (hcovBy : ∀ k : Fin n, f k.castSucc ⩿ f k.succ) :
    IsMaxChain (· ≤ ·) (range f) := by
  have hmono : Monotone f := Fin.monotone_iff_le_succ.2 fun k ↦ (hcovBy k).1
  refine ⟨hmono.isChain_range, fun t htc hbt ↦ hbt.antisymm fun x hx ↦ ?_⟩
  rw [mem_range]; by_contra! h
  suffices ∀ k, f k < x by simpa [hlast] using this (.last _)
  intro k
  induction k using Fin.induction with
  | zero => simpa [h0, bot_lt_iff_ne_bot] using (h 0).symm
  | succ k ihk =>
    rw [range_subset_iff] at hbt
    exact (htc.lt_of_le (hbt k.succ) hx (h _)).resolve_right ((hcovBy k).2 ihk)

/-- Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.

Then the range of `f` is a `Flag α`. -/
@[simps]
/-
**Flag.rangeFin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Flag.rangeFin (f : Fin (n + 1) -> α) (h0 : f 0 = ⊥) (hlast : f (.last n) =
 ⊤) (hcovBy : forall k : Fin n, f k.castSucc ⩿ f k.succ) : Flag α where carrier
参数：f : Fin (n + 1) -> α；h0 : f 0 = ⊥；hlast : f (.last n) = ⊤；hcovBy : forall k :
 Fin n, f k.castSucc ⩿ f k.succ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.

Then the range of `f` is a `Flag α`.
-/
def Flag.rangeFin (f : Fin (n + 1) → α) (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
    (hcovBy : ∀ k : Fin n, f k.castSucc ⩿ f k.succ) : Flag α where
  carrier := range f
  Chain' := (IsMaxChain.range_fin_of_covBy h0 hlast hcovBy).1
  max_chain' := (IsMaxChain.range_fin_of_covBy h0 hlast hcovBy).2
/-
**Flag.mem_rangeFin** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : BoundedOrder α] {n : ℕ}
 {f : Fin (n + 1) → α} {x : α} {h0 : f 0 = ⊥}   {hlast : f (Fin.last n) = ⊤} {hc
ovBy : ∀ (k : Fin n), f k.castSucc ⩿ f k.succ},   x ∈ Flag.rangeFin f h0 hlast h
covBy ↔ ∃ k, f k = x
参数：n + 1；Fin.last n；k : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem Flag.mem_rangeFin {x h0 hlast hcovBy} :
    x ∈ rangeFin f h0 hlast hcovBy ↔ ∃ k, f k = x :=
  Iff.rfl
