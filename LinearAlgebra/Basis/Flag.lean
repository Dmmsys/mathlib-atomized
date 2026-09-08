/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Data.Fin.FlagRange
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Flag of submodules defined by a basis

In this file we define `Basis.flag b k`, where `b : Basis (Fin n) R M`, `k : Fin (n + 1)`,
to be the subspace spanned by the first `k` vectors of the basis `b`.

We also prove some lemmas about this definition.
-/

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- This is why this section is `noncomputable`.
-- See https://github.com/leanprover/lean4/issues/14084.
@[expose] public noncomputable section

open Set Submodule

namespace Module.Basis

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

/-- The subspace spanned by the first `k` vectors of the basis `b`. -/
/-
**Module.Basis.flag** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：flag (b : Basis (Fin n) R M) (k : Fin (n + 1)) : Submodule R M
参数：b : Basis (Fin n) R M；k : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subspace spanned by the first `k` vectors of the basis `b`.
-/
def flag (b : Basis (Fin n) R M) (k : Fin (n + 1)) : Submodule R M :=
  .span R <| b '' {i | i.castSucc < k}

@[simp]
/-
**Module.Basis.flag_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：flag_zero (b : Basis (Fin n) R M) : b.flag 0 = ⊥
参数：b : Basis (Fin n) R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem flag_zero (b : Basis (Fin n) R M) : b.flag 0 = ⊥ := by simp [flag]

@[simp]
/-
**Module.Basis.flag_last** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：flag_last (b : Basis (Fin n) R M) : b.flag (.last n) = ⊤
参数：b : Basis (Fin n) R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem flag_last (b : Basis (Fin n) R M) : b.flag (.last n) = ⊤ := by
  simp [flag]
/-
**Module.Basis.flag_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：flag_le_iff (b : Basis (Fin n) R M) {k p} : b.flag k <= p ↔ forall i : Fin
 n, i.castSucc < k -> b i in p
参数：b : Basis (Fin n) R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
-/
theorem flag_le_iff (b : Basis (Fin n) R M) {k p} :
    b.flag k ≤ p ↔ ∀ i : Fin n, i.castSucc < k → b i ∈ p :=
  span_le.trans forall_mem_image
/-
**Module.Basis.flag_succ** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：flag_succ (b : Basis (Fin n) R M) (k : Fin n) : b.flag k.succ = R ∙ b k ⊔ 
b.flag k.castSucc
参数：b : Basis (Fin n) R M；k : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Submodule.span_insert`：span_insert (x) (s : Set M) : span R (insert x s)
 = R ∙ x ⊔ span R s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem flag_succ (b : Basis (Fin n) R M) (k : Fin n) :
    b.flag k.succ = R ∙ b k ⊔ b.flag k.castSucc := by
  simp only [flag, Fin.castSucc_lt_castSucc_iff]
  simp [Fin.castSucc_lt_iff_succ_le, le_iff_eq_or_lt, ofPred_or, image_insert_eq, span_insert]
/-
**Module.Basis.self_mem_flag** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：self_mem_flag (b : Basis (Fin n) R M) {i : Fin n} {k : Fin (n + 1)} (h : i
.castSucc < k) : b i in b.flag k
参数：b : Basis (Fin n) R M；n + 1；h : i.castSucc < k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem self_mem_flag (b : Basis (Fin n) R M) {i : Fin n} {k : Fin (n + 1)} (h : i.castSucc < k) :
    b i ∈ b.flag k :=
  subset_span <| mem_image_of_mem _ h

@[simp]
/-
**Module.Basis.self_mem_flag_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：self_mem_flag_iff [Nontrivial R] (b : Basis (Fin n) R M) {i : Fin n} {k : 
Fin (n + 1)} : b i in b.flag k ↔ i.castSucc < k
参数：b : Basis (Fin n) R M；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.self_mem_span_image`：self_mem_span_image [Nontrivial R] {i 
: ι} {s : Set ι} : b i in span R (b '' s) ↔ i in s
-/
theorem self_mem_flag_iff [Nontrivial R] (b : Basis (Fin n) R M) {i : Fin n} {k : Fin (n + 1)} :
    b i ∈ b.flag k ↔ i.castSucc < k :=
  b.self_mem_span_image

@[gcongr, mono]
/-
**Module.Basis.flag_mono** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：flag_mono (b : Basis (Fin n) R M) : Monotone b.flag
参数：b : Basis (Fin n) R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Fin.monotone_iff_le_succ`：monotone_iff_le_succ : Monotone f ↔ forall i :
 Fin n, f (castSucc i) <= f i.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.flag_succ`：flag_succ (b : Basis (Fin n) R M) (k : Fin n) : 
b.flag k.succ = R ∙ b k ⊔ b.flag k.castSucc
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem flag_mono (b : Basis (Fin n) R M) : Monotone b.flag :=
  Fin.monotone_iff_le_succ.2 fun k ↦ by rw [flag_succ]; exact le_sup_right
/-
**Module.Basis.isChain_range_flag** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：isChain_range_flag (b : Basis (Fin n) R M) : IsChain (· <= ·) (range b.fla
g)
参数：b : Basis (Fin n) R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.isChain_range`：Monotone.isChain_range [LinearOrder α] [Preorder
 β] {f : α -> β} (hf : Monotone f) : IsChain (· <= ·) (range f)
· 使用定理 `Module.Basis.flag_mono`：flag_mono (b : Basis (Fin n) R M) : Monotone b.f
lag
-/
theorem isChain_range_flag (b : Basis (Fin n) R M) : IsChain (· ≤ ·) (range b.flag) :=
  b.flag_mono.isChain_range

@[gcongr, mono]
/-
**Module.Basis.flag_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：flag_strictMono [Nontrivial R] (b : Basis (Fin n) R M) : StrictMono b.flag
参数：b : Basis (Fin n) R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Fin.strictMono_iff_lt_succ`：strictMono_iff_lt_succ : StrictMono f ↔ fora
ll i : Fin n, f (castSucc i) < f i.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.flag_succ`：flag_succ (b : Basis (Fin n) R M) (k : Fin n) : 
b.flag k.succ = R ∙ b k ⊔ b.flag k.castSucc
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem flag_strictMono [Nontrivial R] (b : Basis (Fin n) R M) : StrictMono b.flag :=
  Fin.strictMono_iff_lt_succ.2 fun _ ↦ by simp [flag_succ]

end Semiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

@[simp]
/-
**Module.Basis.flag_le_ker_coord_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：flag_le_ker_coord_iff [Nontrivial R] (b : Basis (Fin n) R M) {k : Fin (n +
 1)} {l : Fin n} : b.flag k <= LinearMap.ker (b.coord l) ↔ k <= l.castSucc
参数：b : Basis (Fin n) R M；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem flag_le_ker_coord_iff [Nontrivial R] (b : Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n} :
    b.flag k ≤ LinearMap.ker (b.coord l) ↔ k ≤ l.castSucc := by
  simp [flag_le_iff, Finsupp.single_apply_eq_zero, imp_false, imp_not_comm]
/-
**Module.Basis.flag_le_ker_coord** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：flag_le_ker_coord (b : Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n} (h
 : k <= l.castSucc) : b.flag k <= LinearMap.ker (b.coord l)
参数：b : Basis (Fin n) R M；n + 1；h : k <= l.castSucc。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.flag_le_ker_coord_iff`：flag_le_ker_coord_iff [Nontrivial R]
 (b : Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n} : b.flag k <= LinearMap.k
er (b.coord l) ↔ k <= l.…
-/
theorem flag_le_ker_coord (b : Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n}
    (h : k ≤ l.castSucc) : b.flag k ≤ LinearMap.ker (b.coord l) := by
  nontriviality R
  exact b.flag_le_ker_coord_iff.2 h
/-
**Module.Basis.flag_le_ker_dual** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：flag_le_ker_dual (b : Basis (Fin n) R M) (k : Fin n) : b.flag k.castSucc <
= LinearMap.ker (b.dualBasis k)
参数：b : Basis (Fin n) R M；k : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Module.Basis.flag_le_ker_coord_iff`：flag_le_ker_coord_iff [Nontrivial R]
 (b : Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n} : b.flag k <= LinearMap.k
er (b.coord l) ↔ k <= l.…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem flag_le_ker_dual (b : Basis (Fin n) R M) (k : Fin n) :
    b.flag k.castSucc ≤ LinearMap.ker (b.dualBasis k) := by
  nontriviality R
  rw [coe_dualBasis, b.flag_le_ker_coord_iff]

end CommRing

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {n : ℕ}

/-
**Module.Basis.flag_covBy** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：flag_covBy (b : Basis (Fin n) K V) (i : Fin n) : b.flag i.castSucc ⋖ b.fla
g i.succ
参数：b : Basis (Fin n) K V；i : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.flag_succ`：flag_succ (b : Basis (Fin n) R M) (k : Fin n) : 
b.flag k.succ = R ∙ b k ⊔ b.flag k.castSucc
· 使用定理 `Submodule.covBy_span_singleton_sup`：covBy_span_singleton_sup {x : V} {s 
: Submodule K V} (h : x ∉ s) : CovBy s (K ∙ x ⊔ s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem flag_covBy (b : Basis (Fin n) K V) (i : Fin n) :
    b.flag i.castSucc ⋖ b.flag i.succ := by
  rw [flag_succ]
  apply covBy_span_singleton_sup
  simp
/-
**Module.Basis.flag_wcovBy** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：flag_wcovBy (b : Basis (Fin n) K V) (i : Fin n) : b.flag i.castSucc ⩿ b.fl
ag i.succ
参数：b : Basis (Fin n) K V；i : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.wcovBy`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ⋖ b → a 
⩿ b
· 使用定理 `Module.Basis.flag_covBy`：flag_covBy (b : Basis (Fin n) K V) (i : Fin n) 
: b.flag i.castSucc ⋖ b.flag i.succ
-/
theorem flag_wcovBy (b : Basis (Fin n) K V) (i : Fin n) :
    b.flag i.castSucc ⩿ b.flag i.succ :=
  (b.flag_covBy i).wcovBy

/-- Range of `Basis.flag` as a `Flag`. -/
@[simps!]
/-
**Module.Basis.toFlag** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：toFlag (b : Basis (Fin n) K V) : Flag (Submodule K V)
参数：b : Basis (Fin n) K V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.flag_wcovBy`：flag_wcovBy (b : Basis (Fin n) K V) (i : Fin n
) : b.flag i.castSucc ⩿ b.flag i.succ

--- 原说明 ---
Range of `Basis.flag` as a `Flag`.
-/
def toFlag (b : Basis (Fin n) K V) : Flag (Submodule K V) :=
  .rangeFin b.flag b.flag_zero b.flag_last b.flag_wcovBy

@[simp]
/-
**Module.Basis.mem_toFlag** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mem_toFlag (b : Basis (Fin n) K V) {p : Submodule K V} : p in b.toFlag ↔ e
xists k, b.flag k = p
参数：b : Basis (Fin n) K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toFlag (b : Basis (Fin n) K V) {p : Submodule K V} : p ∈ b.toFlag ↔ ∃ k, b.flag k = p :=
  Iff.rfl
/-
**Module.Basis.isMaxChain_range_flag** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：isMaxChain_range_flag (b : Basis (Fin n) K V) : IsMaxChain (· <= ·) (range
 b.flag)
参数：b : Basis (Fin n) K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Flag.maxChain`：∀ {α : Type u_1} [inst : LE α] (s : Flag α), IsMaxChain (
fun x1 x2 => x1 ≤ x2) ↑s
-/
theorem isMaxChain_range_flag (b : Basis (Fin n) K V) : IsMaxChain (· ≤ ·) (range b.flag) :=
  b.toFlag.maxChain

end DivisionRing

end Module.Basis

