/-
Copyright (c) 2020 Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Kim Morrison, Eric Wieser, Oliver Nash, Wen Yang
-/
module

public import Mathlib.Data.Matrix.Basic

/-!
# Matrices with a single non-zero element.

This file provides `Matrix.single`. The matrix `Matrix.single i j c` has `c`
at position `(i, j)`, and zeroes elsewhere.
-/

@[expose] public section

assert_not_exists Matrix.trace

variable {l m n o : Type*}
variable {R S α β γ : Type*}

namespace Matrix

variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq o]

section Zero
variable [Zero α]

/-- `single i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
/-
**Matrix.single** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：single (i : m) (j : n) (a : α) : Matrix m n α
参数：i : m；j : n；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`single i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def single (i : m) (j : n) (a : α) : Matrix m n α :=
  of <| fun i' j' => if i = i' ∧ j = j' then a else 0

section
variable (i : m) (j : n) (c : α) (i' : m) (j' : n)

@[simp]
/-
**Matrix.single_apply_same** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_apply_same : single i j c i j = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem single_apply_same : single i j c i j = c :=
  if_pos (And.intro rfl rfl)

@[simp]
/-
**Matrix.single_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) : single i j c i' j' = 0
参数：h : ¬(i = i' ∧ j = j')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
theorem single_apply_of_ne (h : ¬(i = i' ∧ j = j')) : single i j c i' j' = 0 := by
  simp only [single, and_imp, ite_eq_right_iff, of_apply]
  tauto
/-
**Matrix.single_apply_of_row_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_apply_of_row_ne {i i' : m} (hi : i != i') (j j' : n) (a : α) : sing
le i j a i' j' = 0
参数：hi : i != i'；j j' : n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_apply_of_row_ne {i i' : m} (hi : i ≠ i') (j j' : n) (a : α) :
    single i j a i' j' = 0 := by simp [hi]
/-
**Matrix.single_apply_of_col_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_apply_of_col_ne (i i' : m) {j j' : n} (hj : j != j') (a : α) : sing
le i j a i' j' = 0
参数：i i' : m；hj : j != j'；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_apply_of_col_ne (i i' : m) {j j' : n} (hj : j ≠ j') (a : α) :
    single i j a i' j' = 0 := by simp [hj]

@[grind =]
/-
**Matrix.single_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：single_apply : single i j c i' j' = if i = i' ∧ j = j' then c else 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma single_apply : single i j c i' j' = if i = i' ∧ j = j' then c else 0 := rfl

end

/-- See also `single_eq_updateRow_zero` and `single_eq_updateCol_zero`. -/
/-
**Matrix.single_eq_of_single_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_eq_of_single_single (i : m) (j : n) (a : α) : single i j a = Matrix
.of (Pi.single i (Pi.single j a))
参数：i : m；j : n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
See also `single_eq_updateRow_zero` and `single_eq_updateCol_zero`.
-/
theorem single_eq_of_single_single (i : m) (j : n) (a : α) :
    single i j a = Matrix.of (Pi.single i (Pi.single j a)) := by
  ext a b
  unfold single
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [*]

@[simp]
/-
**Matrix.of_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：of_symm_single (i : m) (j : n) (a : α) : of.symm (single i j a) = Pi.singl
e i (Pi.single j a)
参数：i : m；j : n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.single_eq_of_single_single`：single_eq_of_single_single (i : m) (j
 : n) (a : α) : single i j a = Matrix.of (Pi.single i (Pi.single j a))
-/
theorem of_symm_single (i : m) (j : n) (a : α) :
    of.symm (single i j a) = Pi.single i (Pi.single j a) :=
  congr_arg of.symm <| single_eq_of_single_single i j a

@[simp]
/-
**Matrix.smul_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_single [SMulZeroClass R α] (r : R) (i : m) (j : n) (a : α) : r • sing
le i j a = single i j (r • a)
参数：r : R；i : m；j : n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_single [SMulZeroClass R α] (r : R) (i : m) (j : n) (a : α) :
    r • single i j a = single i j (r • a) := by
  unfold single
  ext
  simp [smul_ite]

@[simp]
/-
**Matrix.single_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_zero (i : m) (j : n) : single i j (0 : α) = 0
参数：i : m；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_zero (i : m) (j : n) : single i j (0 : α) = 0 := by
  unfold single
  ext
  simp

@[simp]
/-
**Matrix.transpose_single** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：transpose_single (i : m) (j : n) (a : α) : (single i j a)ᵀ = single j i a
参数：i : m；j : n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma transpose_single (i : m) (j : n) (a : α) :
    (single i j a)ᵀ = single j i a := by
  aesop (add unsafe unfold single)

@[simp]
/-
**Matrix.map_single** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：map_single (i : m) (j : n) (a : α) {β : Type*} [Zero β] {F : Type*} [FunLi
ke F α β] [ZeroHomClass F α β] (f : F) : (single i j a).map f = single i j (f a)
参数：i : m；j : n；a : α；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma map_single (i : m) (j : n) (a : α) {β : Type*} [Zero β]
    {F : Type*} [FunLike F α β] [ZeroHomClass F α β] (f : F) :
    (single i j a).map f = single i j (f a) := by
  aesop (add unsafe unfold single)
/-
**Matrix.single_mem_matrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_mem_matrix {S : Set α} (hS : 0 in S) {i : m} {j : n} {a : α} : Matr
ix.single i j a in S.matrix ↔ a in S
参数：hS : 0 in S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_mem`：ite_mem {a b : α} {s : β} : (if p then a else b) in s ↔ (p -> a
 in s) ∧ (¬p -> b in s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem single_mem_matrix {S : Set α} (hS : 0 ∈ S) {i : m} {j : n} {a : α} :
    Matrix.single i j a ∈ S.matrix ↔ a ∈ S := by
  simp only [Set.mem_matrix, single, of_apply]
  conv_lhs => intro _ _; rw [ite_mem]
  simp [hS]
/-
**Matrix.diagonal_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_single (i : m) (r : α) : diagonal (Pi.single i r) = single i i r
参数：i : m；r : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem diagonal_single (i : m) (r : α) :
    diagonal (Pi.single i r) = single i i r := by
  ext j k
  dsimp [diagonal, single]
  grind

@[simp]
/-
**Matrix.submatrix_single_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_single_equiv (f : l ≃ n) (g : m ≃ o) (i : n) (j : o) (r : α) : (
single i j r).submatrix f g = single (f.symm i) (g.symm j) r
参数：f : l ≃ n；g : m ≃ o；i : n；j : o；r : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_apply_of_row_ne`：single_apply_of_row_ne {i i' : m} (hi : i
 != i') (j j' : n) (a : α) : single i j a i' j' = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `Matrix.single_apply_of_col_ne`：single_apply_of_col_ne (i i' : m) {j j' :
 n} (hj : j != j') (a : α) : single i j a i' j' = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.single.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type u_7}
 {inst : DecidableEq m} [inst_1 : DecidableEq m] {inst_2 : DecidableEq n}   [ins
t_3 : Decidabl…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem submatrix_single_equiv
    (f : l ≃ n) (g : m ≃ o) (i : n) (j : o) (r : α) :
    (single i j r).submatrix f g = single (f.symm i) (g.symm j) r := by
  ext i' j'
  dsimp
  obtain hi | rfl := ne_or_eq (f.symm i) i'
  · rw [single_apply_of_row_ne hi, single_apply_of_row_ne]
    exact f.symm_apply_eq.not.1 hi
  obtain hj | rfl := ne_or_eq (g.symm j) j'
  · rw [single_apply_of_col_ne _ _ hj, single_apply_of_col_ne]
    exact g.symm_apply_eq.not.1 hj
  simp

end Zero

/-
**Matrix.single_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_add [AddZeroClass α] (i : m) (j : n) (a b : α) : single i j (a + b)
 = single i j a + single i j b
参数：i : m；j : n；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem single_add [AddZeroClass α] (i : m) (j : n) (a b : α) :
    single i j (a + b) = single i j a + single i j b := by
  ext
  simp only [single, of_apply]
  split_ifs with h <;> simp [h]
/-
**Matrix.single_neg** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：single_neg [NegZeroClass α] (i j : n) (b : α) : - single i j b = single i 
j (-b)
参数：i j : n；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.neg_of`：neg_of [Neg α] (f : m -> n -> α) : -of f = of (-f)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_ite`：neg_ite {α : Type*} (P : Prop) [Decidable P] [Neg α] (b : α) (c
 : α) : -(if P then b else c) = if P then -b else -c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma single_neg [NegZeroClass α] (i j : n) (b : α) :
    - single i j b = single i j (-b) :=
  neg_of _ |>.trans <| ext fun x y ↦ by simp [single, neg_ite]
/-
**Matrix.single_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_mulVec [NonUnitalNonAssocSemiring α] [Fintype m] (i : n) (j : m) (c
 : α) (x : m -> α) : mulVec (single i j c) x = Function.update (0 : n -> α) i (c
 * x j)
参数：i : n；j : m；c : α；x : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem single_mulVec [NonUnitalNonAssocSemiring α] [Fintype m]
    (i : n) (j : m) (c : α) (x : m → α) :
    mulVec (single i j c) x = Function.update (0 : n → α) i (c * x j) := by
  ext i'
  simp only [mulVec, dotProduct, single, of_apply, ite_mul, zero_mul]
  rcases eq_or_ne i i' with rfl | h
  · simp
  simp [h, h.symm]
/-
**Matrix.single_mulVec_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：single_mulVec_eq [Fintype n] [NonAssocSemiring α] (i j : n) (b : α) (w : n
 -> α) : single i j b *ᵥ w = (b * w j) • Pi.single i (1 : α)
参数：i j : n；b : α；w : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.single_mulVec`：single_mulVec [NonUnitalNonAssocSemiring α] [Finty
pe m] (i : n) (j : m) (c : α) (x : m -> α) : mulVec (single i j c) x = Function.
update (0 …
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma single_mulVec_eq [Fintype n] [NonAssocSemiring α] (i j : n) (b : α) (w : n → α) :
    single i j b *ᵥ w = (b * w j) • Pi.single i (1 : α) := by
  ext
  simp [Matrix.single_mulVec, Function.update_apply, Pi.single_apply]
/-
**Matrix.sum_single_eq_diagonal** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：sum_single_eq_diagonal [AddCommMonoid α] [Fintype m] (f : m -> α) : ∑ i : 
m, single i i (f i) = Matrix.diagonal f
参数：f : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.sum_apply`：sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finse
t β) (g : β -> Matrix m n α) : (∑ c in s, g c) i j = ∑ c in s, g c i j
· 使用定理 `Matrix.diagonal_apply`：diagonal_apply [Zero α] (d : n -> α) (i j) : diag
onal d i j = if i = j then d i else 0
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma sum_single_eq_diagonal [AddCommMonoid α] [Fintype m] (f : m → α) :
    ∑ i : m, single i i (f i) = Matrix.diagonal f := by
  ext j k
  rw [sum_apply, diagonal_apply, Finset.sum_eq_single j] <;> simp +contextual [single]
/-
**Matrix.sum_single_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：sum_single_one [AddCommMonoid α] [One α] [Fintype m] : ∑ i : m, single i i
 (1 : α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.sum_single_eq_diagonal`：sum_single_eq_diagonal [AddCommMonoid α] 
[Fintype m] (f : m -> α) : ∑ i : m, single i i (f i) = Matrix.diagonal f
-/
lemma sum_single_one [AddCommMonoid α] [One α] [Fintype m] :
    ∑ i : m, single i i (1 : α) = 1 :=
  sum_single_eq_diagonal _
/-
**Matrix.sum_single_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：sum_single_natCast [AddCommMonoidWithOne α] [Fintype m] (n : Nat) : ∑ i : 
m, single i i (n : α) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.sum_single_eq_diagonal`：sum_single_eq_diagonal [AddCommMonoid α] 
[Fintype m] (f : m -> α) : ∑ i : m, single i i (f i) = Matrix.diagonal f
-/
lemma sum_single_natCast [AddCommMonoidWithOne α] [Fintype m] (n : ℕ) :
    ∑ i : m, single i i (n : α) = n :=
  sum_single_eq_diagonal _
/-
**Matrix.sum_single_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：sum_single_ofNat [AddCommMonoidWithOne α] [Fintype m] (n : Nat) [n.AtLeast
Two] : ∑ i : m, single i i (ofNat(n) : α) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.sum_single_eq_diagonal`：sum_single_eq_diagonal [AddCommMonoid α] 
[Fintype m] (f : m -> α) : ∑ i : m, single i i (f i) = Matrix.diagonal f
-/
lemma sum_single_ofNat [AddCommMonoidWithOne α] [Fintype m] (n : ℕ) [n.AtLeastTwo] :
    ∑ i : m, single i i (ofNat(n) : α) = ofNat(n) :=
  sum_single_eq_diagonal _
/-
**Matrix.sum_single_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：sum_single_intCast [AddCommGroupWithOne α] [Fintype m] (z : Int) : ∑ i : m
, single i i (z : α) = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.sum_single_eq_diagonal`：sum_single_eq_diagonal [AddCommMonoid α] 
[Fintype m] (f : m -> α) : ∑ i : m, single i i (f i) = Matrix.diagonal f
-/
lemma sum_single_intCast [AddCommGroupWithOne α] [Fintype m] (z : ℤ) :
    ∑ i : m, single i i (z : α) = z :=
  sum_single_eq_diagonal _
/-
**Matrix.sum_sum_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：sum_sum_single [AddCommMonoid α] [Fintype m] [Fintype n] (x : m -> n -> α)
 : ∑ i : m, ∑ j : n, single i j (x i j) = of x
参数：x : m -> n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.sum_prod_type'`：∀ {γ : Type u_3} {α₁ : Type u_4} {α₂ : Type u_5}
 [inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid γ]   (f : α₁ 
→ α₂ → γ), ∑…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `Matrix.sum_apply`：sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finse
t β) (g : β -> Matrix m n α) : (∑ c in s, g c) i j = ∑ c in s, g c i j
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_sum_single [AddCommMonoid α] [Fintype m] [Fintype n] (x : m → n → α) :
    ∑ i : m, ∑ j : n, single i j (x i j) = of x := by
  ext i j
  rw [← Fintype.sum_prod_type']
  simp [single, Matrix.sum_apply, Matrix.of_apply, ← Prod.mk_inj]
/-
**Matrix.matrix_eq_sum_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：matrix_eq_sum_single [AddCommMonoid α] [Fintype m] [Fintype n] (x : Matrix
 m n α) : x = ∑ i : m, ∑ j : n, single i j (x i j)
参数：x : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.sum_sum_single`：sum_sum_single [AddCommMonoid α] [Fintype m] [Fin
type n] (x : m -> n -> α) : ∑ i : m, ∑ j : n, single i j (x i j) = of x
-/
theorem matrix_eq_sum_single [AddCommMonoid α] [Fintype m] [Fintype n] (x : Matrix m n α) :
    x = ∑ i : m, ∑ j : n, single i j (x i j) :=
  sum_sum_single _ |>.symm
/-
**Matrix.single_eq_single_vecMulVec_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_eq_single_vecMulVec_single [MulZeroOneClass α] (i : m) (j : n) : si
ngle i j (1 : α) = vecMulVec (Pi.single i 1) (Pi.single j 1)
参数：i : m；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_eq_single_vecMulVec_single [MulZeroOneClass α] (i : m) (j : n) :
    single i j (1 : α) = vecMulVec (Pi.single i 1) (Pi.single j 1) := by
  simp [-mul_ite, single, vecMulVec, ite_and, Pi.single_apply, eq_comm]

-- todo: the old proof used fintypes, I don't know `Finsupp` but this feels generalizable
@[elab_as_elim]
/-
**Matrix.induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type u_7} [inst : DecidableEq m] [ins
t_1 : DecidableEq n]   [inst_2 : AddCommMonoid α] [Finite m] [Finite n] {P : Mat
rix m n α → Prop} (M : Matrix m n α),   P 0 → (∀ (p q : Matrix m n α), P p → P q
 → P (p + q)) → (∀ (i : m) (j : n) (x : α), P (Matrix.single i j x)) → P M
参数：M : Matrix m n α；∀ (p q : Matrix m n α), P p → P q → P (p + q)；∀ (i : m) (j :
 n) (x : α), P (Matrix.single i j x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.matrix_eq_sum_single`：matrix_eq_sum_single [AddCommMonoid α] [Fin
type m] [Fintype n] (x : Matrix m n α) : x = ∑ i : m, ∑ j : n, single i j (x i j
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_product'`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [ins
t : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ → α → β),   ∑ x ∈ s ×ˢ
 t, f x.1…
· 使用定理 `Finset.sum_induction`：∀ {ι : Type u_1} {s : Finset ι} {M : Type u_7} [in
st : AddCommMonoid M] (f : ι → M) (p : M → Prop),   (∀ (a b : M), p a → p b → p 
(a + b)) →…
-/
protected theorem induction_on'
    [AddCommMonoid α] [Finite m] [Finite n] {P : Matrix m n α → Prop} (M : Matrix m n α)
    (h_zero : P 0) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ (i : m) (j : n) (x : α), P (single i j x)) : P M := by
  cases nonempty_fintype m; cases nonempty_fintype n
  rw [matrix_eq_sum_single M, ← Finset.sum_product']
  apply Finset.sum_induction _ _ h_add h_zero
  · intros
    apply h_std_basis

@[elab_as_elim]
/-
**Matrix.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type u_7} [inst : DecidableEq m] [ins
t_1 : DecidableEq n]   [inst_2 : AddCommMonoid α] [Finite m] [Finite n] [Nonempt
y m] [Nonempty n] {P : Matrix m n α → Prop}   (M : Matrix m n α),   (∀ (p q : Ma
trix m n α), P p → P q → P (p + q)) → (∀ (i : m) (j : n) (x : α), P (Matrix.sing
le i j x)) → P M
参数：M : Matrix m n α；∀ (p q : Matrix m n α), P p → P q → P (p + q)；∀ (i : m) (j :
 n) (x : α), P (Matrix.single i j x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.induction_on'`：∀ {m : Type u_2} {n : Type u_3} {α : Type u_7} [in
st : DecidableEq m] [inst_1 : DecidableEq n]   [inst_2 : AddCommMonoid α] [Finit
e m] [Fini…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_zero`：single_zero (i : m) (j : n) : single i j (0 : α) = 0
-/
protected theorem induction_on
    [AddCommMonoid α] [Finite m] [Finite n] [Nonempty m] [Nonempty n]
    {P : Matrix m n α → Prop} (M : Matrix m n α) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ i j x, P (single i j x)) : P M :=
  Matrix.induction_on' M
    (by
      inhabit m
      inhabit n
      simpa using h_std_basis default default 0)
    h_add h_std_basis

/-- `Matrix.single` as a bundled additive map. -/
@[simps]
/-
**Matrix.singleAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：singleAddMonoidHom [AddCommMonoid α] (i : m) (j : n) : α ->+ Matrix m n α 
where toFun
参数：i : m；j : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.single` as a bundled additive map.
-/
def singleAddMonoidHom [AddCommMonoid α] (i : m) (j : n) : α →+ Matrix m n α where
  toFun := single i j
  map_zero' := single_zero _ _
  map_add' _ _ := single_add _ _ _ _

variable (R)
/-- `Matrix.single` as a bundled linear map. -/
@[simps!]
/-
**Matrix.singleLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：singleLinearMap [Semiring R] [AddCommMonoid α] [Module R α] (i : m) (j : n
) : α ->ₗ[R] Matrix m n α where __
参数：i : m；j : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.single` as a bundled linear map.
-/
def singleLinearMap [Semiring R] [AddCommMonoid α] [Module R α] (i : m) (j : n) :
    α →ₗ[R] Matrix m n α where
  __ := singleAddMonoidHom i j
  map_smul' _ _ := smul_single _ _ _ _ |>.symm

section ext

/-- Additive maps from finite matrices are equal if they agree on the standard basis.

See note [partially-applied ext lemmas]. -/
@[local ext]
/-
**Matrix.ext_addMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ext_addMonoidHom [Finite m] [Finite n] [AddCommMonoid α] [AddCommMonoid β]
 ⦃f g : Matrix m n α ->+ β⦄ (h : forall i j, f.comp (singleAddMonoidHom i j) = g
.comp (singleAddMonoidHom i j)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.matrix_eq_sum_single`：matrix_eq_sum_single [AddCommMonoid α] [Fin
type m] [Fintype n] (x : Matrix m n α) : x = ∑ i : m, ∑ j : n, single i j (x i j
)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
Additive maps from finite matrices are equal if they agree on the standard basis
.

See note [partially-applied ext lemmas].
-/
theorem ext_addMonoidHom
    [Finite m] [Finite n] [AddCommMonoid α] [AddCommMonoid β] ⦃f g : Matrix m n α →+ β⦄
    (h : ∀ i j, f.comp (singleAddMonoidHom i j) = g.comp (singleAddMonoidHom i j)) :
    f = g := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  ext x
  rw [matrix_eq_sum_single x]
  simp_rw [map_sum]
  congr! 2
  exact DFunLike.congr_fun (h _ _) _

/-- Linear maps from finite matrices are equal if they agree on the standard basis.

See note [partially-applied ext lemmas]. -/
@[local ext]
/-
**Matrix.ext_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ext_linearMap [Finite m] [Finite n] [Semiring R] [AddCommMonoid α] [AddCom
mMonoid β] [Module R α] [Module R β] ⦃f g : Matrix m n α ->ₗ[R] β⦄ (h : forall i
 j, f ∘ₗ singleLinearMap R i j = g ∘ₗ singleLinearMap R i j) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toAddMonoidHom_injective`：toAddMonoidHom_injective : Function.
Injective (toAddMonoidHom : (M ->ₛₗ[σ] M₃) -> M ->+ M₃)
· 使用定理 `Matrix.ext_addMonoidHom`：ext_addMonoidHom [Finite m] [Finite n] [AddComm
Monoid α] [AddCommMonoid β] ⦃f g : Matrix m n α ->+ β⦄ (h : forall i j, f.comp (
singleAddMono…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Linear maps from finite matrices are equal if they agree on the standard basis.

See note [partially-applied ext lemmas].
-/
theorem ext_linearMap
    [Finite m] [Finite n] [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [Module R α] [Module R β]
    ⦃f g : Matrix m n α →ₗ[R] β⦄
    (h : ∀ i j, f ∘ₗ singleLinearMap R i j = g ∘ₗ singleLinearMap R i j) :
    f = g :=
  LinearMap.toAddMonoidHom_injective <| ext_addMonoidHom fun i j =>
    congrArg LinearMap.toAddMonoidHom <| h i j

section liftLinear
variable {R} (S)
variable [Fintype m] [Fintype n] [Semiring R] [Semiring S] [AddCommMonoid α] [AddCommMonoid β]
variable [Module R α] [Module R β] [Module S β] [SMulCommClass R S β]

/-- Families of linear maps acting on each element are equivalent to linear maps from a matrix.

This can be thought of as the matrix version of `LinearMap.lsum`. -/
/-
**Matrix.liftLinear** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：liftLinear : (m -> n -> α ->ₗ[R] β) ≃ₗ[S] (Matrix m n α ->ₗ[R] β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Families of linear maps acting on each element are equivalent to linear maps fro
m a matrix.

This can be thought of as the matrix version of `LinearMap.lsum`.
-/
def liftLinear : (m → n → α →ₗ[R] β) ≃ₗ[S] (Matrix m n α →ₗ[R] β) :=
  LinearEquiv.piCongrRight (fun _ => LinearMap.lsum R _ S) ≪≫ₗ LinearMap.lsum R _ S ≪≫ₗ
    LinearEquiv.congrLeft _ _ (ofLinearEquiv _)

-- not `simp` to let `liftLinear_single` fire instead
/-
**Matrix.liftLinear_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：liftLinear_apply (f : m -> n -> α ->ₗ[R] β) (M : Matrix m n α) : liftLinea
r S f M = ∑ i, ∑ j, f i j (M i j)
参数：f : m -> n -> α ->ₗ[R] β；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearEquiv.arrowCongrAddEquiv_apply`：∀ {R₁ : Type u_9} {R₂ : Type u_10}
 {R₁' : Type u_11} {R₂' : Type u_12} {M₁ : Type u_13} {M₂ : Type u_14}   {M₁' : 
Type u_15} {M₂' : Type u_1…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftLinear_apply (f : m → n → α →ₗ[R] β) (M : Matrix m n α) :
    liftLinear S f M = ∑ i, ∑ j, f i j (M i j) := by
  simp [liftLinear, map_sum, LinearEquiv.congrLeft]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Matrix.liftLinear_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：liftLinear_single (f : m -> n -> α ->ₗ[R] β) (i : m) (j : n) (a : α) : lif
tLinear S f (Matrix.single i j a) = f i j a
参数：f : m -> n -> α ->ₗ[R] β；i : m；j : n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.of_symm_single`：of_symm_single (i : m) (j : n) (a : α) : of.symm 
(single i j a) = Pi.single i (Pi.single j a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.lsum_piSingle`：lsum_piSingle (S) [AddCommMonoid M] [Module R M
] [Fintype ι] [Semiring S] [Module S M] [SMulCommClass R S M] (f : (i : ι) -> φ 
i ->ₗ[R] M) (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftLinear_single (f : m → n → α →ₗ[R] β) (i : m) (j : n) (a : α) :
    liftLinear S f (Matrix.single i j a) = f i j a := by
  dsimp [liftLinear, -LinearMap.lsum_apply, LinearEquiv.congrLeft, LinearEquiv.piCongrRight]
  simp_rw [of_symm_single, LinearMap.lsum_piSingle]

@[simp]
/-
**Matrix.liftLinear_comp_singleLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：liftLinear_comp_singleLinearMap (f : m -> n -> α ->ₗ[R] β) (i : m) (j : n)
 : liftLinear S f ∘ₗ Matrix.singleLinearMap _ i j = f i j
参数：f : m -> n -> α ->ₗ[R] β；i : m；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Matrix.liftLinear_single`：liftLinear_single (f : m -> n -> α ->ₗ[R] β) (
i : m) (j : n) (a : α) : liftLinear S f (Matrix.single i j a) = f i j a
-/
theorem liftLinear_comp_singleLinearMap (f : m → n → α →ₗ[R] β) (i : m) (j : n) :
    liftLinear S f ∘ₗ Matrix.singleLinearMap _ i j = f i j :=
  LinearMap.ext <| liftLinear_single S f i j

@[simp]
/-
**Matrix.liftLinear_singleLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：liftLinear_singleLinearMap [Module S α] [SMulCommClass R S α] : liftLinear
 S (Matrix.singleLinearMap R) = .id (M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext_linearMap`：ext_linearMap [Finite m] [Finite n] [Semiring R] [
AddCommMonoid α] [AddCommMonoid β] [Module R α] [Module R β] ⦃f g : Matrix m n α
 ->ₗ[R] β⦄…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.liftLinear_comp_singleLinearMap`：liftLinear_comp_singleLinearMap 
(f : m -> n -> α ->ₗ[R] β) (i : m) (j : n) : liftLinear S f ∘ₗ Matrix.singleLine
arMap _ i j = f i j
-/
theorem liftLinear_singleLinearMap [Module S α] [SMulCommClass R S α] :
    liftLinear S (Matrix.singleLinearMap R) = .id (M := Matrix m n α) :=
  ext_linearMap _ <| liftLinear_comp_singleLinearMap _ _

end liftLinear

end ext

section
variable [Zero α] (i j : n) (c : α)

-- This simp lemma should take priority over `diag_apply`
@[simp 1050]
/-
**Matrix.diag_single_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_single_of_ne (h : i != j) : diag (single i j c) = 0
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem diag_single_of_ne (h : i ≠ j) : diag (single i j c) = 0 :=
  funext fun _ => if_neg fun ⟨e₁, e₂⟩ => h (e₁.trans e₂.symm)

-- This simp lemma should take priority over `diag_apply`
@[simp 1050]
/-
**Matrix.diag_single_same** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_single_same : diag (single i i c) = Pi.single i c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
-/
theorem diag_single_same : diag (single i i c) = Pi.single i c := by
  ext j
  by_cases hij : i = j <;> (try rw [hij]) <;> simp [hij]

end

section mul
variable [Fintype m] [NonUnitalNonAssocSemiring α] (c : α)

omit [DecidableEq n] in
@[simp]
/-
**Matrix.single_mul_apply_same** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_mul_apply_same (i : l) (j : m) (b : n) (M : Matrix m n α) : (single
 i j c * M) i b = c * M j b
参数：i : l；j : m；b : n；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
theorem single_mul_apply_same (i : l) (j : m) (b : n) (M : Matrix m n α) :
    (single i j c * M) i b = c * M j b := by simp [mul_apply, single]

omit [DecidableEq l] in
@[simp]
/-
**Matrix.mul_single_apply_same** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_single_apply_same (i : m) (j : n) (a : l) (M : Matrix l m α) : (M * si
ngle i j c) a j = M a i * c
参数：i : m；j : n；a : l；M : Matrix l m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
theorem mul_single_apply_same (i : m) (j : n) (a : l) (M : Matrix l m α) :
    (M * single i j c) a j = M a i * c := by simp [mul_apply, single]

omit [DecidableEq n] in
@[simp]
/-
**Matrix.single_mul_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_mul_apply_of_ne (i : l) (j : m) (a : l) (b : n) (h : a != i) (M : M
atrix m n α) : (single i j c * M) a b = 0
参数：i : l；j : m；a : l；b : n；h : a != i；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_mul_apply_of_ne (i : l) (j : m) (a : l) (b : n) (h : a ≠ i) (M : Matrix m n α) :
    (single i j c * M) a b = 0 := by simp [mul_apply, h.symm]

omit [DecidableEq l] in
@[simp]
/-
**Matrix.mul_single_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_single_apply_of_ne (i : m) (j : n) (a : l) (b : n) (hbj : b != j) (M :
 Matrix l m α) : (M * single i j c) a b = 0
参数：i : m；j : n；a : l；b : n；hbj : b != j；M : Matrix l m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_single_apply_of_ne (i : m) (j : n) (a : l) (b : n) (hbj : b ≠ j) (M : Matrix l m α) :
    (M * single i j c) a b = 0 := by simp [mul_apply, hbj.symm]

@[simp]
/-
**Matrix.single_mul_single_same** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_mul_single_same (i : l) (j : m) (k : n) (d : α) : single i j c * si
ngle j k d = single i k (c * d)
参数：i : l；j : m；k : n；d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem single_mul_single_same (i : l) (j : m) (k : n) (d : α) :
    single i j c * single j k d = single i k (c * d) := by
  ext a b
  simp only [mul_apply, single]
  by_cases h₁ : i = a <;> by_cases h₂ : k = b <;> simp [h₁, h₂]

@[simp]
/-
**Matrix.single_mul_mul_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_mul_mul_single [Fintype n] (i : l) (i' : m) (j' : n) (j : o) (a : α
) (x : Matrix m n α) (b : α) : single i i' a * x * single j' j b = single i j (a
 * x i' j' * b)
参数：i : l；i' : m；j' : n；j : o；a : α；x : Matrix m n α；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem single_mul_mul_single [Fintype n]
    (i : l) (i' : m) (j' : n) (j : o) (a : α) (x : Matrix m n α) (b : α) :
    single i i' a * x * single j' j b = single i j (a * x i' j' * b) := by
  ext i'' j''
  simp only [mul_apply, single]
  by_cases h₁ : i = i'' <;> by_cases h₂ : j = j'' <;> simp [h₁, h₂]

@[simp]
/-
**Matrix.single_mul_single_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_mul_single_of_ne (i : l) (j k : m) {l : n} (h : j != k) (d : α) : s
ingle i j c * single k l d = 0
参数：i : l；j k : m；h : j != k；d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
-/
theorem single_mul_single_of_ne (i : l) (j k : m) {l : n} (h : j ≠ k) (d : α) :
    single i j c * single k l d = 0 := by
  ext a b
  simp only [mul_apply, single, of_apply]
  by_cases h₁ : i = a
  · simp [h₁, h, Finset.sum_eq_zero]
  · simp [h₁]

end mul

section Commute

variable [Fintype n] [Semiring α]

/-
**Matrix.row_eq_zero_of_commute_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：row_eq_zero_of_commute_single {i j k : n} {M : Matrix n n α} (hM : Commute
 (single i j 1) M) (hkj : k != j) : M j k = 0
参数：hM : Commute (single i j 1) M；hkj : k != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.single_mul_apply_same`：single_mul_apply_same (i : l) (j : m) (b :
 n) (M : Matrix m n α) : (single i j c * M) i b = c * M j b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.mul_single_apply_of_ne`：mul_single_apply_of_ne (i : m) (j : n) (a
 : l) (b : n) (hbj : b != j) (M : Matrix l m α) : (M * single i j c) a b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem row_eq_zero_of_commute_single {i j k : n} {M : Matrix n n α}
    (hM : Commute (single i j 1) M) (hkj : k ≠ j) : M j k = 0 := by
  have := ext_iff.mpr hM i k
  simp_all
/-
**Matrix.col_eq_zero_of_commute_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：col_eq_zero_of_commute_single {i j k : n} {M : Matrix n n α} (hM : Commute
 (single i j 1) M) (hki : k != i) : M k i = 0
参数：hM : Commute (single i j 1) M；hki : k != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.single_mul_apply_of_ne`：single_mul_apply_of_ne (i : l) (j : m) (a
 : l) (b : n) (h : a != i) (M : Matrix m n α) : (single i j c * M) a b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.mul_single_apply_same`：mul_single_apply_same (i : m) (j : n) (a :
 l) (M : Matrix l m α) : (M * single i j c) a j = M a i * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem col_eq_zero_of_commute_single {i j k : n} {M : Matrix n n α}
    (hM : Commute (single i j 1) M) (hki : k ≠ i) : M k i = 0 := by
  have := ext_iff.mpr hM k j
  simp_all
/-
**Matrix.diag_eq_of_commute_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_eq_of_commute_single {i j : n} {M : Matrix n n α} (hM : Commute (sing
le i j 1) M) : M i i = M j j
参数：hM : Commute (single i j 1) M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.single_mul_apply_same`：single_mul_apply_same (i : l) (j : m) (b :
 n) (M : Matrix m n α) : (single i j c * M) i b = c * M j b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.mul_single_apply_same`：mul_single_apply_same (i : m) (j : n) (a :
 l) (M : Matrix l m α) : (M * single i j c) a j = M a i * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diag_eq_of_commute_single {i j : n} {M : Matrix n n α}
    (hM : Commute (single i j 1) M) : M i i = M j j := by
  have := ext_iff.mpr hM i j
  simp_all

/-- `M` is a scalar matrix if it commutes with every non-diagonal `single`. -/
/-
**Matrix.mem_range_scalar_of_commute_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_range_scalar_of_commute_single {M : Matrix n n α} (hM : Pairwise fun i
 j => Commute (single i j 1) M) : M in Set.range (Matrix.scalar n)
参数：hM : Pairwise fun i j => Commute (single i j 1) M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diag_eq_of_commute_single`：diag_eq_of_commute_single {i j : n} {M
 : Matrix n n α} (hM : Commute (single i j 1) M) : M i i = M j j
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Matrix.col_eq_zero_of_commute_single`：col_eq_zero_of_commute_single {i j
 k : n} {M : Matrix n n α} (hM : Commute (single i j 1) M) (hki : k != i) : M k 
i = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Matrix.row_eq_zero_of_commute_single`：row_eq_zero_of_commute_single {i j
 k : n} {M : Matrix n n α} (hM : Commute (single i j 1) M) (hkj : k != j) : M j 
k = 0

--- 原说明 ---
`M` is a scalar matrix if it commutes with every non-diagonal `single`.
-/
theorem mem_range_scalar_of_commute_single {M : Matrix n n α}
    (hM : Pairwise fun i j => Commute (single i j 1) M) :
    M ∈ Set.range (Matrix.scalar n) := by
  cases isEmpty_or_nonempty n
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨M i i, Matrix.ext fun j k => ?_⟩
  simp only [scalar_apply]
  obtain rfl | hkl := Decidable.eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rfl
    · exact diag_eq_of_commute_single (hM hij)
  · rw [diagonal_apply_ne _ hkl]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [col_eq_zero_of_commute_single (hM hkl.symm) hkl]
    · rw [row_eq_zero_of_commute_single (hM hij) hkl.symm]
/-
**Matrix.mem_range_scalar_iff_commute_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_range_scalar_iff_commute_single {M : Matrix n n α} : M in Set.range (M
atrix.scalar n) ↔ forall (i j : n), i != j -> Commute (single i j 1) M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.scalar_commute_iff`：scalar_commute_iff {r : α} {M : Matrix n n α}
 : Commute (scalar n r) M ↔ r • M = MulOpposite.op r • M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.smul_single`：smul_single [SMulZeroClass R α] (r : R) (i : m) (j :
 n) (a : α) : r • single i j a = single i j (r • a)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.mem_range_scalar_of_commute_single`：mem_range_scalar_of_commute_s
ingle {M : Matrix n n α} (hM : Pairwise fun i j => Commute (single i j 1) M) : M
 in Set.range (Matrix.scalar n)
-/
theorem mem_range_scalar_iff_commute_single {M : Matrix n n α} :
    M ∈ Set.range (Matrix.scalar n) ↔ ∀ (i j : n), i ≠ j → Commute (single i j 1) M := by
  refine ⟨fun ⟨r, hr⟩ i j _ => hr ▸ Commute.symm ?_, mem_range_scalar_of_commute_single⟩
  rw [scalar_commute_iff]
  simp

/-- `M` is a scalar matrix if and only if it commutes with every `single`. -/
/-
**Matrix.mem_range_scalar_iff_commute_single'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：mem_range_scalar_iff_commute_single' {M : Matrix n n α} : M in Set.range (
Matrix.scalar n) ↔ forall (i j : n), Commute (single i j 1) M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.scalar_commute_iff`：scalar_commute_iff {r : α} {M : Matrix n n α}
 : Commute (scalar n r) M ↔ r • M = MulOpposite.op r • M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.smul_single`：smul_single [SMulZeroClass R α] (r : R) (i : m) (j :
 n) (a : α) : r • single i j a = single i j (r • a)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.mem_range_scalar_iff_commute_single`：mem_range_scalar_iff_commute
_single {M : Matrix n n α} : M in Set.range (Matrix.scalar n) ↔ forall (i j : n)
, i != j -> Commute (single i j …

--- 原说明 ---
`M` is a scalar matrix if and only if it commutes with every `single`.
-/
theorem mem_range_scalar_iff_commute_single' {M : Matrix n n α} :
    M ∈ Set.range (Matrix.scalar n) ↔ ∀ (i j : n), Commute (single i j 1) M := by
  refine ⟨fun ⟨r, hr⟩ i j => hr ▸ Commute.symm ?_,
    fun hM => mem_range_scalar_iff_commute_single.mpr <| fun i j _ => hM i j⟩
  rw [scalar_commute_iff]
  simp

/-- The center of `Matrix n n α` is equal to the image of the center of `α` under `scalar n`. -/
/-
**Matrix.center_eq_scalar_image** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：center_eq_scalar_image : Set.center (Matrix n n α) = scalar n '' Set.cente
r α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Matrix.diagonal_zero`：diagonal_zero [Zero α] : (diagonal fun _ => 0 : Ma
trix n n α) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.mem_range_scalar_iff_commute_single'`：mem_range_scalar_iff_commut
e_single' {M : Matrix n n α} : M in Set.range (Matrix.scalar n) ↔ forall (i j : 
n), Commute (single i j 1) M
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
· 使用定理 `Matrix.mul_single_apply_same`：mul_single_apply_same (i : m) (j : n) (a :
 l) (M : Matrix l m α) : (M * single i j c) a j = M a i * c
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Matrix.scalar_commute`：scalar_commute (r : α) (hr : forall r', Commute r
 r') (M : Matrix n n α) : Commute (scalar n r) M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The center of `Matrix n n α` is equal to the image of the center of `α` under `s
calar n`.
-/
theorem center_eq_scalar_image :
    Set.center (Matrix n n α) = scalar n '' Set.center α := Set.ext fun x ↦ by
  simp_rw [Set.mem_image, Semigroup.mem_center_iff]
  refine ⟨fun hx ↦ ?_, fun ⟨x, hx, eq⟩ y ↦ eq ▸ scalar_commute x (hx · |>.symm) y |>.symm⟩
  refine (isEmpty_or_nonempty n).elim (fun _ ↦ ⟨0, by simp [nontriviality]⟩) fun ⟨i⟩ ↦ ?_
  obtain ⟨x, rfl⟩ := mem_range_scalar_iff_commute_single'.mpr fun _ _ ↦ hx _
  exact ⟨x, by simpa using fun r ↦ congr($(hx (single i i r)) i i)⟩
/-
**Matrix.submonoidCenter_eq_scalar_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submonoidCenter_eq_scalar_map : Submonoid.center (Matrix n n α) = (Submono
id.center α).map (scalar n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Matrix.center_eq_scalar_image`：center_eq_scalar_image : Set.center (Matr
ix n n α) = scalar n '' Set.center α
-/
theorem submonoidCenter_eq_scalar_map :
    Submonoid.center (Matrix n n α) = (Submonoid.center α).map (scalar n) :=
  SetLike.coe_injective center_eq_scalar_image
/-
**Matrix.subsemigroupCenter_eq_scalar_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：subsemigroupCenter_eq_scalar_map : Subsemigroup.center (Matrix n n α) = (S
ubsemigroup.center α).map (scalar n).toMulHom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Matrix.center_eq_scalar_image`：center_eq_scalar_image : Set.center (Matr
ix n n α) = scalar n '' Set.center α
-/
theorem subsemigroupCenter_eq_scalar_map :
    Subsemigroup.center (Matrix n n α) = (Subsemigroup.center α).map (scalar n).toMulHom :=
  SetLike.coe_injective center_eq_scalar_image
/-
**Matrix.subsemiringCenter_eq_scalar_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：subsemiringCenter_eq_scalar_map : Subsemiring.center (Matrix n n α) = (Sub
semiring.center α).map (scalar n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Matrix.center_eq_scalar_image`：center_eq_scalar_image : Set.center (Matr
ix n n α) = scalar n '' Set.center α
-/
theorem subsemiringCenter_eq_scalar_map :
    Subsemiring.center (Matrix n n α) = (Subsemiring.center α).map (scalar n) :=
  SetLike.coe_injective center_eq_scalar_image
/-
**Matrix.subringCenter_eq_scalar_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：subringCenter_eq_scalar_map [Ring R] : Subring.center (Matrix n n R) = (Su
bring.center R).map (scalar n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Matrix.center_eq_scalar_image`：center_eq_scalar_image : Set.center (Matr
ix n n α) = scalar n '' Set.center α
-/
theorem subringCenter_eq_scalar_map [Ring R] :
    Subring.center (Matrix n n R) = (Subring.center R).map (scalar n) :=
  SetLike.coe_injective center_eq_scalar_image

/-- For a commutative semiring `R`, the center of `Matrix n n R` is the range of `scalar n`
(i.e., the span of `{1}`). -/
/-
**Matrix.center_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} (R : Type u_5) [inst : DecidableEq n] [inst_1 : Fintype n
] [inst_2 : CommSemiring R],   Set.center (Matrix n n R) = Set.range ⇑(Matrix.sc
alar n)
参数：R : Type u_5；Matrix n n R；Matrix.scalar n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.center_eq_scalar_image`：center_eq_scalar_image : Set.center (Matr
ix n n α) = scalar n '' Set.center α
· 使用定理 `Set.center_eq_univ`：center_eq_univ : center M = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f

--- 原说明 ---
For a commutative semiring `R`, the center of `Matrix n n R` is the range of `sc
alar n`
(i.e., the span of `{1}`).
-/
@[simp] theorem center_eq_range [CommSemiring R] :
    Set.center (Matrix n n R) = Set.range (scalar n) := by
  rw [center_eq_scalar_image, Set.center_eq_univ, Set.image_univ]

end Commute

end Matrix

