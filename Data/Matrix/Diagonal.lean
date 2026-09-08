/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
module

public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Embedding.Basic

/-!
# Diagonal matrices

This file defines diagonal matrices and the `AddCommMonoidWithOne` structure on matrices.

## Main definitions

* `Matrix.diagonal d`: matrix with the vector `d` along the diagonal
* `Matrix.diag M`: the diagonal of a square matrix
* `Matrix.instAddCommMonoidWithOne`: matrices are an additive commutative monoid with one
-/

@[expose] public section

assert_not_exists Algebra TrivialStar

universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix

section Diagonal

variable [DecidableEq n]

/-- `diagonal d` is the square matrix such that `(diagonal d) i i = d i` and `(diagonal d) i j = 0`
if `i ≠ j`.

Note that bundled versions exist as:
* `Matrix.diagonalAddMonoidHom`
* `Matrix.diagonalLinearMap`
* `Matrix.diagonalRingHom`
* `Matrix.diagonalAlgHom`
-/
/-
**Matrix.diagonal** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：diagonal [Zero α] (d : n -> α) : Matrix n n α
参数：d : n -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`diagonal d` is the square matrix such that `(diagonal d) i i = d i` and `(diago
nal d) i j = 0`
if `i ≠ j`.

Note that bundled versions exist as:
* `Matrix.diagonalAddMonoidHom`
* `Matrix.diagonalLinearMap`
* `Matrix.diagonalRingHom`
* `Matrix.diagonalAlgHom`
-/
def diagonal [Zero α] (d : n → α) : Matrix n n α :=
  of fun i j => if i = j then d i else 0

-- TODO: set as an equation lemma for `diagonal`, see https://github.com/leanprover-community/mathlib4/pull/3024
/-
**Matrix.diagonal_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_apply [Zero α] (d : n -> α) (i j) : diagonal d i j = if i = j the
n d i else 0
参数：d : n -> α；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagonal_apply [Zero α] (d : n → α) (i j) : diagonal d i j = if i = j then d i else 0 :=
  rfl

@[simp]
/-
**Matrix.diagonal_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_apply_eq [Zero α] (d : n -> α) (i : n) : (diagonal d) i i = d i
参数：d : n -> α；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonal_apply_eq [Zero α] (d : n → α) (i : n) : (diagonal d) i i = d i := by
  simp [diagonal]

@[simp]
/-
**Matrix.diagonal_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_apply_ne [Zero α] (d : n -> α) {i j : n} (h : i != j) : (diagonal
 d) i j = 0
参数：d : n -> α；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonal_apply_ne [Zero α] (d : n → α) {i j : n} (h : i ≠ j) : (diagonal d) i j = 0 := by
  simp [diagonal, h]
/-
**Matrix.diagonal_apply_ne'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_apply_ne' [Zero α] (d : n -> α) {i j : n} (h : j != i) : (diagona
l d) i j = 0
参数：d : n -> α；h : j != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem diagonal_apply_ne' [Zero α] (d : n → α) {i j : n} (h : j ≠ i) : (diagonal d) i j = 0 :=
  diagonal_apply_ne d h.symm

@[simp]
/-
**Matrix.diagonal_eq_diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_eq_diagonal_iff [Zero α] {d₁ d₂ : n -> α} : diagonal d₁ = diagona
l d₂ ↔ forall i, d₁ i = d₂ i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem diagonal_eq_diagonal_iff [Zero α] {d₁ d₂ : n → α} :
    diagonal d₁ = diagonal d₂ ↔ ∀ i, d₁ i = d₂ i :=
  ⟨fun h i => by simpa using congr_arg (fun m : Matrix n n α => m i i) h, fun h => by
    rw [show d₁ = d₂ from funext h]⟩
/-
**Matrix.diagonal_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_injective [Zero α] : Function.Injective (diagonal : (n -> α) -> M
atrix n n α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
-/
theorem diagonal_injective [Zero α] : Function.Injective (diagonal : (n → α) → Matrix n n α) :=
  fun d₁ d₂ h => funext fun i => by simpa using Matrix.ext_iff.mpr h i i

@[simp]
/-
**Matrix.diagonal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_zero [Zero α] : (diagonal fun _ => 0 : Matrix n n α) = 0
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
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonal_zero [Zero α] : (diagonal fun _ => 0 : Matrix n n α) = 0 := by
  ext
  simp [diagonal]

@[simp]
/-
**Matrix.diagonal_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_zero' [Zero α] : (diagonal 0 : Matrix n n α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_zero`：diagonal_zero [Zero α] : (diagonal fun _ => 0 : Ma
trix n n α) = 0
-/
theorem diagonal_zero' [Zero α] : (diagonal 0 : Matrix n n α) = 0 := diagonal_zero

@[simp]
/-
**Matrix.diagonal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_eq_zero [Zero α] {d : n -> α} : diagonal d = 0 ↔ d = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Matrix.diagonal_injective`：diagonal_injective [Zero α] : Function.Inject
ive (diagonal : (n -> α) -> Matrix n n α)
· 使用定理 `Matrix.diagonal_zero`：diagonal_zero [Zero α] : (diagonal fun _ => 0 : Ma
trix n n α) = 0
-/
theorem diagonal_eq_zero [Zero α] {d : n → α} : diagonal d = 0 ↔ d = 0 :=
  diagonal_injective.eq_iff' diagonal_zero

@[simp]
/-
**Matrix.diagonal_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_transpose [Zero α] (v : n -> α) : (diagonal v)ᵀ = diagonal v
参数：v : n -> α。
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
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem diagonal_transpose [Zero α] (v : n → α) : (diagonal v)ᵀ = diagonal v := by
  ext i j
  by_cases h : i = j <;> simp [h, transpose, eqComm]

@[simp]
/-
**Matrix.diagonal_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_add [AddZeroClass α] (d₁ d₂ : n -> α) : diagonal d₁ + diagonal d₂
 = diagonal fun i => d₁ i + d₂ i
参数：d₁ d₂ : n -> α。
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
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem diagonal_add [AddZeroClass α] (d₁ d₂ : n → α) :
    diagonal d₁ + diagonal d₂ = diagonal fun i => d₁ i + d₂ i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]
/-
**Matrix.diagonal_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_smul [Zero α] [SMulZeroClass R α] (r : R) (d : n -> α) : diagonal
 (r • d) = r • diagonal d
参数：r : R；d : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem diagonal_smul [Zero α] [SMulZeroClass R α] (r : R) (d : n → α) :
    diagonal (r • d) = r • diagonal d := by
  ext i j
  by_cases h : i = j <;> simp [h]

@[simp]
/-
**Matrix.diagonal_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_neg [NegZeroClass α] (d : n -> α) : -diagonal d = diagonal fun i 
=> -d i
参数：d : n -> α。
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
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem diagonal_neg [NegZeroClass α] (d : n → α) :
    -diagonal d = diagonal fun i => -d i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]
/-
**Matrix.diagonal_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_sub [SubNegZeroMonoid α] (d₁ d₂ : n -> α) : diagonal d₁ - diagona
l d₂ = diagonal fun i => d₁ i - d₂ i
参数：d₁ d₂ : n -> α。
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
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem diagonal_sub [SubNegZeroMonoid α] (d₁ d₂ : n → α) :
    diagonal d₁ - diagonal d₂ = diagonal fun i => d₁ i - d₂ i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]
/-
**Matrix.diagonal_mem_matrix_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_mem_matrix_iff [Zero α] {S : Set α} (hS : 0 in S) {d : n -> α} : 
Matrix.diagonal d in S.matrix ↔ forall i, d i in S
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem diagonal_mem_matrix_iff [Zero α] {S : Set α} (hS : 0 ∈ S) {d : n → α} :
    Matrix.diagonal d ∈ S.matrix ↔ ∀ i, d i ∈ S := by
  simp only [Set.mem_matrix, diagonal, of_apply]
  conv_lhs => intro _ _; rw [ite_mem]
  simp [hS]
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero α] [NatCast α] : NatCast (Matrix n n α) where
  natCast m := diagonal fun _ => m

@[norm_cast]
/-
**Matrix.diagonal_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_natCast [Zero α] [NatCast α] (m : Nat) : diagonal (fun _ : n => (
m : α)) = m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagonal_natCast [Zero α] [NatCast α] (m : ℕ) : diagonal (fun _ : n => (m : α)) = m := rfl

@[norm_cast]
/-
**Matrix.diagonal_natCast'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_natCast' [Zero α] [NatCast α] (m : Nat) : diagonal ((m : n -> α))
 = m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagonal_natCast' [Zero α] [NatCast α] (m : ℕ) : diagonal ((m : n → α)) = m := rfl

@[simp]
/-
**Matrix.diagonal_eq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_eq_natCast [Zero α] [NatCast α] {d : n -> α} {m : Nat} : diagonal
 d = m ↔ d = m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Matrix.diagonal_injective`：diagonal_injective [Zero α] : Function.Inject
ive (diagonal : (n -> α) -> Matrix n n α)
· 使用定理 `Matrix.diagonal_natCast'`：diagonal_natCast' [Zero α] [NatCast α] (m : Na
t) : diagonal ((m : n -> α)) = m
-/
theorem diagonal_eq_natCast [Zero α] [NatCast α] {d : n → α} {m : ℕ} :
    diagonal d = m ↔ d = m :=
  diagonal_injective.eq_iff' <| diagonal_natCast' _
/-
**Matrix.diagonal_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_ofNat [Zero α] [NatCast α] (m : Nat) [m.AtLeastTwo] : diagonal (f
un _ : n => (ofNat(m) : α)) = ofNat(m)
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagonal_ofNat [Zero α] [NatCast α] (m : ℕ) [m.AtLeastTwo] :
    diagonal (fun _ : n => (ofNat(m) : α)) = ofNat(m) := rfl
/-
**Matrix.diagonal_ofNat'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_ofNat' [Zero α] [NatCast α] (m : Nat) [m.AtLeastTwo] : diagonal (
ofNat(m) : n -> α) = ofNat(m)
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagonal_ofNat' [Zero α] [NatCast α] (m : ℕ) [m.AtLeastTwo] :
    diagonal (ofNat(m) : n → α) = ofNat(m) := rfl

@[simp]
/-
**Matrix.diagonal_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_eq_ofNat [Zero α] [NatCast α] {d : n -> α} {m : Nat} [m.AtLeastTw
o] : diagonal d = ofNat(m) ↔ d = ofNat(m)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Matrix.diagonal_injective`：diagonal_injective [Zero α] : Function.Inject
ive (diagonal : (n -> α) -> Matrix n n α)
· 使用定理 `Matrix.diagonal_ofNat'`：diagonal_ofNat' [Zero α] [NatCast α] (m : Nat) [
m.AtLeastTwo] : diagonal (ofNat(m) : n -> α) = ofNat(m)
-/
theorem diagonal_eq_ofNat [Zero α] [NatCast α] {d : n → α} {m : ℕ} [m.AtLeastTwo] :
    diagonal d = ofNat(m) ↔ d = ofNat(m) :=
  diagonal_injective.eq_iff' <| diagonal_ofNat' _
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero α] [IntCast α] : IntCast (Matrix n n α) where
  intCast m := diagonal fun _ => m

@[norm_cast]
/-
**Matrix.diagonal_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_intCast [Zero α] [IntCast α] (m : Int) : diagonal (fun _ : n => (
m : α)) = m
参数：m : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagonal_intCast [Zero α] [IntCast α] (m : ℤ) : diagonal (fun _ : n => (m : α)) = m := rfl

@[norm_cast]
/-
**Matrix.diagonal_intCast'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_intCast' [Zero α] [IntCast α] (m : Int) : diagonal ((m : n -> α))
 = m
参数：m : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagonal_intCast' [Zero α] [IntCast α] (m : ℤ) : diagonal ((m : n → α)) = m := rfl

@[simp]
/-
**Matrix.diagonal_eq_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_eq_intCast [Zero α] [IntCast α] {d : n -> α} {m : Int} : diagonal
 d = m ↔ d = m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Matrix.diagonal_injective`：diagonal_injective [Zero α] : Function.Inject
ive (diagonal : (n -> α) -> Matrix n n α)
· 使用定理 `Matrix.diagonal_intCast'`：diagonal_intCast' [Zero α] [IntCast α] (m : In
t) : diagonal ((m : n -> α)) = m
-/
theorem diagonal_eq_intCast [Zero α] [IntCast α] {d : n → α} {m : ℤ} :
    diagonal d = m ↔ d = m :=
  diagonal_injective.eq_iff' <| diagonal_intCast' _

@[simp]
/-
**Matrix.diagonal_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 0 = 0) {d : n -> α} : (
diagonal d).map f = diagonal fun m => f (d m)
参数：h : f 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem diagonal_map [Zero α] [Zero β] {f : α → β} (h : f 0 = 0) {d : n → α} :
    (diagonal d).map f = diagonal fun m => f (d m) := by
  ext
  simp only [diagonal_apply, map_apply]
  split_ifs <;> simp [h]
/-
**Matrix.map_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : DecidableEq n] [inst_1 
: AddMonoidWithOne α] [inst_2 : Zero β]   {f : α → β}, f 0 = 0 → ∀ (d : ℕ), (↑d)
.map f = Matrix.diagonal fun x => f ↑d
参数：d : ℕ；↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
-/
protected theorem map_natCast [AddMonoidWithOne α] [Zero β]
    {f : α → β} (h : f 0 = 0) (d : ℕ) :
    (d : Matrix n n α).map f = diagonal (fun _ => f d) :=
  diagonal_map h
/-
**Matrix.map_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : DecidableEq n] [inst_1 
: AddMonoidWithOne α] [inst_2 : Zero β]   {f : α → β},   f 0 = 0 → ∀ (d : ℕ) [in
st_3 : d.AtLeastTwo], (OfNat.ofNat d).map f = Matrix.diagonal fun x => f (OfNat.
ofNat d)
参数：d : ℕ；OfNat.ofNat d；OfNat.ofNat d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
-/
protected theorem map_ofNat [AddMonoidWithOne α] [Zero β]
    {f : α → β} (h : f 0 = 0) (d : ℕ) [d.AtLeastTwo] :
    (ofNat(d) : Matrix n n α).map f = diagonal (fun _ => f (OfNat.ofNat d)) :=
  diagonal_map h
/-
**Matrix.natCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：natCast_apply [AddMonoidWithOne α] {i j} {d : Nat} : (d : Matrix n n α) i 
j = if i = j then d else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_ite`：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m 
n : Nat) : R) = ite P (m : R) (n : R)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_natCast`：diagonal_natCast [Zero α] [NatCast α] (m : Nat)
 : diagonal (fun _ : n => (m : α)) = m
· 使用定理 `Matrix.diagonal_apply`：diagonal_apply [Zero α] (d : n -> α) (i j) : diag
onal d i j = if i = j then d i else 0
-/
theorem natCast_apply [AddMonoidWithOne α] {i j} {d : ℕ} :
    (d : Matrix n n α) i j = if i = j then d else 0 := by
  rw [Nat.cast_ite, Nat.cast_zero, ← diagonal_natCast, diagonal_apply]
/-
**Matrix.ofNat_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ofNat_apply [AddMonoidWithOne α] {i j} {d : Nat} [d.AtLeastTwo] : (ofNat(d
) : Matrix n n α) i j = if i = j then d else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.natCast_apply`：natCast_apply [AddMonoidWithOne α] {i j} {d : Nat}
 : (d : Matrix n n α) i j = if i = j then d else 0
-/
theorem ofNat_apply [AddMonoidWithOne α] {i j} {d : ℕ} [d.AtLeastTwo] :
    (ofNat(d) : Matrix n n α) i j = if i = j then d else 0 :=
  natCast_apply
/-
**Matrix.map_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : DecidableEq n] [inst_1 
: AddGroupWithOne α] [inst_2 : Zero β]   {f : α → β}, f 0 = 0 → ∀ (d : ℤ), (↑d).
map f = Matrix.diagonal fun x => f ↑d
参数：d : ℤ；↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
-/
protected theorem map_intCast [AddGroupWithOne α] [Zero β]
    {f : α → β} (h : f 0 = 0) (d : ℤ) :
    (d : Matrix n n α).map f = diagonal (fun _ => f d) :=
  diagonal_map h
/-
**Matrix.intCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：intCast_apply [AddGroupWithOne α] {i j} {d : Int} : (d : Matrix n n α) i j
 = if i = j then d else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_ite`：cast_ite [IntCast R] (P : Prop) [Decidable P] (m n : Int) 
: ((ite P m n : Int) : R) = ite P (m : R) (n : R)
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_intCast`：diagonal_intCast [Zero α] [IntCast α] (m : Int)
 : diagonal (fun _ : n => (m : α)) = m
· 使用定理 `Matrix.diagonal_apply`：diagonal_apply [Zero α] (d : n -> α) (i j) : diag
onal d i j = if i = j then d i else 0
-/
theorem intCast_apply [AddGroupWithOne α] {i j} {d : ℤ} :
    (d : Matrix n n α) i j = if i = j then d else 0 := by
  rw [Int.cast_ite, Int.cast_zero, ← diagonal_intCast, diagonal_apply]
/-
**Matrix.diagonal_unique** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_unique [Unique m] [DecidableEq m] [Zero α] (d : m -> α) : diagona
l d = of fun _ _ => d default
参数：d : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
-/
theorem diagonal_unique [Unique m] [DecidableEq m] [Zero α] (d : m → α) :
    diagonal d = of fun _ _ => d default := by
  ext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default, diagonal_apply_eq _ _, of_apply]

@[simp]
/-
**Matrix.col_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：col_diagonal [Zero α] (d : n -> α) (i) : (diagonal d).col i = Pi.single i 
(d i)
参数：d : n -> α；i。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem col_diagonal [Zero α] (d : n → α) (i) : (diagonal d).col i = Pi.single i (d i) := by
  ext
  simp +contextual [diagonal, Pi.single_apply]

@[simp]
/-
**Matrix.row_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：row_diagonal [Zero α] (d : n -> α) (j) : (diagonal d).row j = Pi.single j 
(d j)
参数：d : n -> α；j。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem row_diagonal [Zero α] (d : n → α) (j) : (diagonal d).row j = Pi.single j (d j) := by
  ext
  simp +contextual [diagonal, eq_comm, Pi.single_apply]

section One

variable [Zero α] [One α]

/-
**Matrix.one** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：one : One (Matrix n n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance one : One (Matrix n n α) :=
  ⟨diagonal fun _ => 1⟩

@[simp]
/-
**Matrix.diagonal_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_one : (diagonal fun _ => 1 : Matrix n n α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagonal_one : (diagonal fun _ => 1 : Matrix n n α) = 1 :=
  rfl

@[simp]
/-
**Matrix.diagonal_one'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_one' : (diagonal 1 : Matrix n n α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagonal_one' : (diagonal 1 : Matrix n n α) = 1 :=
  rfl

@[simp]
/-
**Matrix.diagonal_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_eq_one {d : n -> α} : diagonal d = 1 ↔ d = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Matrix.diagonal_injective`：diagonal_injective [Zero α] : Function.Inject
ive (diagonal : (n -> α) -> Matrix n n α)
· 使用定理 `Matrix.diagonal_one`：diagonal_one : (diagonal fun _ => 1 : Matrix n n α)
 = 1
-/
theorem diagonal_eq_one {d : n → α} : diagonal d = 1 ↔ d = 1 :=
  diagonal_injective.eq_iff' diagonal_one
/-
**Matrix.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_apply {i j} : (1 : Matrix n n α) i j = if i = j then 1 else 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply {i j} : (1 : Matrix n n α) i j = if i = j then 1 else 0 :=
  rfl

@[simp]
/-
**Matrix.one_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
-/
theorem one_apply_eq (i) : (1 : Matrix n n α) i i = 1 :=
  diagonal_apply_eq _ i

@[simp]
/-
**Matrix.one_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i j = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
-/
theorem one_apply_ne {i j} : i ≠ j → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne _
/-
**Matrix.one_apply_ne'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_apply_ne' {i j} : j != i -> (1 : Matrix n n α) i j = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_apply_ne'`：diagonal_apply_ne' [Zero α] (d : n -> α) {i j
 : n} (h : j != i) : (diagonal d) i j = 0
-/
theorem one_apply_ne' {i j} : j ≠ i → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne' _

@[simp]
/-
**Matrix.map_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : DecidableEq n] [inst_1 
: Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β] (f : α → β), f 0
 = 0 → f 1 = 1 → Matrix.map 1 f = 1
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
protected theorem map_one [Zero β] [One β] (f : α → β) (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
    (1 : Matrix n n α).map f = (1 : Matrix n n β) := by
  ext
  simp only [one_apply, map_apply]
  split_ifs <;> simp [h₀, h₁]
/-
**Matrix.one_eq_pi_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_eq_pi_single {i j} : (1 : Matrix n n α) i j = Pi.single (M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_eq_pi_single {i j} : (1 : Matrix n n α) i j = Pi.single (M := fun _ => α) i 1 j := by
  simp only [one_apply, Pi.single_apply, eq_comm]

end One

/-
**Matrix.instAddMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：instAddMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (Matrix n n α
) where natCast_zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (Matrix n n α) where
  natCast_zero := show diagonal _ = _ by
    rw [Nat.cast_zero, diagonal_zero]
  natCast_succ n := show diagonal _ = diagonal _ + _ by
    rw [Nat.cast_succ, ← diagonal_add, diagonal_one]
/-
**Matrix.instAddGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：instAddGroupWithOne [AddGroupWithOne α] : AddGroupWithOne (Matrix n n α) w
here intCast_ofNat n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddGroupWithOne [AddGroupWithOne α] : AddGroupWithOne (Matrix n n α) where
  intCast_ofNat n := show diagonal _ = diagonal _ by
    rw [Int.cast_natCast]
  intCast_negSucc n := show diagonal _ = -(diagonal _) by
    rw [Int.cast_negSucc, diagonal_neg]
  __ := addGroup
  __ := instAddMonoidWithOne
/-
**Matrix.instAddCommMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：instAddCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (
Matrix n n α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoidWithOne [AddCommMonoidWithOne α] :
    AddCommMonoidWithOne (Matrix n n α) where
  __ := addCommMonoid
  __ := instAddMonoidWithOne
/-
**Matrix.instAddCommGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：instAddCommGroupWithOne [AddCommGroupWithOne α] : AddCommGroupWithOne (Mat
rix n n α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroupWithOne [AddCommGroupWithOne α] :
    AddCommGroupWithOne (Matrix n n α) where
  __ := addCommGroup
  __ := instAddGroupWithOne

end Diagonal

section Diag

/-- The diagonal of a square matrix. -/
/-
**Matrix.diag** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：diag (A : Matrix n n α) (i : n) : α
参数：A : Matrix n n α；i : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal of a square matrix.
-/
def diag (A : Matrix n n α) (i : n) : α :=
  A i i

@[simp]
/-
**Matrix.diag_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_apply (A : Matrix n n α) (i) : diag A i = A i i
参数：A : Matrix n n α；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_apply (A : Matrix n n α) (i) : diag A i = A i i :=
  rfl

@[simp]
/-
**Matrix.diag_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_diagonal [DecidableEq n] [Zero α] (a : n -> α) : diag (diagonal a) = 
a
参数：a : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
-/
theorem diag_diagonal [DecidableEq n] [Zero α] (a : n → α) : diag (diagonal a) = a :=
  funext <| @diagonal_apply_eq _ _ _ _ a

@[simp]
/-
**Matrix.diag_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_transpose (A : Matrix n n α) : diag Aᵀ = diag A
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_transpose (A : Matrix n n α) : diag Aᵀ = diag A :=
  rfl

@[simp]
/-
**Matrix.diag_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_zero [Zero α] : diag (0 : Matrix n n α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_zero [Zero α] : diag (0 : Matrix n n α) = 0 :=
  rfl

@[simp]
/-
**Matrix.diag_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_add [Add α] (A B : Matrix n n α) : diag (A + B) = diag A + diag B
参数：A B : Matrix n n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_add [Add α] (A B : Matrix n n α) : diag (A + B) = diag A + diag B :=
  rfl

@[simp]
/-
**Matrix.diag_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_sub [Sub α] (A B : Matrix n n α) : diag (A - B) = diag A - diag B
参数：A B : Matrix n n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_sub [Sub α] (A B : Matrix n n α) : diag (A - B) = diag A - diag B :=
  rfl

@[simp]
/-
**Matrix.diag_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_neg [Neg α] (A : Matrix n n α) : diag (-A) = -diag A
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_neg [Neg α] (A : Matrix n n α) : diag (-A) = -diag A :=
  rfl

@[simp]
/-
**Matrix.diag_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_smul [SMul R α] (r : R) (A : Matrix n n α) : diag (r • A) = r • diag 
A
参数：r : R；A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_smul [SMul R α] (r : R) (A : Matrix n n α) : diag (r • A) = r • diag A :=
  rfl

@[simp]
/-
**Matrix.diag_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_one [DecidableEq n] [Zero α] [One α] : diag (1 : Matrix n n α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diag_diagonal`：diag_diagonal [DecidableEq n] [Zero α] (a : n -> α
) : diag (diagonal a) = a
-/
theorem diag_one [DecidableEq n] [Zero α] [One α] : diag (1 : Matrix n n α) = 1 :=
  diag_diagonal _
/-
**Matrix.diag_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_map {f : α -> β} {A : Matrix n n α} : diag (A.map f) = f ∘ diag A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_map {f : α → β} {A : Matrix n n α} : diag (A.map f) = f ∘ diag A :=
  rfl

end Diag

end Matrix

open Matrix

namespace Matrix

section Transpose

@[simp]
/-
**Matrix.transpose_eq_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_eq_diagonal [DecidableEq n] [Zero α] {M : Matrix n n α} {v : n -
> α} : Mᵀ = diagonal v ↔ M = diagonal v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem transpose_eq_diagonal [DecidableEq n] [Zero α] {M : Matrix n n α} {v : n → α} :
    Mᵀ = diagonal v ↔ M = diagonal v :=
  (Function.Involutive.eq_iff transpose_transpose).trans <|
    by rw [diagonal_transpose]

@[simp]
/-
**Matrix.transpose_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α)ᵀ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
-/
theorem transpose_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α)ᵀ = 1 :=
  diagonal_transpose _

@[simp]
/-
**Matrix.transpose_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_eq_one [DecidableEq n] [Zero α] [One α] {M : Matrix n n α} : Mᵀ 
= 1 ↔ M = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_eq_diagonal`：transpose_eq_diagonal [DecidableEq n] [Zer
o α] {M : Matrix n n α} {v : n -> α} : Mᵀ = diagonal v ↔ M = diagonal v
-/
theorem transpose_eq_one [DecidableEq n] [Zero α] [One α] {M : Matrix n n α} : Mᵀ = 1 ↔ M = 1 :=
  transpose_eq_diagonal

@[simp]
/-
**Matrix.transpose_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_natCast [DecidableEq n] [AddMonoidWithOne α] (d : Nat) : (d : Ma
trix n n α)ᵀ = d
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
-/
theorem transpose_natCast [DecidableEq n] [AddMonoidWithOne α] (d : ℕ) :
    (d : Matrix n n α)ᵀ = d :=
  diagonal_transpose _

@[simp]
/-
**Matrix.transpose_eq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_eq_natCast [DecidableEq n] [AddMonoidWithOne α] {M : Matrix n n 
α} {d : Nat} : Mᵀ = d ↔ M = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_eq_diagonal`：transpose_eq_diagonal [DecidableEq n] [Zer
o α] {M : Matrix n n α} {v : n -> α} : Mᵀ = diagonal v ↔ M = diagonal v
-/
theorem transpose_eq_natCast [DecidableEq n] [AddMonoidWithOne α] {M : Matrix n n α} {d : ℕ} :
    Mᵀ = d ↔ M = d :=
  transpose_eq_diagonal

@[simp]
/-
**Matrix.transpose_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_ofNat [DecidableEq n] [AddMonoidWithOne α] (d : Nat) [d.AtLeastT
wo] : (ofNat(d) : Matrix n n α)ᵀ = OfNat.ofNat d
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_natCast`：transpose_natCast [DecidableEq n] [AddMonoidWi
thOne α] (d : Nat) : (d : Matrix n n α)ᵀ = d
-/
theorem transpose_ofNat [DecidableEq n] [AddMonoidWithOne α] (d : ℕ) [d.AtLeastTwo] :
    (ofNat(d) : Matrix n n α)ᵀ = OfNat.ofNat d :=
  transpose_natCast _

@[simp]
/-
**Matrix.transpose_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_eq_ofNat [DecidableEq n] [AddMonoidWithOne α] {M : Matrix n n α}
 {d : Nat} [d.AtLeastTwo] : Mᵀ = ofNat(d) ↔ M = OfNat.ofNat d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_eq_diagonal`：transpose_eq_diagonal [DecidableEq n] [Zer
o α] {M : Matrix n n α} {v : n -> α} : Mᵀ = diagonal v ↔ M = diagonal v
-/
theorem transpose_eq_ofNat [DecidableEq n] [AddMonoidWithOne α]
    {M : Matrix n n α} {d : ℕ} [d.AtLeastTwo] :
    Mᵀ = ofNat(d) ↔ M = OfNat.ofNat d :=
  transpose_eq_diagonal

@[simp]
/-
**Matrix.transpose_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_intCast [DecidableEq n] [AddGroupWithOne α] (d : Int) : (d : Mat
rix n n α)ᵀ = d
参数：d : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
-/
theorem transpose_intCast [DecidableEq n] [AddGroupWithOne α] (d : ℤ) :
    (d : Matrix n n α)ᵀ = d :=
  diagonal_transpose _

@[simp]
/-
**Matrix.transpose_eq_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_eq_intCast [DecidableEq n] [AddGroupWithOne α] {M : Matrix n n α
} {d : Int} : Mᵀ = d ↔ M = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_eq_diagonal`：transpose_eq_diagonal [DecidableEq n] [Zer
o α] {M : Matrix n n α} {v : n -> α} : Mᵀ = diagonal v ↔ M = diagonal v
-/
theorem transpose_eq_intCast [DecidableEq n] [AddGroupWithOne α]
    {M : Matrix n n α} {d : ℤ} :
    Mᵀ = d ↔ M = d :=
  transpose_eq_diagonal

end Transpose

/-- Given a `(m × m)` diagonal matrix defined by a map `d : m → α`, if the reindexing map `e` is
  injective, then the resulting matrix is again diagonal. -/
/-
**Matrix.submatrix_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_diagonal [Zero α] [DecidableEq m] [DecidableEq l] (d : m -> α) (
e : l -> m) (he : Function.Injective e) : (diagonal d).submatrix e e = diagonal 
(d ∘ e)
参数：d : m -> α；e : l -> m；he : Function.Injective e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_apply`：submatrix_apply (A : Matrix m n α) (r : l -> m) 
(c : o -> n) (i j) : A.submatrix r c i j = A (r i) (c j)
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂

--- 原说明 ---
Given a `(m × m)` diagonal matrix defined by a map `d : m → α`, if the reindexin
g map `e` is
  injective, then the resulting matrix is again diagonal.
-/
theorem submatrix_diagonal [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l → m)
    (he : Function.Injective e) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  ext fun i j => by
    rw [submatrix_apply]
    by_cases h : i = j
    · rw [h, diagonal_apply_eq, diagonal_apply_eq, Function.comp_apply]
    · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (he.ne h)]
/-
**Matrix.submatrix_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_one [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l -> m
) (he : Function.Injective e) : (1 : Matrix m m α).submatrix e e = 1
参数：e : l -> m；he : Function.Injective e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.submatrix_diagonal`：submatrix_diagonal [Zero α] [DecidableEq m] [
DecidableEq l] (d : m -> α) (e : l -> m) (he : Function.Injective e) : (diagonal
 d).submatrix e…
-/
theorem submatrix_one [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l → m)
    (he : Function.Injective e) : (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_diagonal _ e he
/-
**Matrix.diag_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_submatrix (A : Matrix m m α) (e : l -> m) : diag (A.submatrix e e) = 
A.diag ∘ e
参数：A : Matrix m m α；e : l -> m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_submatrix (A : Matrix m m α) (e : l → m) : diag (A.submatrix e e) = A.diag ∘ e :=
  rfl

/-! `simp` lemmas for `Matrix.submatrix`s interaction with `Matrix.diagonal`, `1`, and `Matrix.mul`
for when the mappings are bundled. -/


@[simp]
/-
**Matrix.submatrix_diagonal_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_diagonal_embedding [Zero α] [DecidableEq m] [DecidableEq l] (d :
 m -> α) (e : l ↪ m) : (diagonal d).submatrix e e = diagonal (d ∘ e)
参数：d : m -> α；e : l ↪ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.submatrix_diagonal`：submatrix_diagonal [Zero α] [DecidableEq m] [
DecidableEq l] (d : m -> α) (e : l -> m) (he : Function.Injective e) : (diagonal
 d).submatrix e…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f

--- 原说明 ---
`simp` lemmas for `Matrix.submatrix`s interaction with `Matrix.diagonal`, `1`, a
nd `Matrix.mul`
for when the mappings are bundled.
-/
theorem submatrix_diagonal_embedding [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α)
    (e : l ↪ m) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.injective

@[simp]
/-
**Matrix.submatrix_diagonal_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_diagonal_equiv [Zero α] [DecidableEq m] [DecidableEq l] (d : m -
> α) (e : l ≃ m) : (diagonal d).submatrix e e = diagonal (d ∘ e)
参数：d : m -> α；e : l ≃ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.submatrix_diagonal`：submatrix_diagonal [Zero α] [DecidableEq m] [
DecidableEq l] (d : m -> α) (e : l -> m) (he : Function.Injective e) : (diagonal
 d).submatrix e…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem submatrix_diagonal_equiv [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l ≃ m) :
    (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.injective

@[simp]
/-
**Matrix.submatrix_one_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_one_embedding [Zero α] [One α] [DecidableEq m] [DecidableEq l] (
e : l ↪ m) : (1 : Matrix m m α).submatrix e e = 1
参数：e : l ↪ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.submatrix_one`：submatrix_one [Zero α] [One α] [DecidableEq m] [De
cidableEq l] (e : l -> m) (he : Function.Injective e) : (1 : Matrix m m α).subma
trix e e =…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem submatrix_one_embedding [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ↪ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.injective

@[simp]
/-
**Matrix.submatrix_one_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_one_equiv [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : 
l ≃ m) : (1 : Matrix m m α).submatrix e e = 1
参数：e : l ≃ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.submatrix_one`：submatrix_one [Zero α] [One α] [DecidableEq m] [De
cidableEq l] (e : l -> m) (he : Function.Injective e) : (1 : Matrix m m α).subma
trix e e =…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem submatrix_one_equiv [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ≃ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.injective

end Matrix

