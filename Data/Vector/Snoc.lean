/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
module

public import Mathlib.Data.Vector.Basic

/-!
  This file establishes a `snoc : Vector α n → α → Vector α (n+1)` operation, that appends a single
  element to the back of a vector.

  It provides a collection of lemmas that show how different `Vector` operations reduce when their
  argument is `snoc xs x`.

  Also, an alternative, reverse, induction principle is added, that breaks down a vector into
  `snoc xs x` for its inductive case. Effectively doing induction from right-to-left
-/

@[expose] public section

namespace List

namespace Vector

variable {α β σ φ : Type*} {n : ℕ} {x : α} {s : σ} (xs : Vector α n)

/-- Append a single element to the end of a vector -/
/-
**List.Vector.snoc** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：snoc : Vector α n -> α -> Vector α (n + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Append a single element to the end of a vector
-/
def snoc : Vector α n → α → Vector α (n + 1) :=
  fun xs x => xs ++ x ::ᵥ Vector.nil

/-! ## Simplification lemmas -/

section Simp

variable {y : α}

@[simp]
/-
**List.Vector.snoc_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：snoc_cons : (x ::ᵥ xs).snoc y = x ::ᵥ (xs.snoc y)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snoc_cons : (x ::ᵥ xs).snoc y = x ::ᵥ (xs.snoc y) :=
  rfl

@[simp]
/-
**List.Vector.snoc_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：snoc_nil : (nil.snoc x) = x ::ᵥ nil
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snoc_nil : (nil.snoc x) = x ::ᵥ nil :=
  rfl

@[simp]
/-
**List.Vector.reverse_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：reverse_cons : reverse (x ::ᵥ xs) = (reverse xs).snoc x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem reverse_cons : reverse (x ::ᵥ xs) = (reverse xs).snoc x := by
  cases xs
  simp only [reverse, cons, toList_mk, List.reverse_cons, snoc]
  congr

@[simp]
/-
**List.Vector.reverse_snoc** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：reverse_snoc : reverse (xs.snoc x) = x ::ᵥ (reverse xs)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem reverse_snoc : reverse (xs.snoc x) = x ::ᵥ (reverse xs) := by
  cases xs
  simp only [reverse, snoc, cons, toList_mk]
  congr
  simp [toList, append_def]
/-
**List.Vector.replicate_succ_to_snoc** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：replicate_succ_to_snoc (val : α) : replicate (n + 1) val = (replicate n va
l).snoc val
参数：val : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.replicate_succ`：∀ {α : Type u_1} {n : ℕ} (val : α), List.Vec
tor.replicate (n + 1) val = val ::ᵥ List.Vector.replicate n val
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.Vector.snoc_cons`：snoc_cons : (x ::ᵥ xs).snoc y = x ::ᵥ (xs.snoc y)
-/
theorem replicate_succ_to_snoc (val : α) :
    replicate (n + 1) val = (replicate n val).snoc val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replicate_succ]
    conv => rhs; rw [replicate_succ]
    rw [snoc_cons, ih]

end Simp

/-! ## Reverse induction principle -/

section Induction

/--
Define `C v` by *reverse* induction on `v : Vector α n`.
That is, break the vector down starting from the right-most element, using `snoc`

This function has two arguments: `nil` handles the base case on `C nil`,
and `snoc` defines the inductive step using `∀ x : α, C xs → C (xs.snoc x)`.

This can be used as `induction v using Vector.revInductionOn`. -/
@[elab_as_elim]
/-
**List.Vector.revInductionOn** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：revInductionOn {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : 
Vector α n) (nil : C nil) (snoc : forall {n : Nat} (xs : Vector α n) (x : α), C 
xs -> C (xs.snoc x)) : C v
参数：v : Vector α n；nil : C nil；snoc : forall {n : Nat} (xs : Vector α n) (x : α),
 C xs -> C (xs.snoc x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `C v` by *reverse* induction on `v : Vector α n`.
That is, break the vector down starting from the right-most element, using `snoc
`

This function has two arguments: `nil` handles the base case on `C nil`,
and `snoc` defines the inductive step using `∀ x : α, C xs → C (xs.snoc x)`.

This can be used as `induction v using Vector.revInductionOn`.
-/
def revInductionOn {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (v : Vector α n)
    (nil : C nil)
    (snoc : ∀ {n : ℕ} (xs : Vector α n) (x : α), C xs → C (xs.snoc x)) :
    C v :=
  cast (by simp) <| inductionOn
    (C := fun v => C v.reverse)
    v.reverse
    nil
    (@fun n x xs (r : C xs.reverse) => cast (by simp) <| snoc xs.reverse x r)

/-- Define `C v w` by *reverse* induction on a pair of vectors `v : Vector α n` and
`w : Vector β n`. -/
@[elab_as_elim]
/-
**List.Vector.revInductionOn** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：revInductionOn {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : 
Vector α n) (nil : C nil) (snoc : forall {n : Nat} (xs : Vector α n) (x : α), C 
xs -> C (xs.snoc x)) : C v
参数：v : Vector α n；nil : C nil；snoc : forall {n : Nat} (xs : Vector α n) (x : α),
 C xs -> C (xs.snoc x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `C v w` by *reverse* induction on a pair of vectors `v : Vector α n` and
`w : Vector β n`.
-/
def revInductionOn₂ {C : ∀ {n : ℕ}, Vector α n → Vector β n → Sort*} {n : ℕ}
    (v : Vector α n) (w : Vector β n)
    (nil : C nil nil)
    (snoc : ∀ {n : ℕ} (xs : Vector α n) (ys : Vector β n) (x : α) (y : β),
      C xs ys → C (xs.snoc x) (ys.snoc y)) :
    C v w :=
  cast (by simp) <| inductionOn₂
    (C := fun v w => C v.reverse w.reverse)
    v.reverse
    w.reverse
    nil
    (@fun n x y xs ys (r : C xs.reverse ys.reverse) =>
      cast (by simp) <| snoc xs.reverse ys.reverse x y r)

/-- Define `C v` by *reverse* case analysis, i.e. by handling the cases `nil` and `xs.snoc x`
separately -/
@[elab_as_elim]
/-
**List.Vector.revCasesOn** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：revCasesOn {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : Vect
or α n) (nil : C nil) (snoc : forall {n : Nat} (xs : Vector α n) (x : α), C (xs.
snoc x)) : C v
参数：v : Vector α n；nil : C nil；snoc : forall {n : Nat} (xs : Vector α n) (x : α),
 C (xs.snoc x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `C v` by *reverse* case analysis, i.e. by handling the cases `nil` and `x
s.snoc x`
separately
-/
def revCasesOn {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (v : Vector α n)
    (nil : C nil)
    (snoc : ∀ {n : ℕ} (xs : Vector α n) (x : α), C (xs.snoc x)) :
    C v :=
  revInductionOn v nil fun xs x _ => snoc xs x

end Induction

/-! ## More simplification lemmas -/

section Simp

@[simp]
/-
**List.Vector.map_snoc** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：map_snoc {f : α -> β} : map f (xs.snoc x) = (map f xs).snoc (f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.map_cons`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} (f : α → β
) (a : α) (v : List.Vector α n),   List.Vector.map f (a ::ᵥ v) = f a ::ᵥ List.Ve
ctor.map f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem map_snoc {f : α → β} : map f (xs.snoc x) = (map f xs).snoc (f x) := by
  induction xs <;> simp_all

@[simp]
/-
**List.Vector.mapAccumr_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr_nil {f : α -> σ -> σ × β} {s : σ} : mapAccumr f Vector.nil s = (
s, Vector.nil)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr_nil {f : α → σ → σ × β} {s : σ} : mapAccumr f Vector.nil s = (s, Vector.nil) :=
  rfl

@[simp]
/-
**List.Vector.mapAccumr_snoc** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr_snoc {f : α -> σ -> σ × β} {s : σ} : mapAccumr f (xs.snoc x) s =
 let q
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapAccumr_snoc {f : α → σ → σ × β} {s : σ} :
    mapAccumr f (xs.snoc x) s
    = let q := f x s
      let r := mapAccumr f xs q.1
      (r.1, r.2.snoc q.2) := by
  induction xs
  · rfl
  · simp [*]

variable (ys : Vector β n)

@[simp]
/-
**List.Vector.map** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {n : ℕ} → (α → β) → List.Vector α n → Li
st.Vector β n
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_snoc {f : α → β → σ} {y : β} :
    map₂ f (xs.snoc x) (ys.snoc y) = (map₂ f xs ys).snoc (f x y) := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all

@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_nil {f : α → β → σ → σ × φ} :
    mapAccumr₂ f Vector.nil Vector.nil s = (s, Vector.nil) :=
  rfl

@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_snoc (f : α → β → σ → σ × φ) (x : α) (y : β) :
    mapAccumr₂ f (xs.snoc x) (ys.snoc y) s
    = let q := f x y s
      let r := mapAccumr₂ f xs ys q.1
      (r.1, r.2.snoc q.2) := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all

end Simp
end Vector

end List

