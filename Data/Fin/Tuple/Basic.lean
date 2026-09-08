/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes, Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Fin.Basic
public import Batteries.Data.Fin.Lemmas

/-!
# Operation on tuples

We interpret maps `∀ i : Fin n, α i` as `n`-tuples of elements of possibly varying type `α i`,
`(α 0, …, α (n-1))`. A particular case is `Fin n → α` of elements with all the same type.
In this case when `α i` is a constant map, then tuples are isomorphic (but not definitionally equal)
to `Vector`s.

## Main declarations

There are three (main) ways to consider `Fin n` as a subtype of `Fin (n + 1)`, hence three (main)
ways to move between tuples of length `n` and of length `n + 1` by adding/removing an entry.

### Adding at the start

* `Fin.succ`: Send `i : Fin n` to `i + 1 : Fin (n + 1)`. This is defined in Core.
* `Fin.cases`: Induction/recursion principle for `Fin`: To prove a property/define a function for
  all `Fin (n + 1)`, it is enough to prove/define it for `0` and for `i.succ` for all `i : Fin n`.
  This is defined in Core.
* `Fin.cons`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.cons a f : Fin (n + 1) → α` by adding `a` at the start. In general, tuples can be dependent
  functions, in which case `f : ∀ i : Fin n, α i.succ` and `a : α 0`. This is a special case of
  `Fin.cases`.
* `Fin.tail`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.tail f : Fin n → α` by forgetting
  the start. In general, tuples can be dependent functions,
  in which case `Fin.tail f : ∀ i : Fin n, α i.succ`.

### Adding at the end

* `Fin.castSucc`: Send `i : Fin n` to `i : Fin (n + 1)`. This is defined in Core.
* `Fin.lastCases`: Induction/recursion principle for `Fin`: To prove a property/define a function
  for all `Fin (n + 1)`, it is enough to prove/define it for `last n` and for `i.castSucc` for all
  `i : Fin n`. This is defined in Core.
* `Fin.snoc`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.snoc f a : Fin (n + 1) → α` by adding `a` at the end. In general, tuples can be dependent
  functions, in which case `f : ∀ i : Fin n, α i.castSucc` and `a : α (last n)`. This is a
  special case of `Fin.lastCases`.
* `Fin.init`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.init f : Fin n → α` by forgetting
  the end. In general, tuples can be dependent functions,
  in which case `Fin.init f : ∀ i : Fin n, α i.castSucc`.

### Adding in the middle

For a **pivot** `p : Fin (n + 1)`,
* `Fin.succAbove`: Send `i : Fin n` to
  * `i : Fin (n + 1)` if `i < p`,
  * `i + 1 : Fin (n + 1)` if `p ≤ i`.
* `Fin.succAboveCases`: Induction/recursion principle for `Fin`: To prove a property/define a
  function for all `Fin (n + 1)`, it is enough to prove/define it for `p` and for `p.succAbove i`
  for all `i : Fin n`.
* `Fin.insertNth`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.insertNth f a : Fin (n + 1) → α` by adding `a` in position `p`. In general, tuples can be
  dependent functions, in which case `f : ∀ i : Fin n, α (p.succAbove i)` and `a : α p`. This is a
  special case of `Fin.succAboveCases`.
* `Fin.removeNth`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.removeNth p f : Fin n → α`
  by forgetting the `p`-th value. In general, tuples can be dependent functions,
  in which case `Fin.removeNth f : ∀ i : Fin n, α (succAbove p i)`.

`p = 0` means we add at the start. `p = last n` means we add at the end.

### Miscellaneous

* `Fin.find p h` : returns the first index `i : Fin n` where `p i` is satisfied given the
  hypothesis that `h : ∃ i, p i`.
* `Fin.append a b` : append two tuples.
* `Fin.repeat n a` : repeat a tuple `n` times.

-/

@[expose] public section

assert_not_exists Monoid

universe u v

namespace Fin

variable {m n : ℕ}

open Function

section Tuple

/-- There is exactly one tuple of size zero. -/
/-
**Fin.** 是 Mathlib 中的一个示例，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is exactly one tuple of size zero.
-/
example (α : Fin 0 → Sort u) : Unique (∀ i : Fin 0, α i) := by infer_instance
/-
**Fin.tuple0_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：tuple0_le {α : Fin 0 -> Type*} [forall i, Preorder (α i)] (f g : forall i,
 α i) : f <= g
参数：α i；f g : forall i, α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tuple0_le {α : Fin 0 → Type*} [∀ i, Preorder (α i)] (f g : ∀ i, α i) : f ≤ g :=
  finZeroElim

variable {α : Fin (n + 1) → Sort u} (x : α 0) (q : ∀ i, α i) (p : ∀ i : Fin n, α i.succ) (i : Fin n)
  (y : α i.succ) (z : α 0)

/-- The tail of an `n+1` tuple, i.e., its last `n` entries. -/
/-
**Fin.tail** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：tail (q : forall i, α i) : forall i : Fin n, α i.succ
参数：q : forall i, α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tail of an `n+1` tuple, i.e., its last `n` entries.
-/
def tail (q : ∀ i, α i) : ∀ i : Fin n, α i.succ := fun i ↦ q i.succ
/-
**Fin.tail_def** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：tail_def {n : Nat} {α : Fin (n + 1) -> Sort*} {q : forall i, α i} : (tail 
fun k : Fin (n + 1) => q k) = fun k : Fin n => q k.succ
参数：n + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_def {n : ℕ} {α : Fin (n + 1) → Sort*} {q : ∀ i, α i} :
    (tail fun k : Fin (n + 1) ↦ q k) = fun k : Fin n ↦ q k.succ :=
  rfl

/-- Adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple. -/
/-
**Fin.cons** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：cons (x : α 0) (p : forall i : Fin n, α i.succ) : forall i, α i
参数：x : α 0；p : forall i : Fin n, α i.succ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple.
-/
def cons (x : α 0) (p : ∀ i : Fin n, α i.succ) : ∀ i, α i := fun j ↦ Fin.cases x p j

@[simp]
/-
**Fin.tail_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：tail_cons : tail (cons x p) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tail_cons : tail (cons x p) = p := by
  simp +unfoldPartialApp [tail, cons]

@[simp]
/-
**Fin.cons_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_succ : cons x p i.succ = p i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_succ : cons x p i.succ = p i := by simp [cons]

@[simp]
/-
**Fin.cons_comp_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_comp_succ {α : Sort*} (x : α) (p : Fin n -> α) : cons x p ∘ Fin.succ 
= p
参数：x : α；p : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
-/
theorem cons_comp_succ {α : Sort*} (x : α) (p : Fin n → α) :
    cons x p ∘ Fin.succ = p :=
  funext fun _ ↦ Fin.cons_succ ..

@[simp]
/-
**Fin.cons_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_zero : cons x p 0 = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_zero : cons x p 0 = x := by simp [cons]

@[simp]
/-
**Fin.cons_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall i : Fin n.succ, 
α i.succ) : cons x p 1 = p 0
参数：n + 2；x : α 0；p : forall i : Fin n.succ, α i.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
-/
theorem cons_one {α : Fin (n + 2) → Sort*} (x : α 0) (p : ∀ i : Fin n.succ, α i.succ) :
    cons x p 1 = p 0 := by
  rw [← cons_succ x p]; rfl

@[simp]
/-
**Fin.cons_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_last {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall i : Fin n.succ,
 α i.succ) : cons x p (.last _) = p (.last _)
参数：n + 2；x : α 0；p : forall i : Fin n.succ, α i.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
-/
theorem cons_last {α : Fin (n + 2) → Sort*} (x : α 0) (p : ∀ i : Fin n.succ, α i.succ) :
    cons x p (.last _) = p (.last _) := by
  rw [← cons_succ x p]; rfl

/-- Updating a tuple and adding an element at the beginning commute. -/
@[simp]
/-
**Fin.cons_update** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_update : cons x (update p i y) = update (cons x p) i.succ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Function.update_apply_of_injective`：update_apply_of_injective (g : foral
l a, β a) {f : α' -> α} (hf : Function.Injective f) (i : α') (a : β (f i)) (j : 
α') : update g (f i) a (…
· 使用引理 `Fin.succ_injective`：succ_injective (n : Nat) : Injective (@Fin.succ n)
· 使用定理 `Function.update.congr_simp`：∀ {α : Sort u} {β : α → Sort v} {inst : Deci
dableEq α} [inst_1 : DecidableEq α] (f f_1 : (a : α) → β a),   f = f_1 → ∀ (a' :
 α) (v v_1 : β a…

--- 原说明 ---
Updating a tuple and adding an element at the beginning commute.
-/
theorem cons_update : cons x (update p i y) = update (cons x p) i.succ y := by
  ext j
  cases j using Fin.cases <;> simp [Ne.symm, update_apply_of_injective _ (succ_injective _)]

/-- As a binary function, `Fin.cons` is injective. -/
/-
**Fin.cons_injective2** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_injective2 : Function.Injective2 (@cons n α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i

--- 原说明 ---
As a binary function, `Fin.cons` is injective.
-/
theorem cons_injective2 : Function.Injective2 (@cons n α) := fun x₀ y₀ x y h ↦
  ⟨congr_fun h 0, funext fun i ↦ by simpa using congr_fun h (Fin.succ i)⟩

@[simp]
/-
**Fin.cons_inj** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_inj {x₀ y₀ : α 0} {x y : forall i : Fin n, α i.succ} : cons x₀ x = co
ns y₀ y ↔ x₀ = y₀ ∧ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.Injective2.eq_iff`：eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f
 a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
· 使用定理 `Fin.cons_injective2`：cons_injective2 : Function.Injective2 (@cons n α)
-/
theorem cons_inj {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ} :
    cons x₀ x = cons y₀ y ↔ x₀ = y₀ ∧ x = y :=
  cons_injective2.eq_iff
/-
**Fin.cons_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_left_injective (x : forall i : Fin n, α i.succ) : Function.Injective 
fun x₀ => cons x₀ x
参数：x : forall i : Fin n, α i.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective2.left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {f : α → β → γ},   Function.Injective2 f → ∀ (b : β), Function.Injective fun a 
=> f a b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.cons_injective2`：cons_injective2 : Function.Injective2 (@cons n α)
-/
theorem cons_left_injective (x : ∀ i : Fin n, α i.succ) : Function.Injective fun x₀ ↦ cons x₀ x :=
  cons_injective2.left _
/-
**Fin.cons_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_right_injective (x₀ : α 0) : Function.Injective (cons x₀)
参数：x₀ : α 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.Injective2.right`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3
} {f : α → β → γ},   Function.Injective2 f → ∀ (a : α), Function.Injective (f a)
· 使用定理 `Fin.cons_injective2`：cons_injective2 : Function.Injective2 (@cons n α)
-/
theorem cons_right_injective (x₀ : α 0) : Function.Injective (cons x₀) :=
  cons_injective2.right _

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
@[simp]
/-
**Fin.update_cons_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：update_cons_zero : update (cons x p) 0 z = cons z p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i

--- 原说明 ---
Adding an element at the beginning of a tuple and then updating it amounts to ad
ding it
directly.
-/
theorem update_cons_zero : update (cons x p) 0 z = cons z p := by
  ext j
  cases j using Fin.cases <;> simp

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
/-
**Fin.cons_self_tail** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_self_tail : cons (q 0) (tail q) = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i

--- 原说明 ---
Concatenating the first element of a tuple with its tail gives back the original
 tuple
-/
theorem cons_self_tail : cons (q 0) (tail q) = q := by
  ext j
  cases j using Fin.cases <;> simp [tail]

@[simp]
/-
**Fin.cons_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_zero_succ : (cons 0 Fin.succ : Fin (n + 1) -> Fin (n + 1)) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.cons_self_tail`：cons_self_tail : cons (q 0) (tail q) = q
-/
theorem cons_zero_succ : (cons 0 Fin.succ : Fin (n + 1) → Fin (n + 1)) = id :=
  cons_self_tail id

/-- Equivalence between tuples of length `n + 1` and pairs of an element and a tuple of length `n`
given by separating out the first element of the tuple.

This is `Fin.cons` as an `Equiv`. -/
@[simps]
/-
**Fin.consEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：consEquiv (α : Fin (n + 1) -> Type*) : α 0 × (forall i, α (succ i)) ≃ fora
ll i, α i where toFun f
参数：α : Fin (n + 1) -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between tuples of length `n + 1` and pairs of an element and a tuple
 of length `n`
given by separating out the first element of the tuple.

This is `Fin.cons` as an `Equiv`.
-/
def consEquiv (α : Fin (n + 1) → Type*) : α 0 × (∀ i, α (succ i)) ≃ ∀ i, α i where
  toFun f := cons f.1 f.2
  invFun f := (f 0, tail f)
  left_inv f := by simp
  right_inv f := by simp

/-- Recurse on an `n+1`-tuple by splitting it into a single element and an `n`-tuple. -/
@[elab_as_elim]
/-
**Fin.consCases** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：consCases {motive : (forall i : Fin n.succ, α i) -> Sort v} (cons : forall
 x₀ x, motive (Fin.cons x₀ x)) (x : forall i : Fin n.succ, α i) : motive x
参数：forall i : Fin n.succ, α i；cons : forall x₀ x, motive (Fin.cons x₀ x)；x : for
all i : Fin n.succ, α i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Recurse on an `n+1`-tuple by splitting it into a single element and an `n`-tuple
.
-/
def consCases {motive : (∀ i : Fin n.succ, α i) → Sort v} (cons : ∀ x₀ x, motive (Fin.cons x₀ x))
    (x : ∀ i : Fin n.succ, α i) : motive x :=
  _root_.cast (by rw [cons_self_tail]) <| cons (x 0) (tail x)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Fin.consCases_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：consCases_cons {motive : (forall i : Fin n.succ, α i) -> Sort v} (cons : f
orall x₀ x, motive (Fin.cons x₀ x)) (x₀ : α 0) (x : forall i : Fin n, α i.succ) 
: consCases cons (Fin.cons x₀ x) = cons x₀ x
参数：forall i : Fin n.succ, α i；cons : forall x₀ x, motive (Fin.cons x₀ x)；x₀ : α 
0；x : forall i : Fin n, α i.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.consCases.eq_1`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u} {motive : ((i :
 Fin n.succ) → α i) → Sort v}   (cons : (x₀ : α 0) → (x : (i : Fin n) → α i.succ
) → moti…
· 使用定理 `cast_eq`：∀ {α : Sort u} (h : α = α) (a : α), cast h a = a
-/
theorem consCases_cons {motive : (∀ i : Fin n.succ, α i) → Sort v}
    (cons : ∀ x₀ x, motive (Fin.cons x₀ x))
    (x₀ : α 0) (x : ∀ i : Fin n, α i.succ) : consCases cons (Fin.cons x₀ x) = cons x₀ x := by
  rw [consCases, cast_eq]
  congr

/-- Recurse on a tuple by splitting into `Fin.elim0` and `Fin.cons`. -/
@[elab_as_elim]
/-
**Fin.consInduction** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：{α : Sort u_1} →   {motive : {n : ℕ} → (Fin n → α) → Sort v} →     motive 
Fin.elim0 →       ({n : ℕ} → (x₀ : α) → (x : Fin n → α) → motive x → motive (Fin
.cons x₀ x)) → {n : ℕ} → (x : Fin n → α) → motive x
参数：Fin n → α；{n : ℕ} → (x₀ : α) → (x : Fin n → α) → motive x → motive (Fin.cons 
x₀ x)；x : Fin n → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recurse on a tuple by splitting into `Fin.elim0` and `Fin.cons`.
-/
def consInduction {α : Sort*} {motive : ∀ {n : ℕ}, (Fin n → α) → Sort v} (elim0 : motive Fin.elim0)
    (cons : ∀ {n} (x₀) (x : Fin n → α), motive x → motive (Fin.cons x₀ x)) :
    ∀ {n : ℕ} (x : Fin n → α), motive x
  | 0, x => by convert! elim0
  | _ + 1, x => consCases (fun _ _ ↦ cons _ _ <| consInduction elim0 cons _) x
/-
**Fin.cons_injective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_injective_of_injective {α} {x₀ : α} {x : Fin n -> α} (hx₀ : x₀ ∉ Set.
range x) (hx : Function.Injective x) : Function.Injective (cons x₀ x : Fin n.suc
c -> α)
参数：hx₀ : x₀ ∉ Set.range x；hx : Function.Injective x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem cons_injective_of_injective {α} {x₀ : α} {x : Fin n → α} (hx₀ : x₀ ∉ Set.range x)
    (hx : Function.Injective x) : Function.Injective (cons x₀ x : Fin n.succ → α) := by
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> aesop (add simp [hx.eq_iff])
/-
**Fin.cons_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_injective_iff {α} {x₀ : α} {x : Fin n -> α} : Function.Injective (con
s x₀ x : Fin n.succ -> α) ↔ x₀ ∉ Set.range x ∧ Function.Injective x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Fin.cons_comp_succ`：cons_comp_succ {α : Sort*} (x : α) (p : Fin n -> α) 
: cons x p ∘ Fin.succ = p
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `Fin.succ_injective`：succ_injective (n : Nat) : Injective (@Fin.succ n)
· 使用定理 `Fin.cons_injective_of_injective`：cons_injective_of_injective {α} {x₀ : α
} {x : Fin n -> α} (hx₀ : x₀ ∉ Set.range x) (hx : Function.Injective x) : Functi
on.Injective (cons x₀…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem cons_injective_iff {α} {x₀ : α} {x : Fin n → α} :
    Function.Injective (cons x₀ x : Fin n.succ → α) ↔ x₀ ∉ Set.range x ∧ Function.Injective x := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ cons_injective_of_injective h.1 h.2⟩
  · rintro ⟨i, hi⟩
    replace h := @h i.succ 0
    simp [hi] at h
  · simpa [Function.comp] using! h.comp (Fin.succ_injective _)
/-
**Fin.exists_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：exists_cons {α : Fin (n + 1) -> Type*} (q : forall i, α i) : exists (x₀ : 
α 0) (x : forall i : Fin n, α i.succ), q = cons x₀ x
参数：n + 1；q : forall i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_self_tail`：cons_self_tail : cons (q 0) (tail q) = q
-/
theorem exists_cons {α : Fin (n + 1) → Type*} (q : ∀ i, α i) :
    ∃ (x₀ : α 0) (x : ∀ i : Fin n, α i.succ), q = cons x₀ x :=
  ⟨q 0, tail q, (cons_self_tail q).symm⟩

@[simp]
/-
**Fin.forall_fin_zero_pi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：forall_fin_zero_pi {α : Fin 0 -> Sort*} {P : (forall i, α i) -> Prop} : (f
orall x, P x) ↔ P finZeroElim
参数：forall i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem forall_fin_zero_pi {α : Fin 0 → Sort*} {P : (∀ i, α i) → Prop} :
    (∀ x, P x) ↔ P finZeroElim :=
  ⟨fun h ↦ h _, fun h x ↦ Subsingleton.elim finZeroElim x ▸ h⟩

@[simp]
/-
**Fin.exists_fin_zero_pi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：exists_fin_zero_pi {α : Fin 0 -> Sort*} {P : (forall i, α i) -> Prop} : (e
xists x, P x) ↔ P finZeroElim
参数：forall i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem exists_fin_zero_pi {α : Fin 0 → Sort*} {P : (∀ i, α i) → Prop} :
    (∃ x, P x) ↔ P finZeroElim :=
  ⟨fun ⟨x, h⟩ ↦ Subsingleton.elim x finZeroElim ▸ h, fun h ↦ ⟨_, h⟩⟩
/-
**Fin.forall_fin_succ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：forall_fin_succ_pi {P : (forall i, α i) -> Prop} : (forall x, P x) ↔ foral
l a v, P (Fin.cons a v)
参数：forall i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem forall_fin_succ_pi {P : (∀ i, α i) → Prop} : (∀ x, P x) ↔ ∀ a v, P (Fin.cons a v) :=
  ⟨fun h a v ↦ h (Fin.cons a v), consCases⟩
/-
**Fin.exists_fin_succ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：exists_fin_succ_pi {P : (forall i, α i) -> Prop} : (exists x, P x) ↔ exist
s a v, P (Fin.cons a v)
参数：forall i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_self_tail`：cons_self_tail : cons (q 0) (tail q) = q
-/
theorem exists_fin_succ_pi {P : (∀ i, α i) → Prop} : (∃ x, P x) ↔ ∃ a v, P (Fin.cons a v) :=
  ⟨fun ⟨x, h⟩ ↦ ⟨x 0, tail x, (cons_self_tail x).symm ▸ h⟩, fun ⟨_, _, h⟩ ↦ ⟨_, h⟩⟩

/-- Updating the first element of a tuple does not change the tail. -/
@[simp]
/-
**Fin.tail_update_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：tail_update_zero : tail (update q 0 z) = tail q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Updating the first element of a tuple does not change the tail.
-/
theorem tail_update_zero : tail (update q 0 z) = tail q := by
  ext j
  simp [tail]

/-- Updating a nonzero element and taking the tail commute. -/
@[simp]
/-
**Fin.tail_update_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：tail_update_succ : tail (update q i.succ y) = update (tail q) i y
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
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用引理 `Fin.succ_injective`：succ_injective (n : Nat) : Injective (@Fin.succ n)
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Updating a nonzero element and taking the tail commute.
-/
theorem tail_update_succ : tail (update q i.succ y) = update (tail q) i y := by
  ext j
  by_cases h : j = i
  · rw [h]
    simp [tail]
  · simp [tail, (Fin.succ_injective n).ne h, h]
/-
**Fin.comp_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：comp_cons {α : Sort*} {β : Sort*} (g : α -> β) (y : α) (q : Fin n -> α) : 
g ∘ cons y q = cons (g y) (g ∘ q)
参数：g : α -> β；y : α；q : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem comp_cons {α : Sort*} {β : Sort*} (g : α → β) (y : α) (q : Fin n → α) :
    g ∘ cons y q = cons (g y) (g ∘ q) := by
  ext j
  by_cases h : j = 0
  · rw [h]
    rfl
  · let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this, cons_succ, comp_apply, comp_apply, cons_succ]
/-
**Fin.comp_tail** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：comp_tail {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n.succ -> α) : g ∘
 tail q = tail (g ∘ q)
参数：g : α -> β；q : Fin n.succ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_tail {α : Sort*} {β : Sort*} (g : α → β) (q : Fin n.succ → α) :
    g ∘ tail q = tail (g ∘ q) := by
  ext j
  simp [tail]

section Preorder

variable {α : Fin (n + 1) → Type*}

/-
**Fin.le_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_cons [forall i, Preorder (α i)] {x : α 0} {q : forall i, α i} {p : fora
ll i : Fin n, α i.succ} : q <= cons x p ↔ q 0 <= x ∧ tail q <= p
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Fin.forall_fin_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∀ (i : Fin (n 
+ 1)), P i) ↔ P 0 ∧ ∀ (i : Fin n), P i.succ
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_cons [∀ i, Preorder (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ i : Fin n, α i.succ} :
    q ≤ cons x p ↔ q 0 ≤ x ∧ tail q ≤ p :=
  forall_fin_succ.trans <| and_congr Iff.rfl <| forall_congr' fun j ↦ by simp [tail]
/-
**Fin.cons_le** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_le [forall i, Preorder (α i)] {x : α 0} {q : forall i, α i} {p : fora
ll i : Fin n, α i.succ} : cons x p <= q ↔ x <= q 0 ∧ p <= tail q
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.le_cons`：le_cons [forall i, Preorder (α i)] {x : α 0} {q : forall i,
 α i} {p : forall i : Fin n, α i.succ} : q <= cons x p ↔ q 0 <= x ∧ tail q <= p
-/
theorem cons_le [∀ i, Preorder (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ i : Fin n, α i.succ} :
    cons x p ≤ q ↔ x ≤ q 0 ∧ p ≤ tail q :=
  @le_cons _ (fun i ↦ (α i)ᵒᵈ) _ x q p
/-
**Fin.cons_le_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_le_cons [forall i, Preorder (α i)] {x₀ y₀ : α 0} {x y : forall i : Fi
n n, α i.succ} : cons x₀ x <= cons y₀ y ↔ x₀ <= y₀ ∧ x <= y
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Fin.forall_fin_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∀ (i : Fin (n 
+ 1)), P i) ↔ P 0 ∧ ∀ (i : Fin n), P i.succ
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cons_le_cons [∀ i, Preorder (α i)] {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ} :
    cons x₀ x ≤ cons y₀ y ↔ x₀ ≤ y₀ ∧ x ≤ y :=
  forall_fin_succ.trans <| and_congr_right' <| by simp only [cons_succ, Pi.le_def]

end Preorder

/-
**Fin.range_fin_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：range_fin_succ {α} (f : Fin (n + 1) -> α) : Set.range f = insert (f 0) (Se
t.range (Fin.tail f))
参数：f : Fin (n + 1) -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Fin.exists_fin_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∃ i, P i) ↔ P 
0 ∨ ∃ i, P i.succ
· 使用定理 `Iff.or`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem range_fin_succ {α} (f : Fin (n + 1) → α) :
    Set.range f = insert (f 0) (Set.range (Fin.tail f)) :=
  Set.ext fun _ ↦ exists_fin_succ.trans <| eq_comm.or Iff.rfl

@[simp]
/-
**Fin.range_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：range_cons {α} {n : Nat} (x : α) (b : Fin n -> α) : Set.range (Fin.cons x 
b : Fin n.succ -> α) = insert x (Set.range b)
参数：x : α；b : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.range_fin_succ`：range_fin_succ {α} (f : Fin (n + 1) -> α) : Set.rang
e f = insert (f 0) (Set.range (Fin.tail f))
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.tail_cons`：tail_cons : tail (cons x p) = p
-/
theorem range_cons {α} {n : ℕ} (x : α) (b : Fin n → α) :
    Set.range (Fin.cons x b : Fin n.succ → α) = insert x (Set.range b) := by
  rw [range_fin_succ, cons_zero, tail_cons]

section Append

variable {α : Sort*}

/-- Append a tuple of length `m` to a tuple of length `n` to get a tuple of length `m + n`.
This is a non-dependent version of `Fin.add_cases`. -/
/-
**Fin.append** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：append (a : Fin m -> α) (b : Fin n -> α) : Fin (m + n) -> α
参数：a : Fin m -> α；b : Fin n -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Append a tuple of length `m` to a tuple of length `n` to get a tuple of length `
m + n`.
This is a non-dependent version of `Fin.add_cases`.
-/
def append (a : Fin m → α) (b : Fin n → α) : Fin (m + n) → α :=
  @Fin.addCases _ _ (fun _ => α) a b

@[simp]
/-
**Fin.append_left** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin m) : append u v (Fi
n.castAdd n i) = u i
参数：u : Fin m -> α；v : Fin n -> α；i : Fin m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
-/
theorem append_left (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    append u v (Fin.castAdd n i) = u i :=
  addCases_left _

/-- Variant of `append_left` using `Fin.castLE` instead of `Fin.castAdd`. -/
@[simp]
/-
**Fin.append_left'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_left' (u : Fin m -> α) (v : Fin n -> α) (i : Fin m) : append u v (F
in.castLE (by lia) i) = u i
参数：u : Fin m -> α；v : Fin n -> α；i : Fin m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …

--- 原说明 ---
Variant of `append_left` using `Fin.castLE` instead of `Fin.castAdd`.
-/
theorem append_left' (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    append u v (Fin.castLE (by lia) i) = u i :=
  addCases_left _

@[simp]
/-
**Fin.append_right** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fin n) : append u v (n
atAdd m i) = v i
参数：u : Fin m -> α；v : Fin n -> α；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
-/
theorem append_right (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    append u v (natAdd m i) = v i :=
  addCases_right _
/-
**Fin.append_right_nil** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_right_nil (u : Fin m -> α) (v : Fin n -> α) (hv : n = 0) : append u
 v = u ∘ Fin.cast (by rw [hv, Nat.add_zero])
参数：u : Fin m -> α；v : Fin n -> α；hv : n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem append_right_nil (u : Fin m → α) (v : Fin n → α) (hv : n = 0) :
    append u v = u ∘ Fin.cast (by rw [hv, Nat.add_zero]) := by
  refine funext (Fin.addCases (fun l => ?_) fun r => ?_)
  · rw [append_left, Function.comp_apply]
    refine congr_arg u (Fin.ext ?_)
    simp
  · exact (Fin.cast hv r).elim0

@[simp]
/-
**Fin.append_elim0** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_elim0 (u : Fin m -> α) : append u Fin.elim0 = u ∘ Fin.cast (Nat.add
_zero _)
参数：u : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.append_right_nil`：append_right_nil (u : Fin m -> α) (v : Fin n -> α)
 (hv : n = 0) : append u v = u ∘ Fin.cast (by rw [hv, Nat.add_zero])
-/
theorem append_elim0 (u : Fin m → α) :
    append u Fin.elim0 = u ∘ Fin.cast (Nat.add_zero _) :=
  append_right_nil _ _ rfl
/-
**Fin.append_left_nil** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_left_nil (u : Fin m -> α) (v : Fin n -> α) (hu : m = 0) : append u 
v = v ∘ Fin.cast (by rw [hu, Nat.zero_add])
参数：u : Fin m -> α；v : Fin n -> α；hu : m = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem append_left_nil (u : Fin m → α) (v : Fin n → α) (hu : m = 0) :
    append u v = v ∘ Fin.cast (by rw [hu, Nat.zero_add]) := by
  refine funext (Fin.addCases (fun l => ?_) fun r => ?_)
  · exact (Fin.cast hu l).elim0
  · rw [append_right, Function.comp_apply]
    refine congr_arg v (Fin.ext ?_)
    simp [hu]

@[simp]
/-
**Fin.elim0_append** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：elim0_append (v : Fin n -> α) : append Fin.elim0 v = v ∘ Fin.cast (Nat.zer
o_add _)
参数：v : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.append_left_nil`：append_left_nil (u : Fin m -> α) (v : Fin n -> α) (
hu : m = 0) : append u v = v ∘ Fin.cast (by rw [hu, Nat.zero_add])
-/
theorem elim0_append (v : Fin n → α) :
    append Fin.elim0 v = v ∘ Fin.cast (Nat.zero_add _) :=
  append_left_nil _ _ rfl
/-
**Fin.append_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_assoc {p : Nat} (a : Fin m -> α) (b : Fin n -> α) (c : Fin p -> α) 
: append (append a b) c = append a (append b c) ∘ Fin.cast (Nat.add_assoc ..)
参数：a : Fin m -> α；b : Fin n -> α；c : Fin p -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
-/
theorem append_assoc {p : ℕ} (a : Fin m → α) (b : Fin n → α) (c : Fin p → α) :
    append (append a b) c = append a (append b c) ∘ Fin.cast (Nat.add_assoc ..) := by
  ext i
  rw [Function.comp_apply]
  refine Fin.addCases (fun l => ?_) (fun r => ?_) i
  · rw [append_left]
    refine Fin.addCases (fun ll => ?_) (fun lr => ?_) l
    · rw [append_left]
      simp [castAdd_castAdd]
    · rw [append_right]
      simp [castAdd_natAdd]
  · rw [append_right]
    simp [← natAdd_natAdd]

/-- Appending a one-tuple to the left is the same as `Fin.cons`. -/
/-
**Fin.append_left_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_left_eq_cons {n : Nat} (x₀ : Fin 1 -> α) (x : Fin n -> α) : Fin.app
end x₀ x = Fin.cons (x₀ 0) x ∘ Fin.cast (Nat.add_comm ..)
参数：x₀ : Fin 1 -> α；x : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
· 使用定理 `Fin.cast_natAdd`：∀ (n : ℕ) {m : ℕ} (i : Fin m), Fin.cast ⋯ (Fin.natAdd n
 i) = i.addNat n
· 使用定理 `Fin.addNat_one`：∀ {n : ℕ} {i : Fin n}, i.addNat 1 = i.succ
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i

--- 原说明 ---
Appending a one-tuple to the left is the same as `Fin.cons`.
-/
theorem append_left_eq_cons {n : ℕ} (x₀ : Fin 1 → α) (x : Fin n → α) :
    Fin.append x₀ x = Fin.cons (x₀ 0) x ∘ Fin.cast (Nat.add_comm ..) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> clear i
  · intro i
    rw [Subsingleton.elim i 0, Fin.append_left, Function.comp_apply, eq_comm]
    exact Fin.cons_zero _ _
  · intro i
    rw [Fin.append_right, Function.comp_apply, Fin.cast_natAdd, eq_comm, Fin.addNat_one]
    exact Fin.cons_succ _ _ _

/-- `Fin.cons` is the same as appending a one-tuple to the left. -/
/-
**Fin.cons_eq_append** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_eq_append (x : α) (xs : Fin n -> α) : cons x xs = append (cons x Fin.
elim0) xs ∘ Fin.cast (Nat.add_comm ..)
参数：x : α；xs : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.append_left_eq_cons`：append_left_eq_cons {n : Nat} (x₀ : Fin 1 -> α)
 (x : Fin n -> α) : Fin.append x₀ x = Fin.cons (x₀ 0) x ∘ Fin.cast (Nat.add_comm
 ..)
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`Fin.cons` is the same as appending a one-tuple to the left.
-/
theorem cons_eq_append (x : α) (xs : Fin n → α) :
    cons x xs = append (cons x Fin.elim0) xs ∘ Fin.cast (Nat.add_comm ..) := by
  funext i; simp [append_left_eq_cons]
/-
**Fin.append_cast_left** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Sort u_1} {n m : ℕ} (xs : Fin n → α) (ys : Fin m → α) (n' : ℕ) (h :
 n' = n),   Fin.append (xs ∘ Fin.cast h) ys = Fin.append xs ys ∘ Fin.cast ⋯
参数：xs : Fin n → α；ys : Fin m → α；n' : ℕ；h : n' = n；xs ∘ Fin.cast h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.cast_refl`：∀ (n : ℕ) (h : n = n), Fin.cast h = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma append_cast_left {n m} (xs : Fin n → α) (ys : Fin m → α) (n' : ℕ)
    (h : n' = n) :
    Fin.append (xs ∘ Fin.cast h) ys = Fin.append xs ys ∘ (Fin.cast <| by rw [h]) := by
  subst h; simp
/-
**Fin.append_cast_right** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Sort u_1} {n m : ℕ} (xs : Fin n → α) (ys : Fin m → α) (m' : ℕ) (h :
 m' = m),   Fin.append xs (ys ∘ Fin.cast h) = Fin.append xs ys ∘ Fin.cast ⋯
参数：xs : Fin n → α；ys : Fin m → α；m' : ℕ；h : m' = m；ys ∘ Fin.cast h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cast_refl`：∀ (n : ℕ) (h : n = n), Fin.cast h = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma append_cast_right {n m} (xs : Fin n → α) (ys : Fin m → α) (m' : ℕ)
    (h : m' = m) :
    Fin.append xs (ys ∘ Fin.cast h) = Fin.append xs ys ∘ (Fin.cast <| by rw [h]) := by
  subst h; simp
/-
**Fin.append_rev** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：append_rev {m n} (xs : Fin m -> α) (ys : Fin n -> α) (i : Fin (m + n)) : a
ppend xs ys (rev i) = append (ys ∘ rev) (xs ∘ rev) (i.cast (Nat.add_comm ..))
参数：xs : Fin m -> α；ys : Fin n -> α；i : Fin (m + n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Fin.rev_surjective`：rev_surjective : Surjective (@rev n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
· 使用定理 `Fin.cast.congr_simp`：∀ {n m : ℕ} (eq : n = m) (i i_1 : Fin n), i = i_1 →
 Fin.cast eq i = Fin.cast eq i_1
· 使用定理 `Fin.rev_castAdd`：∀ {n : ℕ} (k : Fin n) (m : ℕ), (Fin.castAdd m k).rev = 
k.rev.addNat m
· 使用定理 `Fin.cast_addNat`：∀ {n : ℕ} (m : ℕ) (i : Fin n), Fin.cast ⋯ (i.addNat m) 
= Fin.natAdd m i
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.cast_rev`：cast_rev (i : Fin n) (h : n = m) : i.rev.cast h = (i.cast 
h).rev
· 使用定理 `Fin.cast_natAdd`：∀ (n : ℕ) {m : ℕ} (i : Fin m), Fin.cast ⋯ (Fin.natAdd n
 i) = i.addNat n
· 使用定理 `Fin.rev_addNat`：∀ {n : ℕ} (k : Fin n) (m : ℕ), (k.addNat m).rev = Fin.ca
stAdd m k.rev
-/
lemma append_rev {m n} (xs : Fin m → α) (ys : Fin n → α) (i : Fin (m + n)) :
    append xs ys (rev i) = append (ys ∘ rev) (xs ∘ rev) (i.cast (Nat.add_comm ..)) := by
  rcases rev_surjective i with ⟨i, rfl⟩
  rw [rev_rev]
  induction i using Fin.addCases
  · simp [rev_castAdd]
  · simp [cast_rev, rev_addNat]
/-
**Fin.append_comp_rev** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：append_comp_rev {m n} (xs : Fin m -> α) (ys : Fin n -> α) : append xs ys ∘
 rev = append (ys ∘ rev) (xs ∘ rev) ∘ Fin.cast (Nat.add_comm ..)
参数：xs : Fin m -> α；ys : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用引理 `Fin.append_rev`：append_rev {m n} (xs : Fin m -> α) (ys : Fin n -> α) (i 
: Fin (m + n)) : append xs ys (rev i) = append (ys ∘ rev) (xs ∘ rev) (i.cast (Na
t.ad…
-/
lemma append_comp_rev {m n} (xs : Fin m → α) (ys : Fin n → α) :
    append xs ys ∘ rev = append (ys ∘ rev) (xs ∘ rev) ∘ Fin.cast (Nat.add_comm ..) :=
  funext <| append_rev xs ys
/-
**Fin.append_castAdd_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_castAdd_natAdd {f : Fin (m + n) -> α} : append (fun i => f (castAdd
 n i)) (fun i => f (natAdd m i)) = f
参数：m + n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.castAdd_castLT`：∀ {n : ℕ} (m : ℕ) (i : Fin (n + m)) (hi : ↑i < n), F
in.castAdd m (i.castLT hi) = i
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.natAdd_subNat_cast`：∀ {n m : ℕ} {i : Fin (n + m)} (h : n ≤ ↑i), Fin.
natAdd n (Fin.subNat n (Fin.cast ⋯ i) h) = i
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem append_castAdd_natAdd {f : Fin (m + n) → α} :
    append (fun i ↦ f (castAdd n i)) (fun i ↦ f (natAdd m i)) = f := by
  unfold append addCases
  simp

/-- Splitting a dependent finite sequence v into an initial part and a final part,
and then concatenating these components, produces an identical sequence. -/
/-
**Fin.addCases_castAdd_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：addCases_castAdd_natAdd {γ : Fin (m + n) -> Sort*} (v : forall i, γ i) (i 
: Fin (m + n)) : addCases (fun i => v (castAdd n i)) (fun j => v (natAdd m j)) i
 = v i
参数：m + n；v : forall i, γ i；i : Fin (m + n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …

--- 原说明 ---
Splitting a dependent finite sequence v into an initial part and a final part,
and then concatenating these components, produces an identical sequence.
-/
theorem addCases_castAdd_natAdd {γ : Fin (m + n) → Sort*} (v : ∀ i, γ i) (i : Fin (m + n)) :
    addCases (fun i ↦ v (castAdd n i)) (fun j ↦ v (natAdd m j)) i = v i := by
  cases i using addCases <;> simp
/-
**Fin.append_comp_sumElim** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_comp_sumElim {xs : Fin m -> α} {ys : Fin n -> α} : Fin.append xs ys
 ∘ Sum.elim (Fin.castAdd _) (Fin.natAdd _) = Sum.elim xs ys
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
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
-/
theorem append_comp_sumElim {xs : Fin m → α} {ys : Fin n → α} :
    Fin.append xs ys ∘ Sum.elim (Fin.castAdd _) (Fin.natAdd _) = Sum.elim xs ys := by
  ext (i | j) <;> simp

set_option backward.isDefEq.respectTransparency false in
/-
**Fin.append_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_injective_iff {xs : Fin m -> α} {ys : Fin n -> α} : Function.Inject
ive (Fin.append xs ys) ↔ Function.Injective xs ∧ Function.Injective ys ∧ forall 
i j, xs i != ys j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sum.elim_injective`：elim_injective {γ : Sort*} {f : α -> γ} {g : β -> γ}
 : Injective (Sum.elim f g) ↔ Injective f ∧ Injective g ∧ forall a b, f a != g b
 where m…
· 使用定理 `Fin.append_comp_sumElim`：append_comp_sumElim {xs : Fin m -> α} {ys : Fin
 n -> α} : Fin.append xs ys ∘ Sum.elim (Fin.castAdd _) (Fin.natAdd _) = Sum.elim
 xs ys
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
· 使用定理 `Equiv.coe_fn_mk`：∀ {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (l 
: Function.LeftInverse g f) (r : Function.RightInverse g f),   ⇑{ toFun := f, in
vFun …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem append_injective_iff {xs : Fin m → α} {ys : Fin n → α} :
    Function.Injective (Fin.append xs ys) ↔
      Function.Injective xs ∧ Function.Injective ys ∧ ∀ i j, xs i ≠ ys j := by
  -- TODO: move things around so we can just import this.
  -- We inline it because it's still shorter than proving from scratch.
  let finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n) :=
  { toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
    invFun i := @Fin.addCases m n (fun _ => Fin m ⊕ Fin n) Sum.inl Sum.inr i
    left_inv x := by rcases x with y | y <;> simp
    right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp }
  rw [← Sum.elim_injective, ← append_comp_sumElim, ← finSumFinEquiv.injective_comp,
    Equiv.coe_fn_mk]

end Append

section Repeat

variable {α : Sort*}

/-- Repeat `a` `m` times. For example `Fin.repeat 2 ![0, 3, 7] = ![0, 3, 7, 0, 3, 7]`. -/
/-
**Fin.** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Repeat `a` `m` times. For example `Fin.repeat 2 ![0, 3, 7] = ![0, 3, 7, 0, 3, 7]
`.
-/
def «repeat» (m : ℕ) (a : Fin n → α) : Fin (m * n) → α
  | i => a i.modNat

@[simp]
/-
**Fin.repeat_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：repeat_apply (a : Fin n -> α) (i : Fin (m * n)) : Fin.repeat m a i = a i.m
odNat
参数：a : Fin n -> α；i : Fin (m * n)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem repeat_apply (a : Fin n → α) (i : Fin (m * n)) :
    Fin.repeat m a i = a i.modNat :=
  rfl

@[simp]
/-
**Fin.repeat_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：repeat_zero (a : Fin n -> α) : Fin.repeat 0 a = Fin.elim0 ∘ Fin.cast (Nat.
zero_mul _)
参数：a : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
-/
theorem repeat_zero (a : Fin n → α) :
    Fin.repeat 0 a = Fin.elim0 ∘ Fin.cast (Nat.zero_mul _) :=
  funext fun x => (x.cast (Nat.zero_mul _)).elim0

@[simp]
/-
**Fin.repeat_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：repeat_one (a : Fin n -> α) : Fin.repeat 1 a = a ∘ Fin.cast (Nat.one_mul _
)
参数：a : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `Fin.rightInverse_cast`：rightInverse_cast (eq : n = m) : RightInverse (Fi
n.cast eq.symm) (Fin.cast eq)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
-/
theorem repeat_one (a : Fin n → α) : Fin.repeat 1 a = a ∘ Fin.cast (Nat.one_mul _) := by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  intro i
  simp [modNat, Nat.mod_eq_of_lt i.is_lt]
/-
**Fin.repeat_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：repeat_succ (a : Fin n -> α) (m : Nat) : Fin.repeat m.succ a = append a (F
in.repeat m a) ∘ Fin.cast ((Nat.succ_mul _ _).trans (Nat.add_comm ..))
参数：a : Fin n -> α；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `Fin.rightInverse_cast`：rightInverse_cast (eq : n = m) : RightInverse (Fi
n.cast eq.symm) (Fin.cast eq)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_mod_left`：∀ (x z : ℕ), (x + z) % x = z % x
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
-/
theorem repeat_succ (a : Fin n → α) (m : ℕ) :
    Fin.repeat m.succ a =
      append a (Fin.repeat m a) ∘ Fin.cast ((Nat.succ_mul _ _).trans (Nat.add_comm ..)) := by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  refine Fin.addCases (fun l => ?_) fun r => ?_
  · simp [modNat, Nat.mod_eq_of_lt l.is_lt]
  · simp [modNat]

@[simp]
/-
**Fin.repeat_add** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：repeat_add (a : Fin n -> α) (m₁ m₂ : Nat) : Fin.repeat (m₁ + m₂) a = appen
d (Fin.repeat m₁ a) (Fin.repeat m₂ a) ∘ Fin.cast (Nat.add_mul ..)
参数：a : Fin n -> α；m₁ m₂ : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `Fin.rightInverse_cast`：rightInverse_cast (eq : n = m) : RightInverse (Fi
n.cast eq.symm) (Fin.cast eq)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mul_mod_left`：∀ (m n : ℕ), m * n % n = 0
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
· 使用定理 `Nat.add_mul`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
-/
theorem repeat_add (a : Fin n → α) (m₁ m₂ : ℕ) : Fin.repeat (m₁ + m₂) a =
    append (Fin.repeat m₁ a) (Fin.repeat m₂ a) ∘ Fin.cast (Nat.add_mul ..) := by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  refine Fin.addCases (fun l => ?_) fun r => ?_
  · simp [modNat]
  · simp [modNat, Nat.add_mod]
/-
**Fin.repeat_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：repeat_rev (a : Fin n -> α) (k : Fin (m * n)) : Fin.repeat m a k.rev = Fin
.repeat m (a ∘ Fin.rev) k
参数：a : Fin n -> α；k : Fin (m * n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Fin.modNat_rev`：modNat_rev (i : Fin (m * n)) : i.rev.modNat = i.modNat.r
ev
-/
theorem repeat_rev (a : Fin n → α) (k : Fin (m * n)) :
    Fin.repeat m a k.rev = Fin.repeat m (a ∘ Fin.rev) k :=
  congr_arg a k.modNat_rev
/-
**Fin.repeat_comp_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：repeat_comp_rev (a : Fin n -> α) : Fin.repeat m a ∘ Fin.rev = Fin.repeat m
 (a ∘ Fin.rev)
参数：a : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.repeat_rev`：repeat_rev (a : Fin n -> α) (k : Fin (m * n)) : Fin.repe
at m a k.rev = Fin.repeat m (a ∘ Fin.rev) k
-/
theorem repeat_comp_rev (a : Fin n → α) :
    Fin.repeat m a ∘ Fin.rev = Fin.repeat m (a ∘ Fin.rev) :=
  funext <| repeat_rev a

end Repeat

end Tuple

section TupleRight

/-! In the previous section, we have discussed inserting or removing elements on the left of a
tuple. In this section, we do the same on the right. A difference is that `Fin (n+1)` is constructed
inductively from `Fin n` starting from the left, not from the right. This implies that Lean needs
more help to realize that elements belong to the right types, i.e., we need to insert casts at
several places. -/

variable {α : Fin (n + 1) → Sort*} (x : α (last n)) (q : ∀ i, α i)
  (p : ∀ i : Fin n, α i.castSucc) (i : Fin n) (y : α i.castSucc) (z : α (last n))

/-- The beginning of an `n+1` tuple, i.e., its first `n` entries -/
/-
**Fin.init** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：init (q : forall i, α i) (i : Fin n) : α i.castSucc
参数：q : forall i, α i；i : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The beginning of an `n+1` tuple, i.e., its first `n` entries
-/
def init (q : ∀ i, α i) (i : Fin n) : α i.castSucc :=
  q i.castSucc
/-
**Fin.init_def** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：init_def {q : forall i, α i} : (init fun k : Fin (n + 1) => q k) = fun k :
 Fin n => q k.castSucc
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem init_def {q : ∀ i, α i} :
    (init fun k : Fin (n + 1) ↦ q k) = fun k : Fin n ↦ q k.castSucc :=
  rfl

/-- Adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc` comes from
`cons` (i.e., adding an element to the left of a tuple) read in reverse order. -/
/-
**Fin.snoc** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：snoc (p : forall i : Fin n, α i.castSucc) (x : α (last n)) (i : Fin (n + 1
)) : α i
参数：p : forall i : Fin n, α i.castSucc；x : α (last n)；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `s
noc` comes from
`cons` (i.e., adding an element to the left of a tuple) read in reverse order.
-/
def snoc (p : ∀ i : Fin n, α i.castSucc) (x : α (last n)) (i : Fin (n + 1)) : α i :=
  if h : i.val < n then _root_.cast (by rw [Fin.castSucc_castLT i h]) (p (castLT i h))
  else _root_.cast (by rw [eq_last_of_not_lt h]) x

@[simp]
/-
**Fin.init_snoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：init_snoc : init (snoc p x) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `cast_eq`：∀ {α : Sort u} (h : α = α) (a : α), cast h a = a
-/
theorem init_snoc : init (snoc p x) = p := by
  ext i
  simp only [init, snoc, val_castSucc, is_lt, dite_true]
  convert! cast_eq rfl (p i)

@[simp]
/-
**Fin.snoc_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_castSucc : snoc p x i.castSucc = p i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `cast_eq`：∀ {α : Sort u} (h : α = α) (a : α), cast h a = a
-/
theorem snoc_castSucc : snoc p x i.castSucc = p i := by
  simp only [snoc, val_castSucc, is_lt, dite_true]
  convert! cast_eq rfl (p i)

@[simp]
/-
**Fin.snoc_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_apply_zero [NeZero n] : snoc p x 0 = p 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
-/
theorem snoc_apply_zero [NeZero n] : snoc p x 0 = p 0 := snoc_castSucc x p 0

@[simp]
/-
**Fin.snoc_comp_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_comp_castSucc {α : Sort*} {a : α} {f : Fin n -> α} : (snoc f a : Fin 
(n + 1) -> α) ∘ castSucc = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
-/
theorem snoc_comp_castSucc {α : Sort*} {a : α} {f : Fin n → α} :
    (snoc f a : Fin (n + 1) → α) ∘ castSucc = f :=
  funext fun i ↦ by rw [Function.comp_apply, snoc_castSucc]

@[simp]
/-
**Fin.snoc_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_last : snoc p x (last n) = x
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem snoc_last : snoc p x (last n) = x := by simp [snoc]
/-
**Fin.snoc_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：snoc_zero {α : Sort*} (p : Fin 0 -> α) (x : α) : Fin.snoc p x = fun _ => x
参数：p : Fin 0 -> α；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snoc_zero {α : Sort*} (p : Fin 0 → α) (x : α) :
    Fin.snoc p x = fun _ ↦ x := rfl

@[simp]
/-
**Fin.snoc_comp_natAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_comp_natAdd {n m : Nat} {α : Sort*} (f : Fin (m + n) -> α) (a : α) : 
(snoc f a : Fin _ -> α) ∘ (natAdd m : Fin (n + 1) -> Fin (m + n + 1)) = snoc (f 
∘ natAdd m) a
参数：f : Fin (m + n) -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Fin.natAdd_last`：∀ {m n : ℕ}, Fin.natAdd n (Fin.last m) = Fin.last (n + 
m)
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Fin.natAdd_castSucc`：∀ {m n : ℕ} {i : Fin m}, Fin.natAdd n i.castSucc = 
(Fin.natAdd n i).castSucc
-/
theorem snoc_comp_natAdd {n m : ℕ} {α : Sort*} (f : Fin (m + n) → α) (a : α) :
    (snoc f a : Fin _ → α) ∘ (natAdd m : Fin (n + 1) → Fin (m + n + 1)) =
      snoc (f ∘ natAdd m) a := by
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp only [Function.comp_apply]
    rw [snoc_last, natAdd_last, snoc_last]
  · simp only [comp_apply, snoc_castSucc]
    rw [natAdd_castSucc, snoc_castSucc]

@[simp]
/-
**Fin.snoc_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_castAdd {α : Fin (n + m + 1) -> Sort*} (f : forall i : Fin (n + m), α
 i.castSucc) (a : α (last (n + m))) (i : Fin n) : (snoc f a) (castAdd (m + 1) i)
 = f (castAdd m i)
参数：n + m + 1；f : forall i : Fin (n + m), α i.castSucc；a : α (last (n + m))；i : F
in n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem snoc_castAdd {α : Fin (n + m + 1) → Sort*} (f : ∀ i : Fin (n + m), α i.castSucc)
    (a : α (last (n + m))) (i : Fin n) : (snoc f a) (castAdd (m + 1) i) = f (castAdd m i) :=
  dif_pos _

@[simp]
/-
**Fin.snoc_comp_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_comp_castAdd {n m : Nat} {α : Sort*} (f : Fin (n + m) -> α) (a : α) :
 (snoc f a : Fin _ -> α) ∘ castAdd (m + 1) = f ∘ castAdd m
参数：f : Fin (n + m) -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.snoc_castAdd`：snoc_castAdd {α : Fin (n + m + 1) -> Sort*} (f : foral
l i : Fin (n + m), α i.castSucc) (a : α (last (n + m))) (i : Fin n) : (snoc f a)
 (cast…
-/
theorem snoc_comp_castAdd {n m : ℕ} {α : Sort*} (f : Fin (n + m) → α) (a : α) :
    (snoc f a : Fin _ → α) ∘ castAdd (m + 1) = f ∘ castAdd m :=
  funext (snoc_castAdd _ _)

/-- Updating a tuple and adding an element at the end commute. -/
@[simp]
/-
**Fin.snoc_update** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_update : snoc (update p i y) x = update (snoc p x) i.castSucc y
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
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
Updating a tuple and adding an element at the end commute.
-/
theorem snoc_update : snoc (update p i y) x = update (snoc p x) i.castSucc y := by
  ext j
  cases j using lastCases with
  | cast j => rcases eq_or_ne j i with rfl | hne <;> simp [*]
  | last => simp [Ne.symm]

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
/-
**Fin.update_snoc_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：update_snoc_last : update (snoc p x) (last n) z = snoc p z
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
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i

--- 原说明 ---
Adding an element at the beginning of a tuple and then updating it amounts to ad
ding it
directly.
-/
theorem update_snoc_last : update (snoc p x) (last n) z = snoc p z := by
  ext j
  cases j using lastCases <;> simp

@[simp]
/-
**Fin.range_snoc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：range_snoc {α : Type*} (f : Fin n -> α) (x : α) : Set.range (snoc f x) = i
nsert x (Set.range f)
参数：f : Fin n -> α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_snoc {α : Type*} (f : Fin n → α) (x : α) :
    Set.range (snoc f x) = insert x (Set.range f) := by
  ext; simp [Fin.exists_fin_succ', or_comm, eq_comm]

/-- As a binary function, `Fin.snoc` is injective. -/
/-
**Fin.snoc_injective2** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_injective2 : Function.Injective2 (@snoc n α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x

--- 原说明 ---
As a binary function, `Fin.snoc` is injective.
-/
theorem snoc_injective2 : Function.Injective2 (@snoc n α) := fun x y xₙ yₙ h ↦
  ⟨funext fun i ↦ by simpa using congr_fun h (castSucc i), by simpa using congr_fun h (last n)⟩

@[simp]
/-
**Fin.snoc_inj** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_inj {x y : forall i : Fin n, α i.castSucc} {xₙ yₙ : α (last n)} : sno
c x xₙ = snoc y yₙ ↔ x = y ∧ xₙ = yₙ
参数：last n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective2.eq_iff`：eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f
 a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
· 使用定理 `Fin.snoc_injective2`：snoc_injective2 : Function.Injective2 (@snoc n α)
-/
theorem snoc_inj {x y : ∀ i : Fin n, α i.castSucc} {xₙ yₙ : α (last n)} :
    snoc x xₙ = snoc y yₙ ↔ x = y ∧ xₙ = yₙ :=
  snoc_injective2.eq_iff
/-
**Fin.snoc_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_right_injective (x : forall i : Fin n, α i.castSucc) : Function.Injec
tive (snoc x)
参数：x : forall i : Fin n, α i.castSucc。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective2.right`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3
} {f : α → β → γ},   Function.Injective2 f → ∀ (a : α), Function.Injective (f a)
· 使用定理 `Fin.snoc_injective2`：snoc_injective2 : Function.Injective2 (@snoc n α)
-/
theorem snoc_right_injective (x : ∀ i : Fin n, α i.castSucc) :
    Function.Injective (snoc x) :=
  snoc_injective2.right _
/-
**Fin.snoc_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_left_injective (xₙ : α (last n)) : Function.Injective (snoc · xₙ)
参数：xₙ : α (last n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective2.left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {f : α → β → γ},   Function.Injective2 f → ∀ (b : β), Function.Injective fun a 
=> f a b
· 使用定理 `Fin.snoc_injective2`：snoc_injective2 : Function.Injective2 (@snoc n α)
-/
theorem snoc_left_injective (xₙ : α (last n)) : Function.Injective (snoc · xₙ) :=
  snoc_injective2.left _

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
/-
**Fin.snoc_init_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_init_self : snoc (init q) (q (last n)) = q
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
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i

--- 原说明 ---
Concatenating the first element of a tuple with its tail gives back the original
 tuple
-/
theorem snoc_init_self : snoc (init q) (q (last n)) = q := by
  ext j
  cases j using Fin.lastCases <;> simp [init]

/-- Updating the last element of a tuple does not change the beginning. -/
@[simp]
/-
**Fin.init_update_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：init_update_last : init (update q (last n) z) = init q
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
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Updating the last element of a tuple does not change the beginning.
-/
theorem init_update_last : init (update q (last n) z) = init q := by
  ext j
  simp [init, Fin.ne_of_lt]

/-- Updating an element and taking the beginning commute. -/
@[simp]
/-
**Fin.init_update_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：init_update_castSucc : init (update q i.castSucc y) = update (init q) i y
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
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Updating an element and taking the beginning commute.
-/
theorem init_update_castSucc : init (update q i.castSucc y) = update (init q) i y := by
  ext j
  by_cases h : j = i
  · rw [h]
    simp [init]
  · simp [init, h, castSucc_inj]

/-- `tail` and `init` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
/-
**Fin.tail_init_eq_init_tail** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：tail_init_eq_init_tail {β : Sort*} (q : Fin (n + 2) -> β) : tail (init q) 
= init (tail q)
参数：q : Fin (n + 2) -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`tail` and `init` commute. We state this lemma in a non-dependent setting, as ot
herwise it
would involve a cast to convince Lean that the two types are equal, making it ha
rder to use.
-/
theorem tail_init_eq_init_tail {β : Sort*} (q : Fin (n + 2) → β) :
    tail (init q) = init (tail q) := by
  ext i
  simp [tail, init]

/-- `cons` and `snoc` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
/-
**Fin.cons_snoc_eq_snoc_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_snoc_eq_snoc_cons {β : Sort*} (a : β) (q : Fin n -> β) (b : β) : @con
s n.succ (fun _ => β) a (snoc q b) = snoc (cons a q) b
参数：a : β；q : Fin n -> β；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.snoc_apply_zero`：snoc_apply_zero [NeZero n] : snoc p x 0 = p 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_last`：cons_last {α : Fin (n + 2) -> Sort*} (x : α 0) (p : foral
l i : Fin n.succ, α i.succ) : cons x p (.last _) = p (.last _)
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i

--- 原说明 ---
`cons` and `snoc` commute. We state this lemma in a non-dependent setting, as ot
herwise it
would involve a cast to convince Lean that the two types are equal, making it ha
rder to use.
-/
theorem cons_snoc_eq_snoc_cons {β : Sort*} (a : β) (q : Fin n → β) (b : β) :
    @cons n.succ (fun _ ↦ β) a (snoc q b) = snoc (cons a q) b := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ j =>
    cases j using Fin.lastCases with
    | last => simp
    | cast j =>
      rw [cons_succ]
      simp [← castSucc_succ]
/-
**Fin.comp_snoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：comp_snoc {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n -> α) (y : α) : 
g ∘ snoc q y = snoc (g ∘ q) (g y)
参数：g : α -> β；q : Fin n -> α；y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.eq_last_of_not_lt`：∀ {n : ℕ} {i : Fin (n + 1)}, ¬↑i < n → i = Fin.la
st n
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
-/
theorem comp_snoc {α : Sort*} {β : Sort*} (g : α → β) (q : Fin n → α) (y : α) :
    g ∘ snoc q y = snoc (g ∘ q) (g y) := by
  ext j
  by_cases h : j.val < n
  · simp [h, snoc, castSucc_castLT]
  · rw [eq_last_of_not_lt h]
    simp

/-- Appending a one-tuple to the right is the same as `Fin.snoc`. -/
/-
**Fin.append_right_eq_snoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_right_eq_snoc {α : Sort*} {n : Nat} (x : Fin n -> α) (x₀ : Fin 1 ->
 α) : Fin.append x x₀ = Fin.snoc x (x₀ 0)
参数：x : Fin n -> α；x₀ : Fin 1 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x

--- 原说明 ---
Appending a one-tuple to the right is the same as `Fin.snoc`.
-/
theorem append_right_eq_snoc {α : Sort*} {n : ℕ} (x : Fin n → α) (x₀ : Fin 1 → α) :
    Fin.append x x₀ = Fin.snoc x (x₀ 0) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> clear i
  · intro i
    rw [Fin.append_left]
    exact (@snoc_castSucc _ (fun _ => α) _ _ i).symm
  · intro i
    rw [Subsingleton.elim i 0, Fin.append_right]
    exact (@snoc_last _ (fun _ => α) _ _).symm

/-- `Fin.snoc` is the same as appending a one-tuple -/
/-
**Fin.snoc_eq_append** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_eq_append {α : Sort*} (xs : Fin n -> α) (x : α) : snoc xs x = append 
xs (cons x Fin.elim0)
参数：xs : Fin n -> α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.append_right_eq_snoc`：append_right_eq_snoc {α : Sort*} {n : Nat} (x 
: Fin n -> α) (x₀ : Fin 1 -> α) : Fin.append x x₀ = Fin.snoc x (x₀ 0)

--- 原说明 ---
`Fin.snoc` is the same as appending a one-tuple
-/
theorem snoc_eq_append {α : Sort*} (xs : Fin n → α) (x : α) :
    snoc xs x = append xs (cons x Fin.elim0) :=
  (append_right_eq_snoc xs (cons x Fin.elim0)).symm
/-
**Fin.append_left_snoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_left_snoc {n m} {α : Sort*} (xs : Fin n -> α) (x : α) (ys : Fin m -
> α) : Fin.append (Fin.snoc xs x) ys = Fin.append xs (Fin.cons x ys) ∘ Fin.cast 
(Nat.succ_add_eq_add_succ ..)
参数：xs : Fin n -> α；x : α；ys : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_add_eq_add_succ`：∀ (a b : ℕ), a.succ + b = a + b.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_eq_append`：snoc_eq_append {α : Sort*} (xs : Fin n -> α) (x : α)
 : snoc xs x = append xs (cons x Fin.elim0)
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Fin.append_assoc`：append_assoc {p : Nat} (a : Fin m -> α) (b : Fin n -> 
α) (c : Fin p -> α) : append (append a b) c = append a (append b c) ∘ Fin.cast (
Nat.ad…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Fin.append_left_eq_cons`：append_left_eq_cons {n : Nat} (x₀ : Fin 1 -> α)
 (x : Fin n -> α) : Fin.append x₀ x = Fin.cons (x₀ 0) x ∘ Fin.cast (Nat.add_comm
 ..)
· 使用定理 `Fin.append_cast_right`：∀ {α : Sort u_1} {n m : ℕ} (xs : Fin n → α) (ys :
 Fin m → α) (m' : ℕ) (h : m' = m),   Fin.append xs (ys ∘ Fin.cast h) = Fin.appen
d xs ys ∘ F…
-/
theorem append_left_snoc {n m} {α : Sort*} (xs : Fin n → α) (x : α) (ys : Fin m → α) :
    Fin.append (Fin.snoc xs x) ys =
      Fin.append xs (Fin.cons x ys) ∘ Fin.cast (Nat.succ_add_eq_add_succ ..) := by
  rw [snoc_eq_append, append_assoc, append_left_eq_cons, append_cast_right]; rfl
/-
**Fin.append_right_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_right_cons {n m} {α : Sort*} (xs : Fin n -> α) (y : α) (ys : Fin m 
-> α) : Fin.append xs (Fin.cons y ys) = Fin.append (Fin.snoc xs y) ys ∘ Fin.cast
 (Nat.succ_add_eq_add_succ ..).symm
参数：xs : Fin n -> α；y : α；ys : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_add_eq_add_succ`：∀ (a b : ℕ), a.succ + b = a + b.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.append_left_snoc`：append_left_snoc {n m} {α : Sort*} (xs : Fin n -> 
α) (x : α) (ys : Fin m -> α) : Fin.append (Fin.snoc xs x) ys = Fin.append xs (Fi
n.cons x y…
-/
theorem append_right_cons {n m} {α : Sort*} (xs : Fin n → α) (y : α) (ys : Fin m → α) :
    Fin.append xs (Fin.cons y ys) =
      Fin.append (Fin.snoc xs y) ys ∘ Fin.cast (Nat.succ_add_eq_add_succ ..).symm := by
  rw [append_left_snoc]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Fin.append_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_cons {α : Sort*} (a : α) (as : Fin n -> α) (bs : Fin m -> α) : Fin.
append (cons a as) bs = cons a (Fin.append as bs) ∘ (Fin.cast <| Nat.add_right_c
omm n 1 m)
参数：a : α；as : Fin n -> α；bs : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Fin.castAdd_castLT`：∀ {n : ℕ} (m : ℕ) (i : Fin (n + m)) (hi : ↑i < n), F
in.castAdd m (i.castLT hi) = i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.not_le_of_gt`：∀ {n m : ℕ}, n > m → ¬n ≤ m
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Nat.gt_of_not_le`：∀ {n m : ℕ}, ¬n ≤ m → n > m
· 使用定理 `Nat.sub_lt_right_of_lt_add`：∀ {n k m : ℕ}, n ≤ k → k < m + n → k - n < m
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
（共 31 条，此处仅展示前 30 条）
-/
theorem append_cons {α : Sort*} (a : α) (as : Fin n → α) (bs : Fin m → α) :
    Fin.append (cons a as) bs
    = cons a (Fin.append as bs) ∘ (Fin.cast <| Nat.add_right_comm n 1 m) := by
  funext i
  rcases i with ⟨i, -⟩
  simp only [append, addCases, cons, castLT, comp_apply]
  rcases i with - | i
  · simp
  · split_ifs with h
    · have : i < n := Nat.lt_of_succ_lt_succ h
      simp [addCases, this]
    · have : ¬i < n := Nat.not_le_of_gt <| Nat.le_of_lt_succ <| Nat.gt_of_not_le h
      simp [addCases, this]

set_option backward.isDefEq.respectTransparency false in
/-
**Fin.append_snoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：append_snoc {α : Sort*} (as : Fin n -> α) (bs : Fin m -> α) (b : α) : Fin.
append as (snoc bs b) = snoc (Fin.append as bs) b
参数：as : Fin n -> α；bs : Fin m -> α；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Nat.sub_lt_right_of_lt_add`：∀ {n k m : ℕ}, n ≤ k → k < m + n → k - n < m
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Fin.castAdd_castLT`：∀ {n : ℕ} (m : ℕ) (i : Fin (n + m)) (hi : ↑i < n), F
in.castAdd m (i.castLT hi) = i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.snoc.eq_1`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : (i : Fin n) →
 α i.castSucc) (x : α (Fin.last n)) (i : Fin (n + 1)),   Fin.snoc p x i = if h :
 ↑i…
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.lt_add_right`：∀ {a b : ℕ} (c : ℕ), a < b → a < b + c
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_of_le_of_lt_succ`：∀ {n m : ℕ}, n ≤ m → m < n + 1 → m = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_lt`：∀ {a b : ℕ}, ¬a < b ↔ b ≤ a
· 使用定理 `Nat.sub_lt_left_of_lt_add`：∀ {n k m : ℕ}, n ≤ k → k < n + m → k - n < m
-/
theorem append_snoc {α : Sort*} (as : Fin n → α) (bs : Fin m → α) (b : α) :
    Fin.append as (snoc bs b) = snoc (Fin.append as bs) b := by
  funext i
  rcases i with ⟨i, isLt⟩
  simp only [append, addCases, castLT, cast_mk, subNat_mk, natAdd_mk, cast, snoc.eq_1,
    eq_rec_constant, Nat.add_eq]
  split_ifs with lt_n lt_add sub_lt nlt_add lt_add <;> (try rfl)
  · have := Nat.lt_add_right m lt_n
    contradiction
  · obtain rfl := Nat.eq_of_le_of_lt_succ (Nat.not_lt.mp nlt_add) isLt
    simp [Nat.add_comm n m] at sub_lt
  · have := Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp lt_n) lt_add
    contradiction
/-
**Fin.comp_init** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：comp_init {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n.succ -> α) : g ∘
 init q = init (g ∘ q)
参数：g : α -> β；q : Fin n.succ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_init {α : Sort*} {β : Sort*} (g : α → β) (q : Fin n.succ → α) :
    g ∘ init q = init (g ∘ q) := by
  ext j
  simp [init]

/-- Equivalence between tuples of length `n + 1` and pairs of an element and a tuple of length `n`
given by separating out the last element of the tuple.

This is `Fin.snoc` as an `Equiv`. -/
@[simps]
/-
**Fin.snocEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：snocEquiv (α : Fin (n + 1) -> Type*) : α (last n) × (forall i, α (castSucc
 i)) ≃ forall i, α i where toFun f _
参数：α : Fin (n + 1) -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between tuples of length `n + 1` and pairs of an element and a tuple
 of length `n`
given by separating out the last element of the tuple.

This is `Fin.snoc` as an `Equiv`.
-/
def snocEquiv (α : Fin (n + 1) → Type*) : α (last n) × (∀ i, α (castSucc i)) ≃ ∀ i, α i where
  toFun f _ := Fin.snoc f.2 f.1 _
  invFun f := ⟨f _, Fin.init f⟩
  left_inv f := by simp
  right_inv f := by simp

/-- Recurse on an `n+1`-tuple by splitting it its initial `n`-tuple and its last element. -/
@[elab_as_elim, inline]
/-
**Fin.snocCases** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：snocCases {motive : (forall i : Fin n.succ, α i) -> Sort*} (snoc : forall 
xs x, motive (Fin.snoc xs x)) (x : forall i : Fin n.succ, α i) : motive x
参数：forall i : Fin n.succ, α i；snoc : forall xs x, motive (Fin.snoc xs x)；x : for
all i : Fin n.succ, α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recurse on an `n+1`-tuple by splitting it its initial `n`-tuple and its last ele
ment.
-/
def snocCases {motive : (∀ i : Fin n.succ, α i) → Sort*}
    (snoc : ∀ xs x, motive (Fin.snoc xs x))
    (x : ∀ i : Fin n.succ, α i) : motive x :=
  _root_.cast (by rw [Fin.snoc_init_self]) <| snoc (Fin.init x) (x <| Fin.last _)

set_option backward.isDefEq.respectTransparency false in
/-
**Fin.snocCases_snoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} {motive : ((i : Fin (n + 1)) → α i)
 → Sort u_2}   (snoc : (x : (i : Fin n) → α i.castSucc) → (x₀ : α (Fin.last n)) 
→ motive (Fin.snoc x x₀))   (x : (i : Fin n) → Fin.init α i) (x₀ : α (Fin.last n
)), Fin.snocCases snoc (Fin.snoc x x₀) = snoc x x₀
参数：n + 1；(i : Fin (n + 1)) → α i；snoc : (x : (i : Fin n) → α i.castSucc) → (x₀ :
 α (Fin.last n)) → motive (Fin.snoc x x₀)；x : (i : Fin n) → Fin.init α i；x₀ : α 
(Fin.last n)；Fin.snoc x x₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snocCases.eq_1`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} {motive : ((i
 : Fin n.succ) → α i) → Sort u_2}   (snoc : (xs : (i : Fin n) → α i.castSucc) → 
(x : α (…
· 使用定理 `cast_eq_iff_heq`：∀ {a a_1 : Sort u_1} {e : a = a_1} {a_2 : a} {a' : a_1}
, cast e a_2 = a' ↔ a_2 ≍ a'
· 使用定理 `Fin.init_snoc`：init_snoc : init (snoc p x) = p
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
-/
@[simp] lemma snocCases_snoc
    {motive : (∀ i : Fin (n + 1), α i) → Sort*} (snoc : ∀ x x₀, motive (Fin.snoc x x₀))
    (x : ∀ i : Fin n, (Fin.init α) i) (x₀ : α (Fin.last _)) :
    snocCases snoc (Fin.snoc x x₀) = snoc x x₀ := by
  rw [snocCases, cast_eq_iff_heq, Fin.init_snoc, Fin.snoc_last]

/-- Recurse on a tuple by splitting into `Fin.elim0` and `Fin.snoc`. -/
@[elab_as_elim]
/-
**Fin.snocInduction** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：{α : Sort u_2} →   {motive : {n : ℕ} → (Fin n → α) → Sort u_3} →     motiv
e Fin.elim0 →       ({n : ℕ} → (x : Fin n → α) → (x₀ : α) → motive x → motive (F
in.snoc x x₀)) → {n : ℕ} → (x : Fin n → α) → motive x
参数：Fin n → α；{n : ℕ} → (x : Fin n → α) → (x₀ : α) → motive x → motive (Fin.snoc 
x x₀)；x : Fin n → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recurse on a tuple by splitting into `Fin.elim0` and `Fin.snoc`.
-/
def snocInduction {α : Sort*}
    {motive : ∀ {n : ℕ}, (Fin n → α) → Sort*}
    (elim0 : motive Fin.elim0)
    (snoc : ∀ {n} (x : Fin n → α) (x₀), motive x → motive (Fin.snoc x x₀)) :
    ∀ {n : ℕ} (x : Fin n → α), motive x
  | 0, x => by convert! elim0
  | _ + 1, x => snocCases (fun _ _ ↦ snoc _ _ <| snocInduction elim0 snoc _) x
/-
**Fin.snoc_injective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_injective_of_injective {α} {x₀ : α} {x : Fin n -> α} (hx : Function.I
njective x) (hx₀ : x₀ ∉ Set.range x) : Function.Injective (snoc x x₀ : Fin n.suc
c -> α)
参数：hx : Function.Injective x；hx₀ : x₀ ∉ Set.range x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
theorem snoc_injective_of_injective {α} {x₀ : α} {x : Fin n → α}
    (hx : Function.Injective x) (hx₀ : x₀ ∉ Set.range x) :
    Function.Injective (snoc x x₀ : Fin n.succ → α) := fun i j h ↦ by
  induction i using lastCases with
  | cast i =>
    induction j using lastCases with
    | cast j =>
      simpa only [castSucc_inj, ← Injective.eq_iff hx, snoc_castSucc] using h
    | last =>
      simp only [snoc_castSucc, snoc_last] at h
      rw [← h] at hx₀
      apply hx₀.elim (Set.mem_range_self i)
  | last =>
    induction j using lastCases with
    | cast j =>
      simp only [snoc_castSucc, snoc_last] at h
      rw [h] at hx₀
      apply hx₀.elim (Set.mem_range_self j)
    | last => simp
/-
**Fin.snoc_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_injective_iff {α} {x₀ : α} {x : Fin n -> α} : Function.Injective (sno
c x x₀ : Fin n.succ -> α) ↔ Function.Injective x ∧ x₀ ∉ Set.range x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_comp_castSucc`：snoc_comp_castSucc {α : Sort*} {a : α} {f : Fin 
n -> α} : (snoc f a : Fin (n + 1) -> α) ∘ castSucc = f
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `Fin.castSucc_injective`：castSucc_injective (n : Nat) : Injective (@Fin.c
astSucc n)
· 使用引理 `Fin.ne_last_of_lt`：ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a !
= last n
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Fin.snoc_injective_of_injective`：snoc_injective_of_injective {α} {x₀ : α
} {x : Fin n -> α} (hx : Function.Injective x) (hx₀ : x₀ ∉ Set.range x) : Functi
on.Injective (snoc x …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem snoc_injective_iff {α} {x₀ : α} {x : Fin n → α} :
    Function.Injective (snoc x x₀ : Fin n.succ → α) ↔ Function.Injective x ∧ x₀ ∉ Set.range x := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ snoc_injective_of_injective h.1 h.2⟩
  · simpa [Function.comp] using h.comp (Fin.castSucc_injective _)
  · rintro ⟨i, hi⟩
    rw [← @snoc_last n (fun i ↦ α) x₀ x, ← @snoc_castSucc n (fun i ↦ α) x₀ x i,
      h.eq_iff] at hi
    exact ne_last_of_lt i.castSucc_lt_last hi

end TupleRight

section InsertNth

variable {α : Fin (n + 1) → Sort*} {β : Sort*}

/-- Define a function on `Fin (n + 1)` from a value on `i : Fin (n + 1)` and values on each
`Fin.succAbove i j`, `j : Fin n`. This version is elaborated as eliminator and works for
propositions, see also `Fin.insertNth` for a version without an `@[elab_as_elim]`
attribute. -/
@[elab_as_elim]
/-
**Fin.succAboveCases** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：succAboveCases {α : Fin (n + 1) -> Sort u} (i : Fin (n + 1)) (x : α i) (p 
: forall j : Fin n, α (i.succAbove j)) (j : Fin (n + 1)) : α j
参数：n + 1；i : Fin (n + 1)；x : α i；p : forall j : Fin n, α (i.succAbove j)；j : Fin
 (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.succAbove_castPred_of_lt`：succAbove_castPred_of_lt (p i : Fin (n + 1
)) (h : i < p) : succAbove p (i.castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p
.le_last)) = i
-/
def succAboveCases {α : Fin (n + 1) → Sort u} (i : Fin (n + 1)) (x : α i)
    (p : ∀ j : Fin n, α (i.succAbove j)) (j : Fin (n + 1)) : α j :=
  if hj : j = i then Eq.rec x hj.symm
  else
    if hlt : j < i then (succAbove_castPred_of_lt _ _ hlt) ▸ (p _)
    else (succAbove_pred_of_lt _ _ <| (Fin.lt_or_lt_of_ne hj).resolve_left hlt) ▸ (p _)

-- This is a duplicate of `Fin.exists_fin_succ` in Core. We should upstream the name change.
alias forall_iff_succ := forall_fin_succ

-- This is a duplicate of `Fin.exists_fin_succ` in Core. We should upstream the name change.
alias exists_iff_succ := exists_fin_succ
/-
**Fin.forall_iff_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：forall_iff_castSucc {P : Fin (n + 1) -> Prop} : (forall i, P i) ↔ P (last 
n) ∧ forall i : Fin n, P i.castSucc
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma forall_iff_castSucc {P : Fin (n + 1) → Prop} :
    (∀ i, P i) ↔ P (last n) ∧ ∀ i : Fin n, P i.castSucc :=
  ⟨fun h ↦ ⟨h _, fun _ ↦ h _⟩, fun h ↦ lastCases h.1 h.2⟩

/-- A finite sequence of properties `P` holds for `{0, ..., m + n - 1}` iff
it holds separately for both `{0, ..., m - 1}` and `{m, ..., m + n - 1}`. -/
/-
**Fin.forall_fin_add** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：forall_fin_add {m n} (P : Fin (m + n) -> Prop) : (forall i, P i) ↔ (forall
 i, P (castAdd _ i)) ∧ (forall j, P (natAdd _ j))
参数：P : Fin (m + n) -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite sequence of properties `P` holds for `{0, ..., m + n - 1}` iff
it holds separately for both `{0, ..., m - 1}` and `{m, ..., m + n - 1}`.
-/
theorem forall_fin_add {m n} (P : Fin (m + n) → Prop) :
    (∀ i, P i) ↔ (∀ i, P (castAdd _ i)) ∧ (∀ j, P (natAdd _ j)) :=
  ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨hm, hn⟩ => Fin.addCases hm hn⟩

/-- A property holds for all dependent finite sequence of length m + n iff
it holds for the concatenation of all pairs of length m sequences and length n sequences. -/
/-
**Fin.forall_fin_add_pi** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：forall_fin_add_pi {γ : Fin (m + n) -> Sort*} {P : (forall i, γ i) -> Prop}
 : (forall v, P v) ↔ (forall (vₘ : forall i, γ (castAdd n i)) (vₙ : forall j, γ 
(natAdd m j)), P (addCases vₘ vₙ)) where mp hv vm vn
参数：m + n；forall i, γ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.addCases_castAdd_natAdd`：addCases_castAdd_natAdd {γ : Fin (m + n) ->
 Sort*} (v : forall i, γ i) (i : Fin (m + n)) : addCases (fun i => v (castAdd n 
i)) (fun j => v (…

--- 原说明 ---
A property holds for all dependent finite sequence of length m + n iff
it holds for the concatenation of all pairs of length m sequences and length n s
equences.
-/
theorem forall_fin_add_pi {γ : Fin (m + n) → Sort*} {P : (∀ i, γ i) → Prop} :
    (∀ v, P v) ↔
      (∀ (vₘ : ∀ i, γ (castAdd n i)) (vₙ : ∀ j, γ (natAdd m j)), P (addCases vₘ vₙ)) where
  mp hv vm vn := hv (addCases vm vn)
  mpr h v := by
    convert h (fun i => v (castAdd n i)) (fun j => v (natAdd m j))
    exact (addCases_castAdd_natAdd v _).symm
/-
**Fin.exists_iff_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：exists_iff_castSucc {P : Fin (n + 1) -> Prop} : (exists i, P i) ↔ P (last 
n) ∨ exists i : Fin n, P i.castSucc where mp
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists_iff_castSucc {P : Fin (n + 1) → Prop} :
    (∃ i, P i) ↔ P (last n) ∨ ∃ i : Fin n, P i.castSucc where
  mp := by
    rintro ⟨i, hi⟩
    cases i using lastCases with
    | last => exact .inl hi
    | cast _ => exact .inr ⟨_, hi⟩
  mpr := by rintro (h | ⟨i, hi⟩) <;> exact ⟨_, ‹_›⟩
/-
**Fin.forall_iff_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：forall_iff_succAbove {P : Fin (n + 1) -> Prop} (p : Fin (n + 1)) : (forall
 i, P i) ↔ P p ∧ forall i, P (p.succAbove i)
参数：n + 1；p : Fin (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem forall_iff_succAbove {P : Fin (n + 1) → Prop} (p : Fin (n + 1)) :
    (∀ i, P i) ↔ P p ∧ ∀ i, P (p.succAbove i) :=
  ⟨fun h ↦ ⟨h _, fun _ ↦ h _⟩, fun h ↦ succAboveCases p h.1 h.2⟩
/-
**Fin.exists_iff_succAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：exists_iff_succAbove {P : Fin (n + 1) -> Prop} (p : Fin (n + 1)) : (exists
 i, P i) ↔ P p ∨ exists i, P (p.succAbove i) where mp
参数：n + 1；p : Fin (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_iff_succAbove {P : Fin (n + 1) → Prop} (p : Fin (n + 1)) :
    (∃ i, P i) ↔ P p ∨ ∃ i, P (p.succAbove i) where
  mp := by
    rintro ⟨i, hi⟩
    induction i using p.succAboveCases
    · exact .inl hi
    · exact .inr ⟨_, hi⟩
  mpr := by rintro (h | ⟨i, hi⟩) <;> exact ⟨_, ‹_›⟩

/-- Analogue of `Fin.eq_zero_or_eq_succ` for `succAbove`. -/
/-
**Fin.eq_self_or_eq_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：eq_self_or_eq_succAbove (p i : Fin (n + 1)) : i = p ∨ exists j, i = p.succ
Above j
参数：p i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Analogue of `Fin.eq_zero_or_eq_succ` for `succAbove`.
-/
theorem eq_self_or_eq_succAbove (p i : Fin (n + 1)) : i = p ∨ ∃ j, i = p.succAbove j :=
  succAboveCases p (.inl rfl) (fun j => .inr ⟨j, rfl⟩) i

/-- Remove the `p`-th entry of a tuple. -/
/-
**Fin.removeNth** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：removeNth (p : Fin (n + 1)) (f : forall i, α i) : forall i, α (p.succAbove
 i)
参数：p : Fin (n + 1)；f : forall i, α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Remove the `p`-th entry of a tuple.
-/
def removeNth (p : Fin (n + 1)) (f : ∀ i, α i) : ∀ i, α (p.succAbove i) := fun i ↦ f (p.succAbove i)

/-- Insert an element into a tuple at a given position. For `i = 0` see `Fin.cons`,
for `i = Fin.last n` see `Fin.snoc`. See also `Fin.succAboveCases` for a version elaborated
as an eliminator. -/
/-
**Fin.insertNth** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：insertNth (i : Fin (n + 1)) (x : α i) (p : forall j : Fin n, α (i.succAbov
e j)) (j : Fin (n + 1)) : α j
参数：i : Fin (n + 1)；x : α i；p : forall j : Fin n, α (i.succAbove j)；j : Fin (n + 
1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Insert an element into a tuple at a given position. For `i = 0` see `Fin.cons`,
for `i = Fin.last n` see `Fin.snoc`. See also `Fin.succAboveCases` for a version
 elaborated
as an eliminator.
-/
def insertNth (i : Fin (n + 1)) (x : α i) (p : ∀ j : Fin n, α (i.succAbove j)) (j : Fin (n + 1)) :
    α j :=
  succAboveCases i x p j

@[simp]
/-
**Fin.insertNth_apply_same** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_apply_same (i : Fin (n + 1)) (x : α i) (p : forall j, α (i.succA
bove j)) : insertNth i x p i = x
参数：i : Fin (n + 1)；x : α i；p : forall j, α (i.succAbove j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用引理 `Fin.succAbove_castPred_of_lt`：succAbove_castPred_of_lt (p i : Fin (n + 1
)) (h : i < p) : succAbove p (i.castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p
.le_last)) = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insertNth_apply_same (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j)) :
    insertNth i x p i = x := by simp [insertNth, succAboveCases]

@[simp]
/-
**Fin.insertNth_apply_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_apply_succAbove (i : Fin (n + 1)) (x : α i) (p : forall j, α (i.
succAbove j)) (j : Fin n) : insertNth i x p (i.succAbove j) = p j
参数：i : Fin (n + 1)；x : α i；p : forall j, α (i.succAbove j)；j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用引理 `Fin.succAbove_castPred_of_lt`：succAbove_castPred_of_lt (p i : Fin (n + 1
)) (h : i < p) : succAbove p (i.castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p
.le_last)) = i
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用引理 `Fin.succAbove_ne`：succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbo
ve i != p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `Fin.ne_last_of_lt`：ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a !
= last n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Fin.succAbove_lt_iff_castSucc_lt`：succAbove_lt_iff_castSucc_lt (p : Fin 
(n + 1)) (i : Fin n) : p.succAbove i < p ↔ castSucc i < p
· 使用引理 `Fin.castPred_succAbove`：castPred_succAbove (x : Fin n) (y : Fin (n + 1))
 (h : castSucc x < y) (h'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用引理 `Fin.lt_succAbove_iff_le_castSucc`：lt_succAbove_iff_le_castSucc (p : Fin 
(n + 1)) (i : Fin n) : p < p.succAbove i ↔ p <= castSucc i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.not_lt`：∀ {n : ℕ} {a b : Fin n}, ¬a < b ↔ b ≤ a
· 使用引理 `Fin.pred_succAbove`：pred_succAbove (x : Fin n) (y : Fin (n + 1)) (h : y 
<= castSucc x) (h'
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem insertNth_apply_succAbove (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j))
    (j : Fin n) : insertNth i x p (i.succAbove j) = p j := by
  simp only [insertNth, succAboveCases, dif_neg (succAbove_ne _ _), succAbove_lt_iff_castSucc_lt]
  split_ifs with hlt
  · generalize_proofs H₁ H₂; revert H₂
    generalize hk : castPred ((succAbove i) j) H₁ = k
    rw [castPred_succAbove _ _ hlt] at hk; cases hk
    intro; rfl
  · generalize_proofs H₀ H₁ H₂; revert H₂
    generalize hk : pred (succAbove i j) H₁ = k
    rw [pred_succAbove _ _ (Fin.not_lt.1 hlt)] at hk; cases hk
    intro; rfl

@[simp]
/-
**Fin.succAbove_cases_eq_insertNth** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：succAbove_cases_eq_insertNth : @succAboveCases = @insertNth
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succAbove_cases_eq_insertNth : @succAboveCases = @insertNth :=
  rfl
/-
**Fin.removeNth_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：removeNth_apply (p : Fin (n + 1)) (f : forall i, α i) (i : Fin n) : p.remo
veNth f i = f (p.succAbove i)
参数：p : Fin (n + 1)；f : forall i, α i；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma removeNth_apply (p : Fin (n + 1)) (f : ∀ i, α i) (i : Fin n) :
    p.removeNth f i = f (p.succAbove i) :=
  rfl

@[simp]
/-
**Fin.cons_comp_succ_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_comp_succ_succAbove (x : β) (p : Fin (n + 1) -> β) (i : Fin (n + 1)) 
: cons x p ∘ i.succ.succAbove = cons x (i.removeNth p)
参数：x : β；p : Fin (n + 1) -> β；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.succ_succAbove_succ`：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), i.succ
.succAbove j.succ = (i.succAbove j).succ
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_comp_succ_succAbove (x : β) (p : Fin (n + 1) → β) (i : Fin (n + 1)) :
    cons x p ∘ i.succ.succAbove = cons x (i.removeNth p) :=
  funext (Fin.cases rfl fun _ ↦ by simp [removeNth])
/-
**Fin.removeNth_fun_const** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：removeNth_fun_const {α : Type*} {n : Nat} (i : Fin (n + 1)) (a : α) : i.re
moveNth (fun _ => a) = (fun _ => a)
参数：i : Fin (n + 1)；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma removeNth_fun_const {α : Type*} {n : ℕ} (i : Fin (n + 1)) (a : α) :
    i.removeNth (fun _ ↦ a) = (fun _ ↦ a) :=
  rfl
/-
**Fin.removeNth_insertNth** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin (n + 1)) (a : α p) (f : (i
 : Fin n) → α (p.succAbove i)),   p.removeNth (p.insertNth a f) = f
参数：n + 1；p : Fin (n + 1)；a : α p；f : (i : Fin n) → α (p.succAbove i)；p.insertNth
 a f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma removeNth_insertNth (p : Fin (n + 1)) (a : α p) (f : ∀ i, α (succAbove p i)) :
    removeNth p (insertNth p a f) = f := by ext; unfold removeNth; simp
/-
**Fin.removeNth_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (f : (i : Fin (n + 1)) → α i), Fin.
removeNth 0 f = Fin.tail f
参数：n + 1；f : (i : Fin (n + 1)) → α i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma removeNth_zero (f : ∀ i, α i) : removeNth 0 f = tail f := by
  ext; simp [tail, removeNth]
/-
**Fin.removeNth_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {α : Type u_3} (f : Fin (n + 1) → α), (Fin.last n).removeNth f =
 Fin.init f
参数：f : Fin (n + 1) → α；Fin.last n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.succAbove_last`：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma removeNth_last {α : Type*} (f : Fin (n + 1) → α) : removeNth (last n) f = init f := by
  ext; simp [init, removeNth]

@[simp]
/-
**Fin.insertNth_comp_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_comp_succAbove (i : Fin (n + 1)) (x : β) (p : Fin n -> β) : inse
rtNth i x p ∘ i.succAbove = p
参数：i : Fin (n + 1)；x : β；p : Fin n -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
-/
theorem insertNth_comp_succAbove (i : Fin (n + 1)) (x : β) (p : Fin n → β) :
    insertNth i x p ∘ i.succAbove = p :=
  funext (insertNth_apply_succAbove i _ _)
/-
**Fin.insertNth_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_eq_iff {p : Fin (n + 1)} {a : α p} {f : forall i, α (p.succAbove
 i)} {g : forall j, α j} : insertNth p a f = g ↔ a = g p ∧ f = removeNth p g
参数：n + 1；p.succAbove i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.forall_iff_succAbove`：forall_iff_succAbove {P : Fin (n + 1) -> Prop}
 (p : Fin (n + 1)) : (forall i, P i) ↔ P p ∧ forall i, P (p.succAbove i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem insertNth_eq_iff {p : Fin (n + 1)} {a : α p} {f : ∀ i, α (p.succAbove i)} {g : ∀ j, α j} :
    insertNth p a f = g ↔ a = g p ∧ f = removeNth p g := by
  simp [funext_iff, forall_iff_succAbove p, removeNth]
/-
**Fin.eq_insertNth_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：eq_insertNth_iff {p : Fin (n + 1)} {a : α p} {f : forall i, α (p.succAbove
 i)} {g : forall j, α j} : g = insertNth p a f ↔ g p = a ∧ removeNth p g = f
参数：n + 1；p.succAbove i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.insertNth_eq_iff`：insertNth_eq_iff {p : Fin (n + 1)} {a : α p} {f : 
forall i, α (p.succAbove i)} {g : forall j, α j} : insertNth p a f = g ↔ a = g p
 ∧ f = rem…
-/
theorem eq_insertNth_iff {p : Fin (n + 1)} {a : α p} {f : ∀ i, α (p.succAbove i)} {g : ∀ j, α j} :
    g = insertNth p a f ↔ g p = a ∧ removeNth p g = f := by
  simpa [eq_comm] using insertNth_eq_iff

/-- As a binary function, `Fin.insertNth` is injective. -/
/-
**Fin.insertNth_injective2** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_injective2 {p : Fin (n + 1)} : Function.Injective2 (@insertNth n
 α p)
参数：n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j

--- 原说明 ---
As a binary function, `Fin.insertNth` is injective.
-/
theorem insertNth_injective2 {p : Fin (n + 1)} :
    Function.Injective2 (@insertNth n α p) := fun xₚ yₚ x y h ↦
  ⟨by simpa using congr_fun h p, funext fun i ↦ by simpa using congr_fun h (succAbove p i)⟩

@[simp]
/-
**Fin.insertNth_inj** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_inj {p : Fin (n + 1)} {x y : forall i, α (succAbove p i)} {xₚ yₚ
 : α p} : insertNth p xₚ x = insertNth p yₚ y ↔ xₚ = yₚ ∧ x = y
参数：n + 1；succAbove p i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective2.eq_iff`：eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f
 a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
· 使用定理 `Fin.insertNth_injective2`：insertNth_injective2 {p : Fin (n + 1)} : Funct
ion.Injective2 (@insertNth n α p)
-/
theorem insertNth_inj {p : Fin (n + 1)} {x y : ∀ i, α (succAbove p i)} {xₚ yₚ : α p} :
    insertNth p xₚ x = insertNth p yₚ y ↔ xₚ = yₚ ∧ x = y :=
  insertNth_injective2.eq_iff
/-
**Fin.insertNth_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_left_injective {p : Fin (n + 1)} (x : forall i, α (succAbove p i
)) : Function.Injective (insertNth p · x)
参数：n + 1；x : forall i, α (succAbove p i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective2.left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {f : α → β → γ},   Function.Injective2 f → ∀ (b : β), Function.Injective fun a 
=> f a b
· 使用定理 `Fin.insertNth_injective2`：insertNth_injective2 {p : Fin (n + 1)} : Funct
ion.Injective2 (@insertNth n α p)
-/
theorem insertNth_left_injective {p : Fin (n + 1)} (x : ∀ i, α (succAbove p i)) :
    Function.Injective (insertNth p · x) :=
  insertNth_injective2.left _
/-
**Fin.insertNth_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_right_injective {p : Fin (n + 1)} (x : α p) : Function.Injective
 (insertNth p x)
参数：n + 1；x : α p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective2.right`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3
} {f : α → β → γ},   Function.Injective2 f → ∀ (a : α), Function.Injective (f a)
· 使用定理 `Fin.insertNth_injective2`：insertNth_injective2 {p : Fin (n + 1)} : Funct
ion.Injective2 (@insertNth n α p)
-/
theorem insertNth_right_injective {p : Fin (n + 1)} (x : α p) :
    Function.Injective (insertNth p x) :=
  insertNth_injective2.right _
/-
**Fin.insertNth_apply_below** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_apply_below {i j : Fin (n + 1)} (h : j < i) (x : α i) (p : foral
l k, α (i.succAbove k)) : i.insertNth x p j = succAbove_castPred_of_lt _ _ h ▸ (
p <| j.castPred _)
参数：n + 1；h : j < i；x : α i；p : forall k, α (i.succAbove k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用引理 `Fin.succAbove_castPred_of_lt`：succAbove_castPred_of_lt (p i : Fin (n + 1
)) (h : i < p) : succAbove p (i.castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p
.le_last)) = i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNth.eq_1`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (i : Fin (n +
 1)) (x : α i) (p : (j : Fin n) → α (i.succAbove j))   (j : Fin (n + 1)), i.inse
rtNth x …
· 使用定理 `Fin.succAboveCases.eq_1`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u} (i : Fin (
n + 1)) (x : α i) (p : (j : Fin n) → α (i.succAbove j))   (j : Fin (n + 1)),   i
.succAboveCas…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem insertNth_apply_below {i j : Fin (n + 1)} (h : j < i) (x : α i)
    (p : ∀ k, α (i.succAbove k)) :
    i.insertNth x p j = succAbove_castPred_of_lt _ _ h ▸ (p <| j.castPred _) := by
  rw [insertNth, succAboveCases, dif_neg (Fin.ne_of_lt h), dif_pos h]
/-
**Fin.insertNth_apply_above** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_apply_above {i j : Fin (n + 1)} (h : i < j) (x : α i) (p : foral
l k, α (i.succAbove k)) : i.insertNth x p j = succAbove_pred_of_lt _ _ h ▸ (p <|
 j.pred _)
参数：n + 1；h : i < j；x : α i；p : forall k, α (i.succAbove k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ne_of_gt`：∀ {n : ℕ} {a b : Fin n}, a < b → b ≠ a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用引理 `Fin.succAbove_pred_of_lt`：succAbove_pred_of_lt (p i : Fin (n + 1)) (h : 
p < i) : succAbove p (i.pred (Fin.ne_of_gt <| Fin.lt_of_le_of_lt p.zero_le h)) =
 i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNth.eq_1`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (i : Fin (n +
 1)) (x : α i) (p : (j : Fin n) → α (i.succAbove j))   (j : Fin (n + 1)), i.inse
rtNth x …
· 使用引理 `Fin.succAbove_castPred_of_lt`：succAbove_castPred_of_lt (p i : Fin (n + 1
)) (h : i < p) : succAbove p (i.castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p
.le_last)) = i
· 使用定理 `Fin.succAboveCases.eq_1`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u} (i : Fin (
n + 1)) (x : α i) (p : (j : Fin n) → α (i.succAbove j))   (j : Fin (n + 1)),   i
.succAboveCas…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Fin.lt_asymm`：∀ {n : ℕ} {a b : Fin n}, a < b → ¬b < a
-/
theorem insertNth_apply_above {i j : Fin (n + 1)} (h : i < j) (x : α i)
    (p : ∀ k, α (i.succAbove k)) :
    i.insertNth x p j = succAbove_pred_of_lt _ _ h ▸ (p <| j.pred _) := by
  rw [insertNth, succAboveCases, dif_neg (Fin.ne_of_gt h), dif_neg (Fin.lt_asymm h)]
/-
**Fin.insertNth_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_zero (x : α 0) (p : forall j : Fin n, α (succAbove 0 j)) : inser
tNth 0 x p = cons x fun j => _root_.cast (congr_arg α (congr_fun succAbove_zero 
j)) (p j)
参数：x : α 0；p : forall j : Fin n, α (succAbove 0 j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Fin.succAbove_zero`：∀ {n : ℕ}, Fin.succAbove 0 = Fin.succ
· 使用定理 `Fin.insertNth_eq_iff`：insertNth_eq_iff {p : Fin (n + 1)} {a : α p} {f : 
forall i, α (p.succAbove i)} {g : forall j, α j} : insertNth p a f = g ↔ a = g p
 ∧ f = rem…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
-/
theorem insertNth_zero (x : α 0) (p : ∀ j : Fin n, α (succAbove 0 j)) :
    insertNth 0 x p =
      cons x fun j ↦ _root_.cast (congr_arg α (congr_fun succAbove_zero j)) (p j) := by
  refine insertNth_eq_iff.2 ⟨by simp, ?_⟩
  ext j
  convert! (cons_succ x p j).symm

@[simp]
/-
**Fin.insertNth_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_zero' (x : β) (p : Fin n -> β) : @insertNth _ (fun _ => β) 0 x p
 = cons x p
参数：x : β；p : Fin n -> β。
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
· 使用定理 `Fin.insertNth_zero`：insertNth_zero (x : α 0) (p : forall j : Fin n, α (s
uccAbove 0 j)) : insertNth 0 x p = cons x fun j => _root_.cast (congr_arg α (con
gr_fun s…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insertNth_zero' (x : β) (p : Fin n → β) : @insertNth _ (fun _ ↦ β) 0 x p = cons x p := by
  simp [insertNth_zero]
/-
**Fin.insertNth_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_last (x : α (last n)) (p : forall j : Fin n, α ((last n).succAbo
ve j)) : insertNth (last n) x p = snoc (fun j => _root_.cast (congr_arg α (succA
bove_last_apply j)) (p j)) x
参数：x : α (last n)；p : forall j : Fin n, α ((last n).succAbove j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Fin.succAbove_last_apply`：succAbove_last_apply (i : Fin n) : succAbove (
last n) i = castSucc i
· 使用定理 `Fin.insertNth_eq_iff`：insertNth_eq_iff {p : Fin (n + 1)} {a : α p} {f : 
forall i, α (p.succAbove i)} {g : forall j, α j} : insertNth p a f = g ↔ a = g p
 ∧ f = rem…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
· 使用定理 `cast_heq`：∀ {α β : Sort u} (h : α = β) (a : α), cast h a ≍ a
· 使用定理 `congr_arg_heq`：∀ {α : Sort u_1} {β : α → Sort u_2} (f : (a : α) → β a) {
a₁ a₂ : α}, a₁ = a₂ → f a₁ ≍ f a₂
· 使用定理 `Fin.succAbove_last`：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
-/
theorem insertNth_last (x : α (last n)) (p : ∀ j : Fin n, α ((last n).succAbove j)) :
    insertNth (last n) x p =
      snoc (fun j ↦ _root_.cast (congr_arg α (succAbove_last_apply j)) (p j)) x := by
  refine insertNth_eq_iff.2 ⟨by simp, ?_⟩
  ext j
  apply eq_of_heq
  trans snoc (fun j ↦ _root_.cast (congr_arg α (succAbove_last_apply j)) (p j)) x j.castSucc
  · rw [snoc_castSucc]
    exact (cast_heq _ _).symm
  · apply congr_arg_heq
    rw [succAbove_last]

@[simp]
/-
**Fin.insertNth_last'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_last' (x : β) (p : Fin n -> β) : @insertNth _ (fun _ => β) (last
 n) x p = snoc p x
参数：x : β；p : Fin n -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNth_last`：insertNth_last (x : α (last n)) (p : forall j : Fin 
n, α ((last n).succAbove j)) : insertNth (last n) x p = snoc (fun j => _root_.ca
st (cong…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insertNth_last' (x : β) (p : Fin n → β) :
    @insertNth _ (fun _ ↦ β) (last n) x p = snoc p x := by simp [insertNth_last]
/-
**Fin.insertNth_rev** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：insertNth_rev {α : Sort*} (i : Fin (n + 1)) (a : α) (f : Fin n -> α) (j : 
Fin (n + 1)) : insertNth (α
参数：i : Fin (n + 1)；a : α；f : Fin n -> α；j : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Fin.rev_succAbove`：rev_succAbove (p : Fin (n + 1)) (i : Fin n) : rev (su
ccAbove p i) = succAbove (rev p) (rev i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
-/
lemma insertNth_rev {α : Sort*} (i : Fin (n + 1)) (a : α) (f : Fin n → α) (j : Fin (n + 1)) :
    insertNth (α := fun _ ↦ α) i a f (rev j) = insertNth (α := fun _ ↦ α) i.rev a (f ∘ rev) j := by
  induction j using Fin.succAboveCases
  · exact rev i
  · simp
  · simp [rev_succAbove]
/-
**Fin.insertNth_comp_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_comp_rev {α} (i : Fin (n + 1)) (x : α) (p : Fin n -> α) : (Fin.i
nsertNth i x p) ∘ Fin.rev = Fin.insertNth (Fin.rev i) x (p ∘ Fin.rev)
参数：i : Fin (n + 1)；x : α；p : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Fin.insertNth_rev`：insertNth_rev {α : Sort*} (i : Fin (n + 1)) (a : α) (
f : Fin n -> α) (j : Fin (n + 1)) : insertNth (α
-/
theorem insertNth_comp_rev {α} (i : Fin (n + 1)) (x : α) (p : Fin n → α) :
    (Fin.insertNth i x p) ∘ Fin.rev = Fin.insertNth (Fin.rev i) x (p ∘ Fin.rev) := by
  funext x
  apply insertNth_rev

@[simp]
/-
**Fin.insertNth_succ_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_succ_cons {α} (i : Fin (n + 1)) (x a : α) (p : Fin n -> α) : (in
sertNth i.succ x (cons a p) : Fin (n + 2) -> α) = cons a (insertNth i x p)
参数：i : Fin (n + 1)；x a : α；p : Fin n -> α。
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
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用引理 `Fin.succAbove_ne_zero_zero`：succAbove_ne_zero_zero [NeZero n] {a : Fin (
n + 1)} (ha : a != 0) : a.succAbove 0 = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Fin.succ_succAbove_succ`：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), i.succ
.succAbove j.succ = (i.succAbove j).succ
-/
theorem insertNth_succ_cons {α} (i : Fin (n + 1)) (x a : α) (p : Fin n → α) :
    (insertNth i.succ x (cons a p) : Fin (n + 2) → α) = cons a (insertNth i x p) := by
  ext j
  cases j using Fin.succAboveCases i.succ with
  | x => simp
  | p j =>
    simp only [insertNth_apply_succAbove]
    cases j using Fin.cases <;> simp
/-
**Fin.cons_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_rev {α n} (a : α) (f : Fin n -> α) (i : Fin <| n + 1) : cons (α
参数：a : α；f : Fin n -> α；i : Fin <| n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.insertNth_zero'`：insertNth_zero' (x : β) (p : Fin n -> β) : @insertN
th _ (fun _ => β) 0 x p = cons x p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.rev_zero`：∀ (n : ℕ), Fin.rev 0 = Fin.last n
· 使用定理 `Fin.insertNth_last'`：insertNth_last' (x : β) (p : Fin n -> β) : @insertN
th _ (fun _ => β) (last n) x p = snoc p x
· 使用引理 `Fin.insertNth_rev`：insertNth_rev {α : Sort*} (i : Fin (n + 1)) (a : α) (
f : Fin n -> α) (j : Fin (n + 1)) : insertNth (α
-/
theorem cons_rev {α n} (a : α) (f : Fin n → α) (i : Fin <| n + 1) :
    cons (α := fun _ => α) a f i.rev = snoc (α := fun _ => α) (f ∘ Fin.rev : Fin _ → α) a i := by
  simpa using insertNth_rev 0 a f i
/-
**Fin.cons_comp_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：cons_comp_rev {α n} (a : α) (f : Fin n -> α) : Fin.cons a f ∘ Fin.rev = Fi
n.snoc (f ∘ Fin.rev) a
参数：a : α；f : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_rev`：cons_rev {α n} (a : α) (f : Fin n -> α) (i : Fin <| n + 1)
 : cons (α
-/
theorem cons_comp_rev {α n} (a : α) (f : Fin n → α) :
    Fin.cons a f ∘ Fin.rev = Fin.snoc (f ∘ Fin.rev) a := by
  funext i; exact cons_rev ..
/-
**Fin.snoc_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_rev {α n} (a : α) (f : Fin n -> α) (i : Fin <| n + 1) : snoc (α
参数：a : α；f : Fin n -> α；i : Fin <| n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.insertNth_last'`：insertNth_last' (x : β) (p : Fin n -> β) : @insertN
th _ (fun _ => β) (last n) x p = snoc p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.rev_last`：∀ (n : ℕ), (Fin.last n).rev = 0
· 使用定理 `Fin.insertNth_zero'`：insertNth_zero' (x : β) (p : Fin n -> β) : @insertN
th _ (fun _ => β) 0 x p = cons x p
· 使用引理 `Fin.insertNth_rev`：insertNth_rev {α : Sort*} (i : Fin (n + 1)) (a : α) (
f : Fin n -> α) (j : Fin (n + 1)) : insertNth (α
-/
theorem snoc_rev {α n} (a : α) (f : Fin n → α) (i : Fin <| n + 1) :
    snoc (α := fun _ => α) f a i.rev = cons (α := fun _ => α) a (f ∘ Fin.rev : Fin _ → α) i := by
  simpa using insertNth_rev (last n) a f i
/-
**Fin.snoc_comp_rev** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：snoc_comp_rev {α n} (a : α) (f : Fin n -> α) : Fin.snoc f a ∘ Fin.rev = Fi
n.cons a (f ∘ Fin.rev)
参数：a : α；f : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.snoc_rev`：snoc_rev {α n} (a : α) (f : Fin n -> α) (i : Fin <| n + 1)
 : snoc (α
-/
theorem snoc_comp_rev {α n} (a : α) (f : Fin n → α) :
    Fin.snoc f a ∘ Fin.rev = Fin.cons a (f ∘ Fin.rev) :=
  funext <| snoc_rev a f
/-
**Fin.insertNth_binop** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_binop (op : forall j, α j -> α j -> α j) (i : Fin (n + 1)) (x y 
: α i) (p q : forall j, α (i.succAbove j)) : (i.insertNth (op i x y) fun j => op
 _ (p j) (q j)) = fun j => op j (i.insertNth x p j) (i.insertNth y q j)
参数：op : forall j, α j -> α j -> α j；i : Fin (n + 1)；x y : α i；p q : forall j, α 
(i.succAbove j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.insertNth_eq_iff`：insertNth_eq_iff {p : Fin (n + 1)} {a : α p} {f : 
forall i, α (p.succAbove i)} {g : forall j, α j} : insertNth p a f = g ↔ a = g p
 ∧ f = rem…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem insertNth_binop (op : ∀ j, α j → α j → α j) (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    (i.insertNth (op i x y) fun j ↦ op _ (p j) (q j)) = fun j ↦
      op j (i.insertNth x p j) (i.insertNth y q j) :=
  insertNth_eq_iff.2 <| by unfold removeNth; simp

section Preorder

variable {α : Fin (n + 1) → Type*} [∀ i, Preorder (α i)]

/-
**Fin.insertNth_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_le_iff {i : Fin (n + 1)} {x : α i} {p : forall j, α (i.succAbove
 j)} {q : forall j, α j} : i.insertNth x p <= q ↔ x <= q i ∧ p <= fun j => q (i.
succAbove j)
参数：n + 1；i.succAbove j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.forall_iff_succAbove`：forall_iff_succAbove {P : Fin (n + 1) -> Prop}
 (p : Fin (n + 1)) : (forall i, P i) ↔ P p ∧ forall i, P (p.succAbove i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem insertNth_le_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    i.insertNth x p ≤ q ↔ x ≤ q i ∧ p ≤ fun j ↦ q (i.succAbove j) := by
  simp [Pi.le_def, forall_iff_succAbove i]
/-
**Fin.le_insertNth_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：le_insertNth_iff {i : Fin (n + 1)} {x : α i} {p : forall j, α (i.succAbove
 j)} {q : forall j, α j} : q <= i.insertNth x p ↔ q i <= x ∧ (fun j => q (i.succ
Above j)) <= p
参数：n + 1；i.succAbove j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.forall_iff_succAbove`：forall_iff_succAbove {P : Fin (n + 1) -> Prop}
 (p : Fin (n + 1)) : (forall i, P i) ↔ P p ∧ forall i, P (p.succAbove i)
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_insertNth_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    q ≤ i.insertNth x p ↔ q i ≤ x ∧ (fun j ↦ q (i.succAbove j)) ≤ p := by
  simp [Pi.le_def, forall_iff_succAbove i]

end Preorder

open Set

/-
**Fin.removeNth_update** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin (n + 1)) (x : α p) (f : (j
 : Fin (n + 1)) → α j),   p.removeNth (Function.update f p x) = p.removeNth f
参数：n + 1；p : Fin (n + 1)；x : α p；f : (j : Fin (n + 1)) → α j；Function.update f p
 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma removeNth_update (p : Fin (n + 1)) (x) (f : ∀ j, α j) :
    removeNth p (update f p x) = removeNth p f := by ext i; simp [removeNth]

@[simp]
/-
**Fin.removeNth_update_succAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：removeNth_update_succAbove (p : Fin (n + 1)) (i : Fin n) (x : α (p.succAbo
ve i)) (f : forall j, α j) : removeNth p (update f (p.succAbove i) x) = update (
removeNth p f) i x
参数：p : Fin (n + 1)；i : Fin n；x : α (p.succAbove i)；f : forall j, α j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma removeNth_update_succAbove (p : Fin (n + 1)) (i : Fin n) (x : α (p.succAbove i))
    (f : ∀ j, α j) :
    removeNth p (update f (p.succAbove i) x) = update (removeNth p f) i x := by
  ext j
  rcases eq_or_ne j i with rfl | hne <;> simp [removeNth, *]
/-
**Fin.insertNth_removeNth** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin (n + 1)) (x : α p) (f : (j
 : Fin (n + 1)) → α j),   p.insertNth x (p.removeNth f) = Function.update f p x
参数：n + 1；p : Fin (n + 1)；x : α p；f : (j : Fin (n + 1)) → α j；p.removeNth f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.removeNth_update`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin (n
 + 1)) (x : α p) (f : (j : Fin (n + 1)) → α j),   p.removeNth (Function.update f
 p x) = p.…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma insertNth_removeNth (p : Fin (n + 1)) (x) (f : ∀ j, α j) :
    insertNth p x (removeNth p f) = update f p x := by simp [Fin.insertNth_eq_iff]
/-
**Fin.insertNth_self_removeNth** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：insertNth_self_removeNth (p : Fin (n + 1)) (f : forall j, α j) : insertNth
 p (f p) (removeNth p f) = f
参数：p : Fin (n + 1)；f : forall j, α j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNth_removeNth`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin
 (n + 1)) (x : α p) (f : (j : Fin (n + 1)) → α j),   p.insertNth x (p.removeNth 
f) = Function…
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma insertNth_self_removeNth (p : Fin (n + 1)) (f : ∀ j, α j) :
    insertNth p (f p) (removeNth p f) = f := by simp

@[simp]
/-
**Fin.range_insertNth** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：range_insertNth {α : Type*} (p : Fin (n + 1)) (x : α) (f : Fin n -> α) : S
et.range (p.insertNth x f) = Set.insert x (Set.range f)
参数：p : Fin (n + 1)；x : α；f : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Fin.exists_iff_succAbove`：exists_iff_succAbove {P : Fin (n + 1) -> Prop}
 (p : Fin (n + 1)) : (exists i, P i) ↔ P p ∨ exists i, P (p.succAbove i) where m
p
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_insertNth {α : Type*} (p : Fin (n + 1)) (x : α) (f : Fin n → α) :
    Set.range (p.insertNth x f) = Set.insert x (Set.range f) := by
  ext y
  simp [Fin.exists_iff_succAbove p, Set.insert, eq_comm]

@[simp]
/-
**Fin.update_insertNth** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：update_insertNth (p : Fin (n + 1)) (x y : α p) (f : forall i, α (p.succAbo
ve i)) : update (p.insertNth x f) p y = p.insertNth y f
参数：p : Fin (n + 1)；x y : α p；f : forall i, α (p.succAbove i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.removeNth_update`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin (n
 + 1)) (x : α p) (f : (j : Fin (n + 1)) → α j),   p.removeNth (Function.update f
 p x) = p.…
· 使用定理 `Fin.removeNth_insertNth`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin
 (n + 1)) (a : α p) (f : (i : Fin n) → α (p.succAbove i)),   p.removeNth (p.inse
rtNth a f) = …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem update_insertNth (p : Fin (n + 1)) (x y : α p) (f : ∀ i, α (p.succAbove i)) :
    update (p.insertNth x f) p y = p.insertNth y f := by
  simp [eq_insertNth_iff]

@[simp]
/-
**Fin.insertNth_update** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：insertNth_update (p : Fin (n + 1)) (x : α p) (i : Fin n) (y : α (p.succAbo
ve i)) (f : forall j, α (p.succAbove j)) : p.insertNth x (update f i y) = update
 (p.insertNth x f) (p.succAbove i) y
参数：p : Fin (n + 1)；x : α p；i : Fin n；y : α (p.succAbove i)；f : forall j, α (p.su
ccAbove j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Fin.removeNth_update_succAbove`：removeNth_update_succAbove (p : Fin (n +
 1)) (i : Fin n) (x : α (p.succAbove i)) (f : forall j, α j) : removeNth p (upda
te f (p.succAbove i)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.removeNth_insertNth`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin
 (n + 1)) (a : α p) (f : (i : Fin n) → α (p.succAbove i)),   p.removeNth (p.inse
rtNth a f) = …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem insertNth_update (p : Fin (n + 1)) (x : α p) (i : Fin n) (y : α (p.succAbove i))
    (f : ∀ j, α (p.succAbove j)) :
    p.insertNth x (update f i y) = update (p.insertNth x f) (p.succAbove i) y := by
  simp [insertNth_eq_iff]

/-- Equivalence between tuples of length `n + 1` and pairs of an element and a tuple of length `n`
given by separating out the `p`-th element of the tuple.

This is `Fin.insertNth` as an `Equiv`. -/
@[simps]
/-
**Fin.insertNthEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：insertNthEquiv (α : Fin (n + 1) -> Type u) (p : Fin (n + 1)) : α p × (fora
ll i, α (p.succAbove i)) ≃ forall i, α i where toFun f
参数：α : Fin (n + 1) -> Type u；p : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between tuples of length `n + 1` and pairs of an element and a tuple
 of length `n`
given by separating out the `p`-th element of the tuple.

This is `Fin.insertNth` as an `Equiv`.
-/
def insertNthEquiv (α : Fin (n + 1) → Type u) (p : Fin (n + 1)) :
    α p × (∀ i, α (p.succAbove i)) ≃ ∀ i, α i where
  toFun f := insertNth p f.1 f.2
  invFun f := (f p, removeNth p f)
  left_inv f := by ext <;> simp
  right_inv f := by simp
/-
**Fin.insertNthEquiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} (α : Fin (n + 1) → Type u_3), Fin.insertNthEquiv α 0 = Fin.consE
quiv α
参数：α : Fin (n + 1) → Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_bijective`：symm_bijective : Function.Bijective (Equiv.symm : 
(α ≃ β) -> β ≃ α)
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
@[simp] lemma insertNthEquiv_zero (α : Fin (n + 1) → Type*) : insertNthEquiv α 0 = consEquiv α :=
  Equiv.symm_bijective.injective <| by ext <;> rfl

/-- Note this lemma can only be written about non-dependent tuples as `insertNth (last n) = snoc` is
not a definitional equality. -/
/-
**Fin.insertNthEquiv_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ (n : ℕ) (α : Type u_3), Fin.insertNthEquiv (fun x => α) (Fin.last n) = F
in.snocEquiv fun x => α
参数：n : ℕ；α : Type u_3；fun x => α；Fin.last n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNthEquiv_apply`：∀ {n : ℕ} (α : Fin (n + 1) → Type u) (p : Fin 
(n + 1)) (f : α p × ((i : Fin n) → α (p.succAbove i))) (j : Fin (n + 1)),   (Fin
.insertNthEqui…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.insertNth_last'`：insertNth_last' (x : β) (p : Fin n -> β) : @insertN
th _ (fun _ => β) (last n) x p = snoc p x
· 使用定理 `Fin.snocEquiv_apply`：∀ {n : ℕ} (α : Fin (n + 1) → Type u_2) (f : α (Fin.
last n) × ((i : Fin n) → α i.castSucc)) (x : Fin (n + 1)),   (Fin.snocEquiv α) f
 x = Fin.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note this lemma can only be written about non-dependent tuples as `insertNth (la
st n) = snoc` is
not a definitional equality.
-/
@[simp] lemma insertNthEquiv_last (n : ℕ) (α : Type*) :
    insertNthEquiv (fun _ ↦ α) (last n) = snocEquiv (fun _ ↦ α) := by ext; simp

/-- A `HEq` version of `Fin.removeNth_removeNth_eq_swap`. -/
/-
**Fin.removeNth_removeNth_heq_swap** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：removeNth_removeNth_heq_swap {α : Fin (n + 2) -> Sort*} (m : forall i, α i
) (i : Fin (n + 1)) (j : Fin (n + 2)) : i.removeNth (j.removeNth m) ≍ (i.predAbo
ve j).removeNth ((j.succAbove i).removeNth m)
参数：n + 2；m : forall i, α i；i : Fin (n + 1)；j : Fin (n + 2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.hfunext`：hfunext {α α' : Sort u} {β : α -> Sort v} {β' : α' -> 
Sort v} {f : forall a, β a} {f' : forall a, β' a} (hα : α = α') (h : forall a a'
, a ≍ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr_arg_heq`：∀ {α : Sort u_1} {β : α → Sort u_2} (f : (a : α) → β a) {
a₁ a₂ : α}, a₁ = a₂ → f a₁ ≍ f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.succAbove_succAbove_succAbove_predAbove`：succAbove_succAbove_succAbo
ve_predAbove {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (k : Fin n) : (i.succ
Above j).succAbove ((j.predAbove …

--- 原说明 ---
A `HEq` version of `Fin.removeNth_removeNth_eq_swap`.
-/
theorem removeNth_removeNth_heq_swap {α : Fin (n + 2) → Sort*} (m : ∀ i, α i)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    i.removeNth (j.removeNth m) ≍
      (i.predAbove j).removeNth ((j.succAbove i).removeNth m) := by
  apply Function.hfunext rfl
  simp only [heq_iff_eq]
  rintro k _ rfl
  unfold removeNth
  apply congr_arg_heq
  rw [succAbove_succAbove_succAbove_predAbove]

/-- Given an `(n + 2)`-tuple `m` and two indexes `i : Fin (n + 1)` and `j : Fin (n + 2)`,
one can remove `j`th element from `m`, then remove `i`th element from the result,
or one can remove `(j.succAbove i)`th element from `m`,
then remove `(i.predAbove j)`th element from the result.

These two operations correspond to removing the same two elements in a different order,
so they result in the same `n`-tuple. -/
/-
**Fin.removeNth_removeNth_eq_swap** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：removeNth_removeNth_eq_swap {α : Sort*} (m : Fin (n + 2) -> α) (i : Fin (n
 + 1)) (j : Fin (n + 2)) : i.removeNth (j.removeNth m) = (i.predAbove j).removeN
th ((j.succAbove i).removeNth m)
参数：m : Fin (n + 2) -> α；i : Fin (n + 1)；j : Fin (n + 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `heq_iff_eq`：∀ {α : Sort u_1} {a b : α}, a ≍ b ↔ a = b
· 使用定理 `Fin.removeNth_removeNth_heq_swap`：removeNth_removeNth_heq_swap {α : Fin 
(n + 2) -> Sort*} (m : forall i, α i) (i : Fin (n + 1)) (j : Fin (n + 2)) : i.re
moveNth (j.removeNth m…

--- 原说明 ---
Given an `(n + 2)`-tuple `m` and two indexes `i : Fin (n + 1)` and `j : Fin (n +
 2)`,
one can remove `j`th element from `m`, then remove `i`th element from the result
,
or one can remove `(j.succAbove i)`th element from `m`,
then remove `(i.predAbove j)`th element from the result.

These two operations correspond to removing the same two elements in a different
 order,
so they result in the same `n`-tuple.
-/
theorem removeNth_removeNth_eq_swap {α : Sort*} (m : Fin (n + 2) → α)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    i.removeNth (j.removeNth m) = (i.predAbove j).removeNth ((j.succAbove i).removeNth m) :=
  heq_iff_eq.mp (removeNth_removeNth_heq_swap m i j)

end InsertNth

section Find

variable {p q : Fin n → Prop} [DecidablePred p] [DecidablePred q] {i j : Fin n}

set_option backward.privateInPublic true in
/-
**Fin.findX** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def findX {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (h : ∃ k, p k) :
    { i : Fin n // p i ∧ ∀ j < i, ¬ p j } := go n (by grind) where
  go (m : Nat) (hj : ∀ j (hm : j < n - m), ¬p ⟨j, by grind⟩) := match m with
  | m + 1 => if hnm : p ⟨_, n.sub_lt h.choose.pos (by grind)⟩
    then ⟨_, ⟨hnm, (hj ·.val)⟩⟩ else go m (by grind)
  | 0 => absurd h (fun ⟨⟨_, _⟩, _⟩ => by grind)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `Fin.find p h` returns the smallest index `k : Fin n` where `p k` is satisfied,
  given that it is satisfied for some `k`. -/
/-
**Fin.find** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i, p i then so
me (Fin.find (p ·) h) else none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fin.find p h` returns the smallest index `k : Fin n` where `p k` is satisfied,
  given that it is satisfied for some `k`.
-/
protected def find {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (h : ∃ k, p k) : Fin n :=
  (Fin.findX p h).1

/-- `Fin.find p h` satisfies `p`. -/
/-
**Fin.find_spec** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h : ∃ k, p k), p (F
in.find p h)
参数：h : ∃ k, p k；Fin.find p h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
`Fin.find p h` satisfies `p`.
-/
protected theorem find_spec (h : ∃ k, p k) : p (Fin.find p h) := (Fin.findX p h).2.1

grind_pattern Fin.find_spec => Fin.find p h

/-- For `m : Fin n`, if `m < Fin.find p h` then `m` does not satisfy `p`. -/
@[grind →]
/-
**Fin.find_min** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h : ∃ k, p k) {j : 
Fin n}, j < Fin.find p h → ¬p j
参数：h : ∃ k, p k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
For `m : Fin n`, if `m < Fin.find p h` then `m` does not satisfy `p`.
-/
protected theorem find_min (h : ∃ k, p k) : ∀ {j : Fin n}, j < Fin.find p h → ¬ p j :=
  @(Fin.findX p h).2.2

/-- For `m : Fin n`, if `m` satisfies `p`, then `Fin.find p h ≤ m`. -/
/-
**Fin.find_le_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h : ∃ k, p k) {j : 
Fin n}, p j → Fin.find p h ≤ j
参数：h : ∃ k, p k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.mtr`：∀ {a b : Prop}, (¬a → ¬b) → b → a
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `Fin.find_min`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h :
 ∃ k, p k) {j : Fin n}, j < Fin.find p h → ¬p j
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b

--- 原说明 ---
For `m : Fin n`, if `m` satisfies `p`, then `Fin.find p h ≤ m`.
-/
protected theorem find_le_of_pos (h : ∃ k, p k) {j : Fin n} :
    p j → Fin.find p h ≤ j := (j.find_min _ <| lt_of_not_ge ·).mtr
/-
**Fin.find_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：find_eq_iff {i : Fin n} (h : exists k, p k) : Fin.find p h = i ↔ p i ∧ for
all j < i, ¬ p j
参数：h : exists k, p k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `Fin.find_le_of_pos`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p
] (h : ∃ k, p k) {j : Fin n}, p j → Fin.find p h ≤ j
-/
theorem find_eq_iff {i : Fin n} (h : ∃ k, p k) : Fin.find p h = i ↔ p i ∧ ∀ j < i, ¬ p j := by
  refine ⟨?_, fun ⟨hm, hlt⟩ => have := Fin.find_le_of_pos h hm; ?_⟩ <;> grind
/-
**Fin.val_find** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h : ∃ k, p k), ↑(Fi
n.find p h) = Nat.find ⋯
参数：h : ∃ k, p k；Fin.find p h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.exists_iff`：∀ {n : ℕ} {p : Fin n → Prop}, (∃ i, p i) ↔ ∃ i, ∃ (h : i
 < n), p ⟨i, h⟩
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.find_eq_iff`：find_eq_iff (h : exists n : Nat, p n) : Nat.find h = m 
↔ p m ∧ forall n < m, ¬p n
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Fin.find_spec`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h 
: ∃ k, p k), p (Fin.find p h)
· 使用定理 `Fin.find_min`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h :
 ∃ k, p k) {j : Fin n}, j < Fin.find p h → ¬p j
-/
@[simp] theorem val_find (h : ∃ k, p k) :
    (Fin.find p h).val = Nat.find ((Fin.exists_iff.mp h)) :=
  ((Nat.find_eq_iff _).mpr ⟨⟨is_lt _, Fin.find_spec _⟩,
    fun _ hm ⟨_, hi⟩ => Fin.find_min h hm hi⟩).symm
/-
**Fin.find_nat_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：find_nat_lt {p : Nat -> Prop} [DecidablePred p] (h : exists k < n, p k) : 
Nat.find (p
参数：h : exists k < n, p k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.exists_iff`：∀ {n : ℕ} {p : Fin n → Prop}, (∃ i, p i) ↔ ∃ i, ∃ (h : i
 < n), p ⟨i, h⟩
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.val_find`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h :
 ∃ k, p k), ↑(Fin.find p h) = Nat.find ⋯
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `Nat.find_congr`：find_congr [DecidablePred q] {x : Nat} (hx : p x) (hpq :
 forall n <= x, p n ↔ q n) : .1 hx⟩
-/
theorem find_nat_lt {p : ℕ → Prop} [DecidablePred p] (h : ∃ k < n, p k) :
    Nat.find (p := p) (by grind) = Fin.find (n := n) (p ·) (Fin.exists_iff.mpr <| by grind) := by
  rw [val_find]
  have := h.choose_spec; exact Nat.find_congr (x := h.choose) (by grind) (by grind)
/-
**Fin.find_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h : ∃ k, p k) (i : 
Fin n), Fin.find p h < i ↔ ∃ m < i, p m
参数：h : ∃ k, p k；i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Fin.find_le_of_pos`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p
] (h : ∃ k, p k) {j : Fin n}, p j → Fin.find p h ≤ j
-/
@[simp] lemma find_lt_iff (h : ∃ k, p k) (i : Fin n) : Fin.find p h < i ↔ ∃ m < i, p m :=
  ⟨by grind, fun ⟨_, hxi, hx⟩ => (Fin.find_le_of_pos h hx).trans_lt hxi⟩
/-
**Fin.find_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h : ∃ k, p k) (i : 
Fin n), Fin.find p h ≤ i ↔ ∃ m ≤ i, p m
参数：h : ∃ k, p k；i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Fin.find_le_of_pos`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p
] (h : ∃ k, p k) {j : Fin n}, p j → Fin.find p h ≤ j
-/
@[simp] lemma find_le_iff (h : ∃ k, p k) (i : Fin n) : Fin.find p h ≤ i ↔ ∃ m ≤ i, p m :=
  ⟨by grind, fun ⟨_, hxi, hx⟩ => (Fin.find_le_of_pos h hx).trans hxi⟩
/-
**Fin.lt_find_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h : ∃ k, p k) (i : 
Fin n), i < Fin.find p h ↔ ∀ m ≤ i, ¬p m
参数：h : ∃ k, p k；i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma lt_find_iff (h : ∃ k, p k) (i : Fin n) : i < Fin.find p h ↔ ∀ m ≤ i, ¬p m := by
  simp_rw [← not_le, find_le_iff, not_exists, not_and]
/-
**Fin.le_find_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h : ∃ k, p k) (i : 
Fin n), i ≤ Fin.find p h ↔ ∀ m < i, ¬p m
参数：h : ∃ k, p k；i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma le_find_iff (h : ∃ k, p k) (i : Fin n) : i ≤ Fin.find p h ↔ ∀ m < i, ¬p m := by
  simp_rw [← not_lt, find_lt_iff, not_exists, not_and]
/-
**Fin.find_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {p : Fin (n + 1) → Prop} [inst : DecidablePred p] (h : ∃ k, p k)
, Fin.find p h = 0 ↔ p 0
参数：n + 1；h : ∃ k, p k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma find_eq_zero {p : Fin (n + 1) → Prop} [DecidablePred p] (h : ∃ k, p k) :
  Fin.find p h = 0 ↔ p 0 := by simp [find_eq_iff]
/-
**Fin.find_of_not_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：find_of_not_zero {p : Fin (n + 1) -> Prop} [DecidablePred p] (h : exists i
, p i) (h0 : ¬p 0) : Fin.find p h = (Fin.find (fun k => p k.succ) <| (exists_fin
_succ.mp h).resolve_left h0).succ
参数：n + 1；h : exists i, p i；h0 : ¬p 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.exists_fin_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∃ i, P i) ↔ P 
0 ∨ ∃ i, P i.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.find_spec`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h 
: ∃ k, p k), p (Fin.find p h)
· 使用定理 `Fin.find_min`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h :
 ∃ k, p k) {j : Fin n}, j < Fin.find p h → ¬p j
-/
lemma find_of_not_zero {p : Fin (n + 1) → Prop} [DecidablePred p]
    (h : ∃ i, p i) (h0 : ¬p 0) :
    Fin.find p h =
    (Fin.find (fun k => p k.succ) <| (exists_fin_succ.mp h).resolve_left h0).succ := by
  simp_rw [find_eq_iff, forall_fin_succ, h0, not_false_eq_true,
    implies_true, true_and, succ_lt_succ_iff]
  exact ⟨Fin.find_spec (p := fun i => p i.succ) _, fun j => Fin.find_min _⟩
/-
**Fin.find_eq_dite** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：find_eq_dite {p : Fin (n + 1) -> Prop} [DecidablePred p] (h : exists i, p 
i) : Fin.find p h = if h0 : p 0 then 0 else (Fin.find (fun k => p k.succ) <| (ex
ists_fin_succ.mp h).resolve_left h0).succ
参数：n + 1；h : exists i, p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.exists_fin_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∃ i, P i) ↔ P 
0 ∨ ∃ i, P i.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem find_eq_dite {p : Fin (n + 1) → Prop} [DecidablePred p] (h : ∃ i, p i) :
    Fin.find p h = if h0 : p 0 then 0 else
    (Fin.find (fun k => p k.succ) <| (exists_fin_succ.mp h).resolve_left h0).succ := by
  split_ifs
  · grind [find_eq_zero]
  · grind [find_of_not_zero]

/-- If a predicate `q` holds at some `x` and implies `p` up to that `x`, then
the earliest `xq` such that `q xq` is at least the smallest `xp` where `p xp`.
The stronger version of `Fin.find_mono`, since this one needs
implication only up to `Fin.find _` while the other requires `q` implying `p` everywhere. -/
/-
**Fin.find_mono_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：find_mono_of_le (hi : q i) (hpq : forall j <= i, q j -> p j) : Fin.find p 
⟨i, hpq _ le_rfl hi⟩ <= Fin.find q ⟨i, hi⟩
参数：hi : q i；hpq : forall j <= i, q j -> p j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.find_le_of_pos`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p
] (h : ∃ k, p k) {j : Fin n}, p j → Fin.find p h ≤ j
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `Fin.find_spec`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h 
: ∃ k, p k), p (Fin.find p h)

--- 原说明 ---
If a predicate `q` holds at some `x` and implies `p` up to that `x`, then
the earliest `xq` such that `q xq` is at least the smallest `xp` where `p xp`.
The stronger version of `Fin.find_mono`, since this one needs
implication only up to `Fin.find _` while the other requires `q` implying `p` ev
erywhere.
-/
lemma find_mono_of_le (hi : q i) (hpq : ∀ j ≤ i, q j → p j) :
    Fin.find p ⟨i, hpq _ le_rfl hi⟩ ≤ Fin.find q ⟨i, hi⟩ :=
  Fin.find_le_of_pos _ (hpq _ (Fin.find_le_of_pos _ hi) (Fin.find_spec ⟨i, hi⟩))

/-- A weak version of `Fin.find_mono_of_le`, requiring `q` implies `p` everywhere.
-/
/-
**Fin.find_mono** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：find_mono (h : forall i, q i -> p i) {hp : exists i, p i} {hq : exists i, 
q i} : Fin.find p hp <= Fin.find q hq
参数：h : forall i, q i -> p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用引理 `Fin.find_mono_of_le`：find_mono_of_le (hi : q i) (hpq : forall j <= i, q 
j -> p j) : Fin.find p ⟨i, hpq _ le_rfl hi⟩ <= Fin.find q ⟨i, hi⟩

--- 原说明 ---
A weak version of `Fin.find_mono_of_le`, requiring `q` implies `p` everywhere.
-/
lemma find_mono (h : ∀ i, q i → p i) {hp : ∃ i, p i} {hq : ∃ i, q i} :
    Fin.find p hp ≤ Fin.find q hq :=
  let ⟨_, hq⟩ := hq; find_mono_of_le hq fun _ _ ↦ h _

/-- If a predicate `p` holds at some `x` and agrees with `q` up to that `x`, then
their `Fin.find` agree. The stronger version of `Fin.find_congr'`, since this one needs
agreement only up to `Fin.find _` while the other requires `p = q`.
Usage of this lemma will likely be via `obtain ⟨x, hx⟩ := hp; apply Fin.find_congr hx` to unify `q`,
or provide it explicitly with `rw [Fin.find_congr (q := q) hx]`.
-/
/-
**Fin.find_congr** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：find_congr (hi : p i) (hpq : forall j <= i, p j ↔ q j) : .1 hi⟩
参数：hi : p i；hpq : forall j <= i, p j ↔ q j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Fin.find_mono_of_le`：find_mono_of_le (hi : q i) (hpq : forall j <= i, q 
j -> p j) : Fin.find p ⟨i, hpq _ le_rfl hi⟩ <= Fin.find q ⟨i, hi⟩
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
If a predicate `p` holds at some `x` and agrees with `q` up to that `x`, then
their `Fin.find` agree. The stronger version of `Fin.find_congr'`, since this on
e needs
agreement only up to `Fin.find _` while the other requires `p = q`.
Usage of this lemma will likely be via `obtain ⟨x, hx⟩ := hp; apply Fin.find_con
gr hx` to unify `q`,
or provide it explicitly with `rw [Fin.find_congr (q := q) hx]`.
-/
lemma find_congr (hi : p i) (hpq : ∀ j ≤ i, p j ↔ q j) :
    Fin.find p ⟨i, hi⟩ = Fin.find q ⟨i, hpq _ le_rfl |>.1 hi⟩ :=
  le_antisymm (find_mono_of_le (hpq _ le_rfl |>.1 hi) fun _ h ↦ (hpq _ h).mpr)
    (find_mono_of_le hi fun _ h ↦ (hpq _ h).mp)

/-- A weak version of `Fin.find_congr`, requiring `p = q` everywhere. -/
/-
**Fin.find_congr'** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：find_congr' {hp : exists i, p i} {hq : exists i, q i} (hpq : forall {i}, p
 i ↔ q i) : Fin.find p hp = Fin.find q hq
参数：hpq : forall {i}, p i ↔ q i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用引理 `Fin.find_congr`：find_congr (hi : p i) (hpq : forall j <= i, p j ↔ q j) :
 .1 hi⟩

--- 原说明 ---
A weak version of `Fin.find_congr`, requiring `p = q` everywhere.
-/
lemma find_congr' {hp : ∃ i, p i} {hq : ∃ i, q i} (hpq : ∀ {i}, p i ↔ q i) :
    Fin.find p hp = Fin.find q hq :=
  let ⟨_, hp⟩ := hp; find_congr hp fun _ _ ↦ hpq
/-
**Fin.find_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：find_le (hi : p i) : Fin.find p ⟨i, hi⟩ <= i
参数：hi : p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `Fin.find_le_iff`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (
h : ∃ k, p k) (i : Fin n), Fin.find p h ≤ i ↔ ∃ m ≤ i, p m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma find_le (hi : p i) : Fin.find p ⟨i, hi⟩ ≤ i :=
  (Fin.find_le_iff _ _).2 ⟨i, le_refl _, hi⟩
/-
**Fin.find_pos** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：find_pos {p : Fin (n + 1) -> Prop} [DecidablePred p] (h : exists i, p i) :
 0 < Fin.find p h ↔ ¬p 0
参数：n + 1；h : exists i, p i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `Fin.pos_iff_ne_zero`：∀ {n : ℕ} [inst : NeZero n] {a : Fin n}, 0 < a ↔ a 
≠ 0
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.find_eq_zero`：∀ {n : ℕ} {p : Fin (n + 1) → Prop} [inst : DecidablePr
ed p] (h : ∃ k, p k), Fin.find p h = 0 ↔ p 0
-/
lemma find_pos {p : Fin (n + 1) → Prop} [DecidablePred p] (h : ∃ i, p i) :
    0 < Fin.find p h ↔ ¬p 0 := Fin.pos_iff_ne_zero.trans (Fin.find_eq_zero _).not
/-
**Fin.find_of_find_le** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：find_of_find_le {p : Fin (m + n) -> Prop} [DecidablePred p] {hᵢ : exists i
, p i} (hm : m <= Fin.find p hᵢ) : Fin.find p hᵢ = (Fin.find (fun j => p (j.natA
dd m)) ⟨(Fin.cast (Nat.add_comm _ _) (Fin.find p hᵢ)).subNat _ hm, by simp [Fin.
find_spec]⟩).natAdd m
参数：m + n；hm : m <= Fin.find p hᵢ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.find`：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i,
 p i then some (Fin.find (p ·) h) else none
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.natAdd_subNat_cast`：∀ {n m : ℕ} {i : Fin (n + m)} (h : n ≤ ↑i), Fin.
natAdd n (Fin.subNat n (Fin.cast ⋯ i) h) = i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.find_eq_iff`：find_eq_iff {i : Fin n} (h : exists k, p k) : Fin.find 
p h = i ↔ p i ∧ forall j < i, ¬ p j
· 使用定理 `Fin.find_spec`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h 
: ∃ k, p k), p (Fin.find p h)
· 使用定理 `Fin.find_min`：∀ {n : ℕ} {p : Fin n → Prop} [inst : DecidablePred p] (h :
 ∃ k, p k) {j : Fin n}, j < Fin.find p h → ¬p j
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Fin.castAdd_lt`：∀ {m : ℕ} (n : ℕ) (i : Fin m), ↑(Fin.castAdd n i) < m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.natAdd_lt_natAdd_iff`：natAdd_lt_natAdd_iff (m) {i j : Fin n} : natAd
d m i < natAdd m j ↔ i < j
-/
lemma find_of_find_le {p : Fin (m + n) → Prop} [DecidablePred p]
    {hᵢ : ∃ i, p i} (hm : m ≤ Fin.find p hᵢ) :
    Fin.find p hᵢ = (Fin.find (fun j => p (j.natAdd m))
    ⟨(Fin.cast (Nat.add_comm _ _) (Fin.find p hᵢ)).subNat _ hm, by
      simp [Fin.find_spec]⟩).natAdd m := by
  have hⱼ : ∃ j : Fin n, p (j.natAdd m) :=
    ⟨(Fin.cast (Nat.add_comm _ _) (Fin.find p hᵢ)).subNat _ hm, by simp [Fin.find_spec]⟩
  refine (find_eq_iff _).2 ⟨Fin.find_spec hⱼ, fun i hi ↦ ?_⟩
  cases i using addCases with | left i => _ | right i => _
  · exact Fin.find_min hᵢ (Fin.lt_def.mpr <| (Fin.castAdd_lt _ _).trans_le hm)
  · rw [Fin.natAdd_lt_natAdd_iff] at hi
    exact Fin.find_min hⱼ hi
/-
**Fin.find** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i, p i then so
me (Fin.find (p ·) h) else none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem find?_eq_dite {p : Fin n → Bool} :
    find? p = if h : ∃ i, p i then some (Fin.find (p ·) h) else none := by
  split_ifs <;> grind
/-
**Fin.find** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i, p i then so
me (Fin.find (p ·) h) else none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem find?_decide_eq_dite :
    find? (p ·) = if h : ∃ i, p i then some (Fin.find p h) else none := by
  simp_rw [find?_eq_dite, decide_eq_true_eq]
/-
**Fin.get_find** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：get_find?_eq_find_of_eq_true {p : Fin n -> Bool} (h : p i) : (find? p).get
 (isSome_find?_of_eq_true h) = Fin.find (p ·) ⟨i, h⟩
参数：h : p i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_find?_eq_find_of_eq_true {p : Fin n → Bool} (h : p i) :
    (find? p).get (isSome_find?_of_eq_true h) = Fin.find (p ·) ⟨i, h⟩ := by
  simp_rw [find?_eq_dite, Option.get_dite]
/-
**Fin.find** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i, p i then so
me (Fin.find (p ·) h) else none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem find?_decide_get_eq_find (h : ∃ i, p i) :
    (find? (p ·)).get (isSome_find?_of_eq_true (i := h.choose)
    (by simp only [h.choose_spec, decide_true])) = Fin.find p h := by
  simp_rw [find?_decide_eq_dite, Option.get_dite]
/-
**Fin.find_mem_find** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：find_mem_find?_decide (h : exists i, p i) : Fin.find p h in find? p
参数：h : exists i, p i。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem find_mem_find?_decide (h : ∃ i, p i) :
    Fin.find p h ∈ find? p := by grind [find?_eq_dite]

end Find

section Find?

/-
**Fin.mem_find** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：mem_find?_iff {p : Fin n -> Bool} {i : Fin n} : i in find? p ↔ p i ∧ foral
l j, j < i -> ¬ p j
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_find?_iff {p : Fin n → Bool} {i : Fin n} :
    i ∈ find? p ↔ p i ∧ ∀ j, j < i → ¬ p j := by simp
/-
**Fin.find** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i, p i then so
me (Fin.find (p ·) h) else none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem find?_eq_some_find_of_exists {p : Fin n → Bool} (h : ∃ i, p i) :
    find? p = some (Fin.find (p ·) h) := by simp_rw [find?_eq_dite, h, dite_true]
/-
**Fin.find** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：find?_eq_dite {p : Fin n -> Bool} : find? p = if h : exists i, p i then so
me (Fin.find (p ·) h) else none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem find?_eq_some_find_of_isSome {p : Fin n → Bool} (h : (find? p).isSome) :
    find? p = some (Fin.find (p ·) (exists_eq_true_of_isSome_find? h)) := by
  simp_rw [find?_eq_dite, exists_eq_true_of_isSome_find? h, dite_true]

end Find?

section ContractNth

variable {α : Sort*}

/-- Sends `(g₀, ..., gₙ)` to `(g₀, ..., op gⱼ gⱼ₊₁, ..., gₙ)`. -/
/-
**Fin.contractNth** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：contractNth (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n + 1) -> α) (k
 : Fin n) : α
参数：j : Fin (n + 1)；op : α -> α -> α；g : Fin (n + 1) -> α；k : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sends `(g₀, ..., gₙ)` to `(g₀, ..., op gⱼ gⱼ₊₁, ..., gₙ)`.
-/
def contractNth (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n) : α :=
  if (k : ℕ) < j then g (Fin.castSucc k)
  else if (k : ℕ) = j then op (g (Fin.castSucc k)) (g k.succ) else g k.succ
/-
**Fin.contractNth_apply_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：contractNth_apply_of_lt (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n +
 1) -> α) (k : Fin n) (h : (k : Nat) < j) : contractNth j op g k = g (Fin.castSu
cc k)
参数：j : Fin (n + 1)；op : α -> α -> α；g : Fin (n + 1) -> α；k : Fin n；h : (k : Nat)
 < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem contractNth_apply_of_lt (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (k : ℕ) < j) : contractNth j op g k = g (Fin.castSucc k) :=
  if_pos h
/-
**Fin.contractNth_apply_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：contractNth_apply_of_eq (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n +
 1) -> α) (k : Fin n) (h : (k : Nat) = j) : contractNth j op g k = op (g (Fin.ca
stSucc k)) (g k.succ)
参数：j : Fin (n + 1)；op : α -> α -> α；g : Fin (n + 1) -> α；k : Fin n；h : (k : Nat)
 = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.contractNth.eq_1`：∀ {n : ℕ} {α : Sort u_1} (j : Fin (n + 1)) (op : α
 → α → α) (g : Fin (n + 1) → α) (k : Fin n),   j.contractNth op g k = if ↑k < ↑j
 then g k.…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem contractNth_apply_of_eq (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (k : ℕ) = j) : contractNth j op g k = op (g (Fin.castSucc k)) (g k.succ) := by
  have : ¬(k : ℕ) < j := not_lt.2 (le_of_eq h.symm)
  rw [contractNth, if_neg this, if_pos h]
/-
**Fin.contractNth_apply_of_gt** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：contractNth_apply_of_gt (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n +
 1) -> α) (k : Fin n) (h : (j : Nat) < k) : contractNth j op g k = g k.succ
参数：j : Fin (n + 1)；op : α -> α -> α；g : Fin (n + 1) -> α；k : Fin n；h : (j : Nat)
 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.contractNth.eq_1`：∀ {n : ℕ} {α : Sort u_1} (j : Fin (n + 1)) (op : α
 → α → α) (g : Fin (n + 1) → α) (k : Fin n),   j.contractNth op g k = if ↑k < ↑j
 then g k.…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
theorem contractNth_apply_of_gt (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (j : ℕ) < k) : contractNth j op g k = g k.succ := by
  rw [contractNth, if_neg (not_lt_of_gt h), if_neg (Ne.symm <| ne_of_lt h)]
/-
**Fin.contractNth_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：contractNth_apply_of_ne (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n +
 1) -> α) (k : Fin n) (hjk : (j : Nat) != k) : contractNth j op g k = g (j.succA
bove k)
参数：j : Fin (n + 1)；op : α -> α -> α；g : Fin (n + 1) -> α；k : Fin n；hjk : (j : Na
t) != k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Fin.lt_def`：∀ {n : ℕ} {a b : Fin n}, a < b ↔ ↑a < ↑b
· 使用定理 `Fin.contractNth_apply_of_lt`：contractNth_apply_of_lt (j : Fin (n + 1)) (
op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) (h : (k : Nat) < j) : contr
actNth j op g k =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.le_iff_val_le_val`：le_iff_val_le_val {a b : Fin n} : a <= b ↔ (a : N
at) <= b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fin.contractNth_apply_of_gt`：contractNth_apply_of_gt (j : Fin (n + 1)) (
op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) (h : (j : Nat) < k) : contr
actNth j op g k =…
-/
theorem contractNth_apply_of_ne (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (hjk : (j : ℕ) ≠ k) : contractNth j op g k = g (j.succAbove k) := by
  rcases lt_trichotomy (k : ℕ) j with (h | h | h)
  · rwa [j.succAbove_of_castSucc_lt, contractNth_apply_of_lt]
    · rwa [Fin.lt_def]
  · exact False.elim (hjk h.symm)
  · rwa [j.succAbove_of_le_castSucc, contractNth_apply_of_gt]
    · exact Fin.le_iff_val_le_val.2 (le_of_lt h)
/-
**Fin.comp_contractNth** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：comp_contractNth {β : Sort*} (opα : α -> α -> α) (opβ : β -> β -> β) {f : 
α -> β} (hf : forall x y, f (opα x y) = opβ (f x) (f y)) (j : Fin (n + 1)) (g : 
Fin (n + 1) -> α) : f ∘ contractNth j opα g = contractNth j opβ (f ∘ g)
参数：opα : α -> α -> α；opβ : β -> β -> β；hf : forall x y, f (opα x y) = opβ (f x) 
(f y)；j : Fin (n + 1)；g : Fin (n + 1) -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.contractNth_apply_of_lt`：contractNth_apply_of_lt (j : Fin (n + 1)) (
op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) (h : (k : Nat) < j) : contr
actNth j op g k =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.contractNth_apply_of_eq`：contractNth_apply_of_eq (j : Fin (n + 1)) (
op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) (h : (k : Nat) = j) : contr
actNth j op g k =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.contractNth_apply_of_gt`：contractNth_apply_of_gt (j : Fin (n + 1)) (
op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) (h : (j : Nat) < k) : contr
actNth j op g k =…
-/
lemma comp_contractNth {β : Sort*} (opα : α → α → α) (opβ : β → β → β) {f : α → β}
    (hf : ∀ x y, f (opα x y) = opβ (f x) (f y)) (j : Fin (n + 1)) (g : Fin (n + 1) → α) :
    f ∘ contractNth j opα g = contractNth j opβ (f ∘ g) := by
  ext x
  rcases lt_trichotomy (x : ℕ) j with (h | h | h)
  · simp only [Function.comp_apply, contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, contractNth_apply_of_eq, h, hf]
  · simp only [Function.comp_apply, contractNth_apply_of_gt, h]

end ContractNth

/-- To show two sigma pairs of tuples agree, it to show the second elements are related via
`Fin.cast`. -/
/-
**Fin.sigma_eq_of_eq_comp_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {α : Type u_1} {a b : (ii : ℕ) × (Fin ii → α)} (h : a.fst = b.fst), a.sn
d = b.snd ∘ Fin.cast h → a = b
参数：ii : ℕ；Fin ii → α；h : a.fst = b.fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Fin.cast_refl`：∀ (n : ℕ) (h : n = n), Fin.cast h = id

--- 原说明 ---
To show two sigma pairs of tuples agree, it to show the second elements are rela
ted via
`Fin.cast`.
-/
theorem sigma_eq_of_eq_comp_cast {α : Type*} :
    ∀ {a b : Σ ii, Fin ii → α} (h : a.fst = b.fst), a.snd = b.snd ∘ Fin.cast h → a = b
  | ⟨ai, a⟩, ⟨bi, b⟩, hi, h => by
    dsimp only at hi
    subst hi
    simpa using h

/-- `Fin.sigma_eq_of_eq_comp_cast` as an `iff`. -/
/-
**Fin.sigma_eq_iff_eq_comp_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：sigma_eq_iff_eq_comp_cast {α : Type*} {a b : Σ ii, Fin ii -> α} : a = b ↔ 
exists h : a.fst = b.fst, a.snd = b.snd ∘ Fin.cast h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.sigma_eq_of_eq_comp_cast`：∀ {α : Type u_1} {a b : (ii : ℕ) × (Fin ii
 → α)} (h : a.fst = b.fst), a.snd = b.snd ∘ Fin.cast h → a = b

--- 原说明 ---
`Fin.sigma_eq_of_eq_comp_cast` as an `iff`.
-/
theorem sigma_eq_iff_eq_comp_cast {α : Type*} {a b : Σ ii, Fin ii → α} :
    a = b ↔ ∃ h : a.fst = b.fst, a.snd = b.snd ∘ Fin.cast h :=
  ⟨fun h ↦ h ▸ ⟨rfl, funext <| Fin.rec fun _ _ ↦ rfl⟩, fun ⟨_, h'⟩ ↦
    sigma_eq_of_eq_comp_cast _ h'⟩

end Fin

/-- `Π i : Fin 2, α i` is equivalent to `α 0 × α 1`. See also `finTwoArrowEquiv` for a
non-dependent version and `prodEquivPiFinTwo` for a version with inputs `α β : Type u`. -/
@[simps -fullyApplied]
/-
**piFinTwoEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：piFinTwoEquiv (α : Fin 2 -> Type u) : (forall i, α i) ≃ α 0 × α 1 where to
Fun f
参数：α : Fin 2 -> Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Π i : Fin 2, α i` is equivalent to `α 0 × α 1`. See also `finTwoArrowEquiv` for
 a
non-dependent version and `prodEquivPiFinTwo` for a version with inputs `α β : T
ype u`.
-/
def piFinTwoEquiv (α : Fin 2 → Type u) : (∀ i, α i) ≃ α 0 × α 1 where
  toFun f := (f 0, f 1)
  invFun p := Fin.cons p.1 <| Fin.cons p.2 finZeroElim
  left_inv _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
