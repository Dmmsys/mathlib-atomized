/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Tactic.Common

/-!
The type `List.Vector` represents lists with fixed length.

TODO: The API of `List.Vector` is quite incomplete relative to `Vector`,
and in particular does not use `x[i]` (that is `GetElem` notation) as the preferred accessor.
Any combination of reducing the use of `List.Vector` in Mathlib, or modernising its API,
would be welcome.
-/

@[expose] public section

assert_not_exists Monoid

universe u v w
/--
`List.Vector α n` is the type of lists of length `n` with elements of type `α`.

Note that there is also `Vector α n` in the root namespace,
which is the type of *arrays* of length `n` with elements of type `α`.

Typically, if you are doing programming or verification, you will primarily use `Vector α n`,
and if you are doing mathematics, you may want to use `List.Vector α n` instead.
-/
/-
**List.Vector** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：List.Vector (α : Type u) (n : Nat)
参数：α : Type u；n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`List.Vector α n` is the type of lists of length `n` with elements of type `α`.

Note that there is also `Vector α n` in the root namespace,
which is the type of *arrays* of length `n` with elements of type `α`.

Typically, if you are doing programming or verification, you will primarily use 
`Vector α n`,
and if you are doing mathematics, you may want to use `List.Vector α n` instead.
-/
def List.Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }

namespace List.Vector

variable {α β σ φ : Type*} {n : ℕ} {p : α → Prop}

/-
**List.Vector.** 是 Mathlib 中的一个实例，位于命名空间 `List.Vector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] : DecidableEq (Vector α n) :=
  inferInstanceAs (DecidableEq {l : List α // l.length = n})

/-- The empty vector with elements of type `α` -/
@[match_pattern]
/-
**List.Vector.nil** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：nil : Vector α 0
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty vector with elements of type `α`
-/
def nil : Vector α 0 :=
  ⟨[], rfl⟩

/-- If `a : α` and `l : Vector α n`, then `cons a l`, is the vector of length `n + 1`
whose first element is a and with l as the rest of the list. -/
@[match_pattern]
/-
**List.Vector.cons** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {n : ℕ} → α → List.Vector α n → List.Vector α n.succ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a : α` and `l : Vector α n`, then `cons a l`, is the vector of length `n + 1
`
whose first element is a and with l as the rest of the list.
-/
def cons : α → Vector α n → Vector α (Nat.succ n)
  | a, ⟨v, h⟩ => ⟨a :: v, congrArg Nat.succ h⟩


/-- The length of a vector. -/
@[reducible, nolint unusedArguments]
/-
**List.Vector.length** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：length (_ : Vector α n) : Nat
参数：_ : Vector α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of a vector.
-/
def length (_ : Vector α n) : ℕ :=
  n

open Nat

/-- The first element of a vector with length at least `1`. -/
/-
**List.Vector.head** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {n : ℕ} → List.Vector α n.succ → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first element of a vector with length at least `1`.
-/
def head : Vector α (Nat.succ n) → α
  | ⟨a :: _, _⟩ => a

/-- The head of a vector obtained by prepending is the element prepended. -/
@[simp, grind =]
/-
**List.Vector.head_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector α n), (a ::ᵥ v).head = a
参数：a : α；v : List.Vector α n；a ::ᵥ v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The head of a vector obtained by prepending is the element prepended.
-/
theorem head_cons (a : α) : ∀ v : Vector α n, head (cons a v) = a
  | ⟨_, _⟩ => rfl

/-- The tail of a vector, with an empty vector having empty tail. -/
/-
**List.Vector.tail** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {n : ℕ} → List.Vector α n → List.Vector α (n - 1)
参数：n - 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tail of a vector, with an empty vector having empty tail.
-/
def tail : Vector α n → Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congrArg pred h⟩
  | ⟨_ :: v, h⟩ => ⟨v, congrArg pred h⟩

/-- The tail of a vector obtained by prepending is the vector prepended. to -/
@[simp, grind =]
/-
**List.Vector.tail_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector α n), (a ::ᵥ v).tail = v
参数：a : α；v : List.Vector α n；a ::ᵥ v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tail of a vector obtained by prepending is the vector prepended. to
-/
theorem tail_cons (a : α) : ∀ v : Vector α n, tail (cons a v) = v
  | ⟨_, _⟩ => rfl

/-- Prepending the head of a vector to its tail gives the vector. -/
@[simp]
/-
**List.Vector.cons_head_tail** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n.succ), v.head ::ᵥ v.tail = v
参数：v : List.Vector α n.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
Prepending the head of a vector to its tail gives the vector.
-/
theorem cons_head_tail : ∀ v : Vector α (succ n), cons (head v) (tail v) = v
  | ⟨[], h⟩ => by contradiction
  | ⟨_ :: _, _⟩ => rfl

/-- The list obtained from a vector. -/
/-
**List.Vector.toList** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：toList (v : Vector α n) : List α
参数：v : Vector α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The list obtained from a vector.
-/
def toList (v : Vector α n) : List α :=
  v.1

/-- nth element of a vector, indexed by a `Fin` type. -/
/-
**List.Vector.get** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：get (l : Vector α n) (i : Fin n) : α
参数：l : Vector α n；i : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
nth element of a vector, indexed by a `Fin` type.
-/
def get (l : Vector α n) (i : Fin n) : α :=
  l.1.get <| i.cast l.2.symm
/-
**List.Vector.** 是 Mathlib 中的一个实例，位于命名空间 `List.Vector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n m : Nat} : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) where
  hAppend | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩
/-
**List.Vector.append_def** 是 Mathlib 中的一个引理，位于命名空间 `List.Vector`。
形式化陈述：append_def {n m : Nat} : (HAppend.hAppend : Vector α n -> Vector α m -> Ve
ctor α (n + m)) = fun | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma append_def {n m : Nat} :
    (HAppend.hAppend : Vector α n → Vector α m → Vector α (n + m)) =
      fun | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩ :=
  rfl

/-- Elimination rule for `Vector`. -/
@[elab_as_elim]
/-
**List.Vector.elim** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_5} →   {C : {n : ℕ} → List.Vector α n → Sort u} → ((l : List α
) → C ⟨l, ⋯⟩) → {n : ℕ} → (v : List.Vector α n) → C v
参数：(l : List α) → C ⟨l, ⋯⟩；v : List.Vector α n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elimination rule for `Vector`.
-/
def elim {α} {C : ∀ {n}, Vector α n → Sort u}
    (H : ∀ l : List α, C ⟨l, rfl⟩) {n : ℕ} : ∀ v : Vector α n, C v
  | ⟨l, h⟩ =>
    match n, h with
    | _, rfl => H l

/-- Map a vector under a function. -/
/-
**List.Vector.map** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {n : ℕ} → (α → β) → List.Vector α n → Li
st.Vector β n
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a vector under a function.
-/
def map (f : α → β) : Vector α n → Vector β n
  | ⟨l, h⟩ => ⟨List.map f l, by simp [*]⟩

/-- A `nil` vector maps to a `nil` vector. -/
@[simp]
/-
**List.Vector.map_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：map_nil (f : α -> β) : map f nil = nil
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `nil` vector maps to a `nil` vector.
-/
theorem map_nil (f : α → β) : map f nil = nil :=
  rfl

/-- `map` is natural with respect to `cons`. -/
@[simp]
/-
**List.Vector.map_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} (f : α → β) (a : α) (v : List.Vect
or α n),   List.Vector.map f (a ::ᵥ v) = f a ::ᵥ List.Vector.map f v
参数：f : α → β；a : α；v : List.Vector α n；a ::ᵥ v。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map` is natural with respect to `cons`.
-/
theorem map_cons (f : α → β) (a : α) : ∀ v : Vector α n, map f (cons a v) = cons (f a) (map f v)
  | ⟨_, _⟩ => rfl

set_option backward.isDefEq.respectTransparency false in
/-- Map a vector under a partial function. -/
/-
**List.Vector.pmap** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {n : ℕ} → {p : α → Prop} → ((a : α
) → p a → β) → (v : List.Vector α n) → (∀ x ∈ v.toList, p x) → List.Vector β n
参数：(a : α) → p a → β；v : List.Vector α n；∀ x ∈ v.toList, p x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a vector under a partial function.
-/
def pmap (f : (a : α) → p a → β) :
    (v : Vector α n) → (∀ x ∈ v.toList, p x) → Vector β n
  | ⟨l, h⟩, hp => ⟨List.pmap f l hp, by simp [h]⟩

@[simp]
/-
**List.Vector.pmap_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：pmap_nil (f : (a : α) -> p a -> β) (hp : forall x in nil.toList, p x) : ni
l.pmap f hp = nil
参数：f : (a : α) -> p a -> β；hp : forall x in nil.toList, p x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pmap_nil (f : (a : α) → p a → β) (hp : ∀ x ∈ nil.toList, p x) :
    nil.pmap f hp = nil := rfl

/-- Mapping two vectors under a curried function of two variables. -/
/-
**List.Vector.map** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {n : ℕ} → (α → β) → List.Vector α n → Li
st.Vector β n
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping two vectors under a curried function of two variables.
-/
def map₂ (f : α → β → φ) : Vector α n → Vector β n → Vector φ n
  | ⟨x, _⟩, ⟨y, _⟩ => ⟨List.zipWith f x y, by simp [*]⟩

/-- Vector obtained by repeating an element. -/
/-
**List.Vector.replicate** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：replicate (n : Nat) (a : α) : Vector α n
参数：n : Nat；a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n

--- 原说明 ---
Vector obtained by repeating an element.
-/
def replicate (n : ℕ) (a : α) : Vector α n :=
  ⟨List.replicate n a, List.length_replicate⟩

/-- Drop `i` elements from a vector of length `n`; we can have `i > n`. -/
/-
**List.Vector.drop** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {n : ℕ} → (i : ℕ) → List.Vector α n → List.Vector α (n - 
i)
参数：i : ℕ；n - i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Drop `i` elements from a vector of length `n`; we can have `i > n`.
-/
def drop (i : ℕ) : Vector α n → Vector α (n - i)
  | ⟨l, p⟩ => ⟨List.drop i l, by simp [*]⟩

/-- Take `i` elements from a vector of length `n`; we can have `i > n`. -/
/-
**List.Vector.take** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {n : ℕ} → (i : ℕ) → List.Vector α n → List.Vector α (min 
i n)
参数：i : ℕ；min i n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take `i` elements from a vector of length `n`; we can have `i > n`.
-/
def take (i : ℕ) : Vector α n → Vector α (min i n)
  | ⟨l, p⟩ => ⟨List.take i l, by simp [*]⟩

/-- Remove the element at position `i` from a vector of length `n`. -/
/-
**List.Vector.eraseIdx** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {n : ℕ} → Fin n → List.Vector α n → List.Vector α (n - 1)
参数：n - 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Remove the element at position `i` from a vector of length `n`.
-/
def eraseIdx (i : Fin n) : Vector α n → Vector α (n - 1)
  | ⟨l, p⟩ => ⟨List.eraseIdx l i.1, by rw [l.length_eraseIdx_of_lt] <;> rw [p]; exact i.2⟩

/-- Vector of length `n` from a function on `Fin n`. -/
/-
**List.Vector.ofFn** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {n : ℕ} → (Fin n → α) → List.Vector α n
参数：Fin n → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vector of length `n` from a function on `Fin n`.
-/
def ofFn : ∀ {n}, (Fin n → α) → Vector α n
  | 0, _ => nil
  | _ + 1, f => cons (f 0) (ofFn fun i ↦ f i.succ)

/-- Create a vector from another with a provably equal length. -/
/-
**List.Vector.congr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {n m : ℕ} → n = m → List.Vector α n → List.Vector α m
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a vector from another with a provably equal length.
-/
protected def congr {n m : ℕ} (h : n = m) : Vector α n → Vector α m
  | ⟨x, p⟩ => ⟨x, h ▸ p⟩

section Accum

open Prod

/-- Runs a function over a vector returning the intermediate results and a
final result.
-/
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Runs a function over a vector returning the intermediate results and a
final result.
-/
def mapAccumr (f : α → σ → σ × β) : Vector α n → σ → σ × Vector β n
  | ⟨x, px⟩, c =>
    let res := List.mapAccumr f x c
    ⟨res.1, res.2, by simp [*, res]⟩

/-- Runs a function over a pair of vectors returning the intermediate results and a
final result.
-/
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Runs a function over a pair of vectors returning the intermediate results and a
final result.
-/
def mapAccumr₂ (f : α → β → σ → σ × φ) : Vector α n → Vector β n → σ → σ × Vector φ n
  | ⟨x, px⟩, ⟨y, py⟩, c =>
    let res := List.mapAccumr₂ f x y c
    ⟨res.1, res.2, by simp [*, res]⟩

end Accum

/-! ### Shift Primitives -/
section Shift

/-- `shiftLeftFill v i` is the vector obtained by left-shifting `v` `i` times and padding with the
    `fill` argument. If `v.length < i` then this will return `replicate n fill`. -/
/-
**List.Vector.shiftLeftFill** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：shiftLeftFill (v : Vector α n) (i : Nat) (fill : α) : Vector α n
参数：v : Vector α n；i : Nat；fill : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`shiftLeftFill v i` is the vector obtained by left-shifting `v` `i` times and pa
dding with the
    `fill` argument. If `v.length < i` then this will return `replicate n fill`.
-/
def shiftLeftFill (v : Vector α n) (i : ℕ) (fill : α) : Vector α n :=
  Vector.congr (by simp) (drop i v ++ replicate (min n i) fill)

/-- `shiftRightFill v i` is the vector obtained by right-shifting `v` `i` times and padding with the
    `fill` argument. If `v.length < i` then this will return `replicate n fill`. -/
/-
**List.Vector.shiftRightFill** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：shiftRightFill (v : Vector α n) (i : Nat) (fill : α) : Vector α n
参数：v : Vector α n；i : Nat；fill : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`shiftRightFill v i` is the vector obtained by right-shifting `v` `i` times and 
padding with the
    `fill` argument. If `v.length < i` then this will return `replicate n fill`.
-/
def shiftRightFill (v : Vector α n) (i : ℕ) (fill : α) : Vector α n :=
  Vector.congr (by omega) (replicate (min n i) fill ++ take (n - i) v)

end Shift


/-! ### Basic Theorems -/
/-- Vector is determined by the underlying list. -/
/-
**List.Vector.eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (a1 a2 : List.Vector α n), a1.toList = a2.toList 
→ a1 = a2
参数：a1 a2 : List.Vector α n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vector is determined by the underlying list.
-/
protected theorem eq {n : ℕ} : ∀ a1 a2 : Vector α n, toList a1 = toList a2 → a1 = a2
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- A vector of length `0` is a `nil` vector. -/
/-
**List.Vector.eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} (v : List.Vector α 0), v = List.Vector.nil
参数：v : List.Vector α 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.eq`：∀ {α : Type u_1} {n : ℕ} (a1 a2 : List.Vector α n), a1.t
oList = a2.toList → a1 = a2
· 使用定理 `List.eq_nil_of_length_eq_zero`：∀ {α : Type u_1} {l : List α}, l.length =
 0 → l = []
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
A vector of length `0` is a `nil` vector.
-/
protected theorem eq_nil (v : Vector α 0) : v = nil :=
  v.eq nil (List.eq_nil_of_length_eq_zero v.2)

/-- Vector of length from a list `v`
with witness that `v` has length `n` maps to `v` under `toList`. -/
@[simp]
/-
**List.Vector.toList_mk** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_mk (v : List α) (P : List.length v = n) : toList (Subtype.mk v P) =
 v
参数：v : List α；P : List.length v = n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vector of length from a list `v`
with witness that `v` has length `n` maps to `v` under `toList`.
-/
theorem toList_mk (v : List α) (P : List.length v = n) : toList (Subtype.mk v P) = v :=
  rfl

/-- A nil vector maps to a nil list. -/
@[simp]
/-
**List.Vector.toList_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_nil : toList nil = @List.nil α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nil vector maps to a nil list.
-/
theorem toList_nil : toList nil = @List.nil α :=
  rfl

/-- The length of the list to which a vector of length `n` maps is `n`. -/
@[simp]
/-
**List.Vector.toList_length** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_length (v : Vector α n) : (toList v).length = n
参数：v : Vector α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The length of the list to which a vector of length `n` maps is `n`.
-/
theorem toList_length (v : Vector α n) : (toList v).length = n :=
  v.2

/-- `toList` of `cons` of a vector and an element is
the `cons` of the list obtained by `toList` and the element -/
@[simp]
/-
**List.Vector.toList_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_cons (a : α) (v : Vector α n) : toList (cons a v) = a :: toList v
参数：a : α；v : Vector α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`toList` of `cons` of a vector and an element is
the `cons` of the list obtained by `toList` and the element
-/
theorem toList_cons (a : α) (v : Vector α n) : toList (cons a v) = a :: toList v := by
  cases v; rfl

/-- Appending of vectors corresponds under `toList` to appending of lists. -/
@[simp]
/-
**List.Vector.toList_append** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_append {n m : Nat} (v : Vector α n) (w : Vector α m) : toList (v ++
 w) = toList v ++ toList w
参数：v : Vector α n；w : Vector α m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Appending of vectors corresponds under `toList` to appending of lists.
-/
theorem toList_append {n m : ℕ} (v : Vector α n) (w : Vector α m) :
    toList (v ++ w) = toList v ++ toList w := rfl

/-- `drop` of vectors corresponds under `toList` to `drop` of lists. -/
@[simp]
/-
**List.Vector.toList_drop** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_drop {n m : Nat} (v : Vector α m) : toList (drop n v) = List.drop n
 (toList v)
参数：v : Vector α m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`drop` of vectors corresponds under `toList` to `drop` of lists.
-/
theorem toList_drop {n m : ℕ} (v : Vector α m) : toList (drop n v) = List.drop n (toList v) := by
  cases v
  rfl

/-- `take` of vectors corresponds under `toList` to `take` of lists. -/
@[simp]
/-
**List.Vector.toList_take** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_take {n m : Nat} (v : Vector α m) : toList (take n v) = List.take n
 (toList v)
参数：v : Vector α m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`take` of vectors corresponds under `toList` to `take` of lists.
-/
theorem toList_take {n m : ℕ} (v : Vector α m) : toList (take n v) = List.take n (toList v) := by
  cases v
  rfl
/-
**List.Vector.** 是 Mathlib 中的一个实例，位于命名空间 `List.Vector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GetElem (Vector α n) Nat α fun _ i => i < n where
  getElem := fun x i h => get x ⟨i, h⟩
/-
**List.Vector.getElem_def** 是 Mathlib 中的一个引理，位于命名空间 `List.Vector`。
形式化陈述：getElem_def (v : Vector α n) (i : Nat) {hi : i < n} : v[i] = v.toList[i]'(
by simpa)
参数：v : Vector α n；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma getElem_def (v : Vector α n) (i : ℕ) {hi : i < n} :
    v[i] = v.toList[i]'(by simpa) := rfl
/-
**List.Vector.toList_getElem** 是 Mathlib 中的一个引理，位于命名空间 `List.Vector`。
形式化陈述：toList_getElem (v : Vector α n) (i : Nat) {hi : i < v.toList.length} : v.t
oList[i] = v[i]'(by simp_all)
参数：v : Vector α n；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toList_getElem (v : Vector α n) (i : ℕ) {hi : i < v.toList.length} :
    v.toList[i] = v[i]'(by simp_all) := rfl

end List.Vector

