/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Lists from functions

Theorems and lemmas for dealing with `List.ofFn`, which converts a function on `Fin n` to a list
of length `n`.

## Main Statements

The main statements pertain to lists generated using `List.ofFn`

- `List.get?_ofFn`, which tells us the nth element of such a list
- `List.equivSigmaTuple`, which is an `Equiv` between lists and the functions that generate them
  via `List.ofFn`.
-/

@[expose] public section

assert_not_exists Monoid

universe u

variable {α : Type u}

open Nat

namespace List

/-
**List.get_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i = f (Fin.cast (by simp)
 i)
参数：f : Fin n -> α；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
-/
theorem get_ofFn {n} (f : Fin n → α) (i) : get (ofFn f) i = f (Fin.cast (by simp) i) := by
  simp; congr

/-- Useful if `rw [← map_ofFn]` complains that `g ∘ f` is not the same as `fun i => g (f i)`. -/
/-
**List.ofFn_comp'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_comp' {β : Type*} {n : Nat} (f : Fin n -> α) (g : α -> β) : ofFn (fun
 i => g (f i)) = map g (ofFn f)
参数：f : Fin n -> α；g : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_ofFn`：∀ {n : ℕ} {α : Type u_1} {β : Type u_2} {f : Fin n → α} {
g : α → β}, List.map g (List.ofFn f) = List.ofFn (g ∘ f)

--- 原说明 ---
Useful if `rw [← map_ofFn]` complains that `g ∘ f` is not the same as `fun i => 
g (f i)`.
-/
theorem ofFn_comp' {β : Type*} {n : ℕ} (f : Fin n → α) (g : α → β) :
    ofFn (fun i => g (f i)) = map g (ofFn f) :=
  map_ofFn.symm

@[congr]
/-
**List.ofFn_congr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_congr {m n : Nat} (h : m = n) (f : Fin m -> α) : ofFn f = ofFn fun i 
: Fin n => f (Fin.cast h.symm i)
参数：h : m = n；f : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.cast_refl`：∀ (n : ℕ) (h : n = n), Fin.cast h = id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFn_congr {m n : ℕ} (h : m = n) (f : Fin m → α) :
    ofFn f = ofFn fun i : Fin n => f (Fin.cast h.symm i) := by
  subst h
  simp_rw [Fin.cast_refl, id]
/-
**List.ofFn_succ'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_succ' {n} (f : Fin (succ n) -> α) : ofFn f = (ofFn fun i => f (Fin.ca
stSucc i)).concat (f (Fin.last _))
参数：f : Fin (succ n) -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `List.concat_nil`：∀ {α : Type u_1} {a : α}, [].concat a = [a]
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
· 使用定理 `Fin.last_zero`：Fin.last 0 = 0
· 使用定理 `List.concat_cons`：∀ {α : Type u_1} {a b : α} {l : List α}, (a :: l).conc
at b = a :: l.concat b
· 使用定理 `Fin.castSucc_zero`：∀ {n : ℕ} [inst : NeZero n], Fin.castSucc 0 = 0
· 使用定理 `Fin.succ_last`：∀ (n : ℕ), (Fin.last n).succ = Fin.last n.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFn_succ' {n} (f : Fin (succ n) → α) :
    ofFn f = (ofFn fun i => f (Fin.castSucc i)).concat (f (Fin.last _)) := by
  induction n with
  | zero => rw [ofFn_zero, concat_nil, ofFn_succ, ofFn_zero, Fin.last_zero]
  | succ n IH =>
    rw [ofFn_succ, IH, ofFn_succ, concat_cons, Fin.castSucc_zero, Fin.succ_last]
    simp only [succ_eq_add_one, Fin.castSucc_succ]

@[simp]
/-
**List.ofFn_fin_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_fin_append {m n} (a : Fin m -> α) (b : Fin n -> α) : List.ofFn (Fin.a
ppend a b) = List.ofFn a ++ List.ofFn b
参数：a : Fin m -> α；b : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_add`：∀ {α : Type u_1} {n m : ℕ} {f : Fin (n + m) → α},   List.
ofFn f = (List.ofFn fun i => f (Fin.castLE ⋯ i)) ++ List.ofFn fun i => f (Fin.na
tAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.append_left'`：append_left' (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n m) : append u v (Fin.castLE (by lia) i) = u i
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFn_fin_append {m n} (a : Fin m → α) (b : Fin n → α) :
    List.ofFn (Fin.append a b) = List.ofFn a ++ List.ofFn b := by
  simp_rw [ofFn_add]
  simp [Fin.append_left', Fin.append_right]

/-- This breaks a list of `m*n` items into `m` groups each containing `n` elements. -/
/-
**List.ofFn_mul** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_mul {m n} (f : Fin (m * n) -> α) : List.ofFn f = List.flatten (List.o
fFn fun i : Fin m => List.ofFn fun j : Fin n => f ⟨i * n + j, calc ↑i * n + j < 
(i + 1) * n
参数：f : Fin (m * n) -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `List.ofFn_congr`：ofFn_congr {m n : Nat} (h : m = n) (f : Fin m -> α) : o
fFn f = ofFn fun i : Fin n => f (Fin.cast h.symm i)
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.ofFn_succ'`：ofFn_succ' {n} (f : Fin (succ n) -> α) : ofFn f = (ofFn
 fun i => f (Fin.castSucc i)).concat (f (Fin.last _))
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `List.ofFn_add`：∀ {α : Type u_1} {n m : ℕ} {f : Fin (n + m) → α},   List.
ofFn f = (List.ofFn fun i => f (Fin.castLE ⋯ i)) ++ List.ofFn fun i => f (Fin.na
tAd…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cast_castLE`：∀ {k m n : ℕ} (km : k ≤ m) (mn : m = n) (i : Fin k), Fi
n.cast mn (Fin.castLE km i) = Fin.castLE ⋯ i
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.flatten_append`：∀ {α : Type u_1} {L₁ L₂ : List (List α)}, (L₁ ++ L₂
).flatten = L₁.flatten ++ L₂.flatten
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.append_cancel_left_eq`：∀ {α : Type u_1} (as bs cs : List α), (as ++
 bs = as ++ cs) = (bs = cs)

--- 原说明 ---
This breaks a list of `m*n` items into `m` groups each containing `n` elements.
-/
theorem ofFn_mul {m n} (f : Fin (m * n) → α) :
    List.ofFn f = List.flatten (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f ⟨i * n + j,
    calc
      ↑i * n + j < (i + 1) * n :=
        (Nat.add_lt_add_left j.prop _).trans_eq (by rw [Nat.add_mul, Nat.one_mul])
      _ ≤ _ := Nat.mul_le_mul_right _ i.prop⟩) := by
  induction m with
  | zero => simp [ofFn_zero, Nat.zero_mul, ofFn_zero]
  | succ m IH =>
    simp_rw [ofFn_succ', succ_mul]
    simp [ofFn_add, IH]
    rfl

/-- This breaks a list of `m*n` items into `n` groups each containing `m` elements. -/
/-
**List.ofFn_mul'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_mul' {m n} (f : Fin (m * n) -> α) : List.ofFn f = List.flatten (List.
ofFn fun i : Fin n => List.ofFn fun j : Fin m => f ⟨m * i + j, calc m * i + j < 
m * (i + 1)
参数：f : Fin (m * n) -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.ofFn_congr`：ofFn_congr {m n : Nat} (h : m = n) (f : Fin m -> α) : o
fFn f = ofFn fun i : Fin n => f (Fin.cast h.symm i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `List.ofFn_mul`：ofFn_mul {m n} (f : Fin (m * n) -> α) : List.ofFn f = Lis
t.flatten (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f ⟨i * n + j, c
alc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This breaks a list of `m*n` items into `n` groups each containing `m` elements.
-/
theorem ofFn_mul' {m n} (f : Fin (m * n) → α) :
    List.ofFn f = List.flatten (List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => f ⟨m * i + j,
    calc
      m * i + j < m * (i + 1) :=
        (Nat.add_lt_add_left j.prop _).trans_eq (by rw [Nat.mul_add, Nat.mul_one])
      _ ≤ _ := Nat.mul_le_mul_left _ i.prop⟩) := by simp_rw [m.mul_comm, ofFn_mul, Fin.cast_mk]

@[simp]
/-
**List.ofFn_get** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α), List.ofFn l.get = l
参数：l : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFn_get : ∀ l : List α, (ofFn (get l)) = l
  | [] => by rw [ofFn_zero]
  | a :: l => by
    rw [ofFn_succ]
    congr
    exact ofFn_get l

@[simp]
/-
**List.ofFn_getElem_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_getElem_eq_map {β : Type*} (l : List α) (f : α -> β) : ofFn (fun i : 
Fin l.length => f <| l[(i : Nat)]) = l.map f
参数：l : List α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `List.map_ofFn`：∀ {n : ℕ} {α : Type u_1} {β : Type u_2} {f : Fin n → α} {
g : α → β}, List.map g (List.ofFn f) = List.ofFn (g ∘ f)
· 使用定理 `List.ofFn_getElem`：∀ {α : Type u_1} {xs : List α}, (List.ofFn fun i => x
s[↑i]) = xs
-/
theorem ofFn_getElem_eq_map {β : Type*} (l : List α) (f : α → β) :
    ofFn (fun i : Fin l.length => f <| l[(i : Nat)]) = l.map f := by
  rw [← Function.comp_def, ← map_ofFn, ofFn_getElem]

-- Note there is a now another `mem_ofFn` defined in Lean, with an existential on the RHS,
-- which is marked as a simp lemma.
/-
**List.mem_ofFn'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_ofFn' {n} (f : Fin n -> α) (a : α) : a in ofFn f ↔ a in Set.range f
参数：f : Fin n -> α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_ofFn' {n} (f : Fin n → α) (a : α) : a ∈ ofFn f ↔ a ∈ Set.range f := by grind
/-
**List.forall_mem_ofFn_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：forall_mem_ofFn_iff {n : Nat} {f : Fin n -> α} {P : α -> Prop} : (forall i
 in ofFn f, P i) ↔ forall j : Fin n, P (f j)
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_mem_ofFn_iff {n : ℕ} {f : Fin n → α} {P : α → Prop} :
    (∀ i ∈ ofFn f, P i) ↔ ∀ j : Fin n, P (f j) := by simp

@[simp]
/-
**List.ofFn_const** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) = List.replicate n 
c
参数：n : ℕ；c : α；List.ofFn fun x => c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFn_const : ∀ (n : ℕ) (c : α), (ofFn fun _ : Fin n => c) = replicate n c
  | 0, c => by rw [ofFn_zero, replicate_zero]
  | n + 1, c => by rw [replicate, ← ofFn_const n]; simp

@[simp]
/-
**List.ofFn_fin_repeat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_fin_repeat {m} (a : Fin m -> α) (n : Nat) : List.ofFn (Fin.repeat n a
) = (List.replicate n (List.ofFn a)).flatten
参数：a : Fin m -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_mul`：ofFn_mul {m n} (f : Fin (m * n) -> α) : List.ofFn f = Lis
t.flatten (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f ⟨i * n + j, c
alc…
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Nat.add_mul_mod_self_right`：∀ (x y z : ℕ), (x + y * z) % z = x % z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFn_fin_repeat {m} (a : Fin m → α) (n : ℕ) :
    List.ofFn (Fin.repeat n a) = (List.replicate n (List.ofFn a)).flatten := by
  simp_rw [ofFn_mul, ← ofFn_const, Fin.repeat, Fin.modNat, Nat.add_comm,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Fin.is_lt _)]

@[simp]
/-
**List.pairwise_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pairwise_ofFn {R : α -> α -> Prop} {n} {f : Fin n -> α} : (ofFn f).Pairwis
e R ↔ forall ⦃i j⦄, i < j -> R (f i) (f j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_ofFn {R : α → α → Prop} {n} {f : Fin n → α} :
    (ofFn f).Pairwise R ↔ ∀ ⦃i j⦄, i < j → R (f i) (f j) := by
  simp only [pairwise_iff_getElem, length_ofFn, List.getElem_ofFn,
    Fin.forall_iff,
    Fin.mk_lt_mk, forall_comm (α := (_ : Prop)) (β := ℕ)]
/-
**List.getLast_ofFn_succ** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：getLast_ofFn_succ {n : Nat} (f : Fin n.succ -> α) : (ofFn f).getLast (mt o
fFn_eq_nil_iff.1 (Nat.succ_ne_zero _)) = f (Fin.last _)
参数：f : Fin n.succ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast_ofFn`：∀ {α : Type u_1} {n : ℕ} {f : Fin n → α} (h : List.of
Fn f ≠ []), (List.ofFn f).getLast h = f ⟨n - 1, ⋯⟩
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.ofFn_eq_nil_iff`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, List.ofF
n f = [] ↔ n = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
lemma getLast_ofFn_succ {n : ℕ} (f : Fin n.succ → α) :
    (ofFn f).getLast (mt ofFn_eq_nil_iff.1 (Nat.succ_ne_zero _)) = f (Fin.last _) :=
  getLast_ofFn _
/-
**List.ofFn_cons** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：ofFn_cons {n} (a : α) (f : Fin n -> α) : ofFn (Fin.cons a f) = a :: ofFn f
参数：a : α；f : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
-/
lemma ofFn_cons {n} (a : α) (f : Fin n → α) : ofFn (Fin.cons a f) = a :: ofFn f := by
  rw [ofFn_succ]
  rfl
/-
**List.find** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：find?_eq_find?_of_perm {p : α -> Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂) (
hp : {x in l₁ | p x}.Subsingleton) : l₁.find? p = l₂.find? p
参数：h : l₁.Perm l₂；hp : {x in l₁ | p x}.Subsingleton。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma find?_ofFn_eq_some {n} {f : Fin n → α} {p : α → Bool} {b : α} :
    (ofFn f).find? p = some b ↔ p b = true ∧ ∃ i, f i = b ∧ ∀ j < i, ¬(p (f j) = true) := by
  rw [find?_eq_some_iff_getElem]
  exact ⟨fun ⟨hpb, i, hi, hfb, h⟩ ↦
      ⟨hpb, ⟨⟨i, length_ofFn (f := f) ▸ hi⟩, by simpa
        using! hfb, fun j hj ↦ by simpa using! h j hj⟩⟩,
    fun ⟨hpb, i, hfb, h⟩ ↦
      ⟨hpb, ⟨i, (length_ofFn (f := f)).symm ▸ i.isLt, by simpa using! hfb,
        fun j hj ↦ by simpa using! h ⟨j, by lia⟩ (by simpa using! hj)⟩⟩⟩
/-
**List.find** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：find?_eq_find?_of_perm {p : α -> Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂) (
hp : {x in l₁ | p x}.Subsingleton) : l₁.find? p = l₂.find? p
参数：h : l₁.Perm l₂；hp : {x in l₁ | p x}.Subsingleton。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma find?_ofFn_eq_some_of_injective {n} {f : Fin n → α} {p : α → Bool} {i : Fin n}
    (h : Function.Injective f) :
    (ofFn f).find? p = some (f i) ↔ p (f i) = true ∧ ∀ j < i, ¬(p (f j) = true) := by
  simp only [find?_ofFn_eq_some, h.eq_iff, Bool.not_eq_true, exists_eq_left]

/-- Lists are equivalent to the sigma type of tuples of a given length. -/
@[simps]
/-
**List.equivSigmaTuple** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：equivSigmaTuple : List α ≃ Σ n, Fin n -> α where toFun l
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.ofFn_get`：∀ {α : Type u} (l : List α), List.ofFn l.get = l

--- 原说明 ---
Lists are equivalent to the sigma type of tuples of a given length.
-/
def equivSigmaTuple : List α ≃ Σ n, Fin n → α where
  toFun l := ⟨l.length, l.get⟩
  invFun f := List.ofFn f.2
  left_inv := List.ofFn_get
  right_inv := fun ⟨_, f⟩ =>
    Fin.sigma_eq_of_eq_comp_cast length_ofFn <| funext fun i => get_ofFn f i

/-- A recursor for lists that expands a list into a function mapping to its elements.

This can be used with `induction l using List.ofFnRec`. -/
@[elab_as_elim]
/-
**List.ofFnRec** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：ofFnRec {C : List α -> Sort*} (h : forall (n) (f : Fin n -> α), C (List.of
Fn f)) (l : List α) : C l
参数：h : forall (n) (f : Fin n -> α), C (List.ofFn f)；l : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for lists that expands a list into a function mapping to its elements
.

This can be used with `induction l using List.ofFnRec`.
-/
def ofFnRec {C : List α → Sort*} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) (l : List α) : C l :=
  cast (congr_arg C l.ofFn_get) <|
    h l.length l.get

@[simp]
/-
**List.ofFnRec_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFnRec_ofFn {C : List α -> Sort*} (h : forall (n) (f : Fin n -> α), C (Li
st.ofFn f)) {n : Nat} (f : Fin n -> α) : @ofFnRec _ C h (List.ofFn f) = h _ f
参数：h : forall (n) (f : Fin n -> α), C (List.ofFn f)；f : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.cast_eq`：Function.LeftInverse.cast_eq {γ : β -> Sor
t v} {f : α -> β} {g : β -> α} (h : Function.LeftInverse g f) (C : forall a : α,
 γ (f a)) (a : α) …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.rightInverse_symm`：rightInverse_symm (f : α ≃ β) : Function.RightI
nverse f.symm f
-/
theorem ofFnRec_ofFn {C : List α → Sort*} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) {n : ℕ}
    (f : Fin n → α) : @ofFnRec _ C h (List.ofFn f) = h _ f :=
  equivSigmaTuple.rightInverse_symm.cast_eq (fun s => h s.1 s.2) ⟨n, f⟩
/-
**List.exists_iff_exists_tuple** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：exists_iff_exists_tuple {P : List α -> Prop} : (exists l : List α, P l) ↔ 
exists (n : _) (f : Fin n -> α), P (List.ofFn f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Sigma.exists`：∀ {α : Type u_1} {β : α → Type u_4} {p : (a : α) × β a → P
rop}, (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩
-/
theorem exists_iff_exists_tuple {P : List α → Prop} :
    (∃ l : List α, P l) ↔ ∃ (n : _) (f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.surjective.exists.trans Sigma.exists
/-
**List.forall_iff_forall_tuple** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：forall_iff_forall_tuple {P : List α -> Prop} : (forall l : List α, P l) ↔ 
forall (n) (f : Fin n -> α), P (List.ofFn f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Sigma.forall`：∀ {α : Type u_1} {β : α → Type u_4} {p : (a : α) × β a → P
rop},   (∀ (x : (a : α) × β a), p x) ↔ ∀ (a : α) (b : β a), p ⟨a, b⟩
-/
theorem forall_iff_forall_tuple {P : List α → Prop} :
    (∀ l : List α, P l) ↔ ∀ (n) (f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.surjective.forall.trans Sigma.forall

/-- `Fin.sigma_eq_iff_eq_comp_cast` may be useful to work with the RHS of this expression. -/
/-
**List.ofFn_inj'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_inj' {m n : Nat} {f : Fin m -> α} {g : Fin n -> α} : ofFn f = ofFn g 
↔ (⟨m, f⟩ : Σ n, Fin n -> α) = ⟨n, g⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
`Fin.sigma_eq_iff_eq_comp_cast` may be useful to work with the RHS of this expre
ssion.
-/
theorem ofFn_inj' {m n : ℕ} {f : Fin m → α} {g : Fin n → α} :
    ofFn f = ofFn g ↔ (⟨m, f⟩ : Σ n, Fin n → α) = ⟨n, g⟩ :=
  Iff.symm <| equivSigmaTuple.symm.injective.eq_iff.symm

/-- Note we can only state this when the two functions are indexed by defeq `n`. -/
/-
**List.ofFn_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_injective {n : Nat} : Function.Injective (ofFn : (Fin n -> α) -> List
 α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_inj'`：ofFn_inj' {m n : Nat} {f : Fin m -> α} {g : Fin n -> α} 
: ofFn f = ofFn g ↔ (⟨m, f⟩ : Σ n, Fin n -> α) = ⟨n, g⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Note we can only state this when the two functions are indexed by defeq `n`.
-/
theorem ofFn_injective {n : ℕ} : Function.Injective (ofFn : (Fin n → α) → List α) := fun f g h =>
  eq_of_heq <| by rw [ofFn_inj'] at h; cases h; rfl

/-- A special case of `List.ofFn_inj` for when the two functions are indexed by defeq `n`. -/
@[simp]
/-
**List.ofFn_inj** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_inj {n : Nat} {f g : Fin n -> α} : ofFn f = ofFn g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `List.ofFn_injective`：ofFn_injective {n : Nat} : Function.Injective (ofFn
 : (Fin n -> α) -> List α)

--- 原说明 ---
A special case of `List.ofFn_inj` for when the two functions are indexed by defe
q `n`.
-/
theorem ofFn_inj {n : ℕ} {f g : Fin n → α} : ofFn f = ofFn g ↔ f = g :=
  ofFn_injective.eq_iff

end List

