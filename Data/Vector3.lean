/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fin.Fin2
public import Mathlib.Util.Notation3

/-!
# Alternate definition of `Vector` in terms of `Fin2`

This file provides a scope `Vector3` which overrides the `[a, b, c]` notation to create a `Vector3`
instead of a `List`.

The `::` notation is also overloaded by this file to mean `Vector3.cons`.
-/

@[expose] public section

open Fin2 Nat

universe u

variable {α : Type*} {m n : ℕ}

/-- Alternate definition of `Vector` based on `Fin2`. -/
/-
**Vector3** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Vector3 (α : Type u) (n : Nat) : Type u
参数：α : Type u；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternate definition of `Vector` based on `Fin2`.
-/
def Vector3 (α : Type u) (n : ℕ) : Type u :=
  Fin2 n → α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Vector3 α n) where
  default := fun _ => default

namespace Vector3

/-- The empty vector -/
@[match_pattern]
/-
**Vector3.nil** 是 Mathlib 中的一个定义，位于命名空间 `Vector3`。
形式化陈述：nil : Vector3 α 0
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty vector
-/
def nil : Vector3 α 0 :=
  nofun

/-- The vector cons operation -/
@[match_pattern]
/-
**Vector3.cons** 是 Mathlib 中的一个定义，位于命名空间 `Vector3`。
形式化陈述：cons (a : α) (v : Vector3 α n) : Vector3 α (n + 1)
参数：a : α；v : Vector3 α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vector cons operation
-/
def cons (a : α) (v : Vector3 α n) : Vector3 α (n + 1) := fun i => by
  refine i.cases' ?_ ?_
  · exact a
  · exact v

section
open Lean

scoped macro_rules | `([$l,*]) => `(expand_foldr% (h t => cons h t) nil [$(.ofElems l),*])

-- this is copied from `Init/NotationExtra.lean` (Lean core)
/-- Unexpander for `Vector3.nil` -/
@[app_unexpander Vector3.nil] meta def unexpandNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `([])

-- this is copied from `Init/NotationExtra.lean` (Lean core)
/-- Unexpander for `Vector3.cons` -/
@[app_unexpander Vector3.cons] meta def unexpandCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x [])      => `([$x])
  | `($(_) $x [$xs,*]) => `([$x, $xs,*])
  | _                  => throw ()

end

-- Overloading the usual `::` notation for `List.cons` with `Vector3.cons`.
@[inherit_doc]
scoped notation a " :: " b => cons a b

@[simp]
/-
**Vector3.cons_fz** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：cons_fz (a : α) (v : Vector3 α n) : (a :: v) fz = a
参数：a : α；v : Vector3 α n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_fz (a : α) (v : Vector3 α n) : (a :: v) fz = a :=
  rfl

@[simp]
/-
**Vector3.cons_fs** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：cons_fs (a : α) (v : Vector3 α n) (i) : (a :: v) (fs i) = v i
参数：a : α；v : Vector3 α n；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_fs (a : α) (v : Vector3 α n) (i) : (a :: v) (fs i) = v i :=
  rfl

/-- Get the `i`th element of a vector -/
/-
**Vector3.nth** 是 Mathlib 中的一个缩写定义，位于命名空间 `Vector3`。
形式化陈述：nth (i : Fin2 n) (v : Vector3 α n) : α
参数：i : Fin2 n；v : Vector3 α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the `i`th element of a vector
-/
abbrev nth (i : Fin2 n) (v : Vector3 α n) : α :=
  v i

/-- Construct a vector from a function on `Fin2`. -/
/-
**Vector3.ofFn** 是 Mathlib 中的一个缩写定义，位于命名空间 `Vector3`。
形式化陈述：ofFn (f : Fin2 n -> α) : Vector3 α n
参数：f : Fin2 n -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a vector from a function on `Fin2`.
-/
abbrev ofFn (f : Fin2 n → α) : Vector3 α n :=
  f

/-- Get the head of a nonempty vector. -/
/-
**Vector3.head** 是 Mathlib 中的一个定义，位于命名空间 `Vector3`。
形式化陈述：head (v : Vector3 α (n + 1)) : α
参数：v : Vector3 α (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the head of a nonempty vector.
-/
def head (v : Vector3 α (n + 1)) : α :=
  v fz

/-- Get the tail of a nonempty vector. -/
/-
**Vector3.tail** 是 Mathlib 中的一个定义，位于命名空间 `Vector3`。
形式化陈述：tail (v : Vector3 α (n + 1)) : Vector3 α n
参数：v : Vector3 α (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the tail of a nonempty vector.
-/
def tail (v : Vector3 α (n + 1)) : Vector3 α n := fun i => v (fs i)
/-
**Vector3.eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：eq_nil (v : Vector3 α 0) : v = []
参数：v : Vector3 α 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem eq_nil (v : Vector3 α 0) : v = [] :=
  funext fun i => nomatch i
/-
**Vector3.cons_head_tail** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：cons_head_tail (v : Vector3 α (n + 1)) : (head v :: tail v) = v
参数：v : Vector3 α (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem cons_head_tail (v : Vector3 α (n + 1)) : (head v :: tail v) = v :=
  funext fun i => Fin2.cases' rfl (fun _ => rfl) i

/-- Eliminator for an empty vector. -/
@[elab_as_elim]
/-
**Vector3.nilElim** 是 Mathlib 中的一个定义，位于命名空间 `Vector3`。
形式化陈述：nilElim {C : Vector3 α 0 -> Sort u} (H : C []) (v : Vector3 α 0) : C v
参数：H : C []；v : Vector3 α 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Eliminator for an empty vector.
-/
def nilElim {C : Vector3 α 0 → Sort u} (H : C []) (v : Vector3 α 0) : C v := by
  rw [eq_nil v]; apply H

/-- Recursion principle for a nonempty vector. -/
@[elab_as_elim]
/-
**Vector3.consElim** 是 Mathlib 中的一个定义，位于命名空间 `Vector3`。
形式化陈述：consElim {C : Vector3 α (n + 1) -> Sort u} (H : forall (a : α) (t : Vector
3 α n), C (a :: t)) (v : Vector3 α (n + 1)) : C v
参数：n + 1；H : forall (a : α) (t : Vector3 α n), C (a :: t)；v : Vector3 α (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle for a nonempty vector.
-/
def consElim {C : Vector3 α (n + 1) → Sort u} (H : ∀ (a : α) (t : Vector3 α n), C (a :: t))
    (v : Vector3 α (n + 1)) : C v := by rw [← cons_head_tail v]; apply H

@[simp]
/-
**Vector3.consElim_cons** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：consElim_cons {C H a t} : @consElim α n C H (a :: t) = H a t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem consElim_cons {C H a t} : @consElim α n C H (a :: t) = H a t :=
  rfl

/-- Recursion principle with the vector as first argument. -/
@[elab_as_elim]
/-
**Vector3.recOn** 是 Mathlib 中的一个定义，位于命名空间 `Vector3`。
形式化陈述：{α : Type u_1} →   {C : {n : ℕ} → Vector3 α n → Sort u} →     {n : ℕ} → (v
 : Vector3 α n) → C [] → ({n : ℕ} → (a : α) → (w : Vector3 α n) → C w → C (Vecto
r3.cons a w)) → C v
参数：v : Vector3 α n；{n : ℕ} → (a : α) → (w : Vector3 α n) → C w → C (Vector3.cons
 a w)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle with the vector as first argument.
-/
protected def recOn {C : ∀ {n}, Vector3 α n → Sort u} {n} (v : Vector3 α n) (H0 : C [])
    (Hs : ∀ {n} (a) (w : Vector3 α n), C w → C (a :: w)) : C v :=
  match n with
  | 0 => v.nilElim H0
  | _ + 1 => v.consElim fun a t => Hs a t (Vector3.recOn t H0 Hs)

@[simp]
/-
**Vector3.recOn_nil** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：recOn_nil {C H0 Hs} : @Vector3.recOn α (@C) 0 [] H0 @Hs = H0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem recOn_nil {C H0 Hs} : @Vector3.recOn α (@C) 0 [] H0 @Hs = H0 :=
  rfl

@[simp]
/-
**Vector3.recOn_cons** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：recOn_cons {C H0 Hs n a v} : @Vector3.recOn α (@C) (n + 1) (a :: v) H0 @Hs
 = Hs a v (@Vector3.recOn α (@C) n v H0 @Hs)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem recOn_cons {C H0 Hs n a v} :
    @Vector3.recOn α (@C) (n + 1) (a :: v) H0 @Hs = Hs a v (@Vector3.recOn α (@C) n v H0 @Hs) :=
  rfl

/-- Append two vectors -/
/-
**Vector3.append** 是 Mathlib 中的一个定义，位于命名空间 `Vector3`。
形式化陈述：append (v : Vector3 α m) (w : Vector3 α n) : Vector3 α (n + m)
参数：v : Vector3 α m；w : Vector3 α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Append two vectors
-/
def append (v : Vector3 α m) (w : Vector3 α n) : Vector3 α (n + m) :=
  v.recOn w (fun a _ IH => a :: IH)

/--
A local infix notation for `Vector3.append`
-/
local infixl:65 " +-+ " => Vector3.append

@[simp]
/-
**Vector3.append_nil** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：append_nil (w : Vector3 α n) : [] +-+ w = w
参数：w : Vector3 α n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_nil (w : Vector3 α n) : [] +-+ w = w :=
  rfl

@[simp]
/-
**Vector3.append_cons** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：append_cons (a : α) (v : Vector3 α m) (w : Vector3 α n) : (a :: v) +-+ w =
 a :: v +-+ w
参数：a : α；v : Vector3 α m；w : Vector3 α n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_cons (a : α) (v : Vector3 α m) (w : Vector3 α n) : (a :: v) +-+ w = a :: v +-+ w :=
  rfl

@[simp]
/-
**Vector3.append_left** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：∀ {α : Type u_1} {m : ℕ} (i : Fin2 m) (v : Vector3 α m) {n : ℕ} (w : Vecto
r3 α n), v.append w (Fin2.left n i) = v i
参数：i : Fin2 m；v : Vector3 α m；w : Vector3 α n；Fin2.left n i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_left :
    ∀ {m} (i : Fin2 m) (v : Vector3 α m) {n} (w : Vector3 α n), (v +-+ w) (left n i) = v i
  | _, @fz m, v, _, _ => v.consElim fun a _t => by simp [*, left]
  | _, @fs m i, v, n, w => v.consElim fun _a t => by simp [append_left, left]

@[simp]
/-
**Vector3.append_add** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：∀ {α : Type u_1} {m : ℕ} (v : Vector3 α m) {n : ℕ} (w : Vector3 α n) (i : 
Fin2 n), v.append w (i.add m) = w i
参数：v : Vector3 α m；w : Vector3 α n；i : Fin2 n；i.add m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_add :
    ∀ {m} (v : Vector3 α m) {n} (w : Vector3 α n) (i : Fin2 n), (v +-+ w) (add i m) = w i
  | 0, _, _, _, _ => rfl
  | m + 1, v, n, w, i => v.consElim fun _a t => by simp [append_add, add]

/-- Insert `a` into `v` at index `i`. -/
/-
**Vector3.insert** 是 Mathlib 中的一个定义，位于命名空间 `Vector3`。
形式化陈述：insert (a : α) (v : Vector3 α n) (i : Fin2 (n + 1)) : Vector3 α (n + 1)
参数：a : α；v : Vector3 α n；i : Fin2 (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Insert `a` into `v` at index `i`.
-/
def insert (a : α) (v : Vector3 α n) (i : Fin2 (n + 1)) : Vector3 α (n + 1) := fun j =>
  (a :: v) (insertPerm i j)

@[simp]
/-
**Vector3.insert_fz** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：insert_fz (a : α) (v : Vector3 α n) : insert a v fz = a :: v
参数：a : α；v : Vector3 α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem insert_fz (a : α) (v : Vector3 α n) : insert a v fz = a :: v := by
  refine funext fun j => j.cases' ?_ ?_ <;> intros <;> rfl

@[simp]
/-
**Vector3.insert_fs** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：insert_fs (a : α) (b : α) (v : Vector3 α n) (i : Fin2 (n + 1)) : insert a 
(b :: v) (fs i) = b :: insert a v i
参数：a : α；b : α；v : Vector3 α n；i : Fin2 (n + 1)。
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
· 使用定理 `Fin2.insertPerm.eq_3`：∀ (a : ℕ) (a_1 : Fin2 a.succ), a_1.fs.insertPerm F
in2.fz = Fin2.fz.fs
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin2.insertPerm.eq_4`：∀ (a : ℕ) (i : Fin2 a.succ) (j : Fin2 (a + 1)),   
i.fs.insertPerm j.fs =     match i.insertPerm j with     | Fin2.fz => Fin2.fz   
  | k.fs =…
· 使用定理 `_private.Mathlib.Data.Vector3.0.Fin2.cases'.match_1.eq_1`：∀ {n : ℕ} (mot
ive : Fin2 n.succ → Sort u_1) (h_1 : Unit → motive Fin2.fz) (h_2 : (n_1 : Fin2 n
) → motive n_1.fs),   (match Fin2.fz with     …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `_private.Mathlib.Data.Vector3.0.Fin2.cases'.match_1.eq_2`：∀ {n : ℕ} (mot
ive : Fin2 n.succ → Sort u_1) (n_1 : Fin2 n) (h_1 : Unit → motive Fin2.fz)   (h_
2 : (n_2 : Fin2 n) → motive n_2.fs),   (match …
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem insert_fs (a : α) (b : α) (v : Vector3 α n) (i : Fin2 (n + 1)) :
    insert a (b :: v) (fs i) = b :: insert a v i :=
  funext fun j => by
    refine j.cases' (by simp [insert, insertPerm]) fun j => ?_
    simp only [insert, insertPerm, succ_eq_add_one, cons_fs]
    refine Fin2.cases' ?_ ?_ (insertPerm i j) <;> simp
/-
**Vector3.append_insert** 是 Mathlib 中的一个定理，位于命名空间 `Vector3`。
形式化陈述：append_insert (a : α) (t : Vector3 α m) (v : Vector3 α n) (i : Fin2 (n + 1
)) (e : (n + 1) + m = (n + m) + 1) : insert a (t +-+ v) (Eq.recOn e (i.add m)) =
 Eq.recOn e (t +-+ insert a v i)
参数：a : α；t : Vector3 α m；v : Vector3 α n；i : Fin2 (n + 1)；e : (n + 1) + m = (n +
 m) + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Vector3.insert_fs`：insert_fs (a : α) (b : α) (v : Vector3 α n) (i : Fin2
 (n + 1)) : insert a (b :: v) (fs i) = b :: insert a v i
-/
theorem append_insert (a : α) (t : Vector3 α m) (v : Vector3 α n) (i : Fin2 (n + 1))
    (e : (n + 1) + m = (n + m) + 1) :
    insert a (t +-+ v) (Eq.recOn e (i.add m)) = Eq.recOn e (t +-+ insert a v i) := by
  refine Vector3.recOn t (fun e => ?_) (@fun k b t IH _ => ?_) e
  · rfl
  have e' : (n + 1) + k = (n + k) + 1 := by lia
  change
    insert a (b :: t +-+ v)
      (Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (fs (add i k))) =
      Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (b :: t +-+ insert a v i)
  rw [← (Eq.recOn e' rfl :
      fs (Eq.recOn e' (i.add k) : Fin2 ((n + k) + 1)) =
        Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (fs (i.add k)))]
  simpa [IH] using Eq.recOn e' rfl

end Vector3

section Vector3

open Vector3

/-- "Curried" exists, i.e. `∃ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
/-
**VectorEx** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_1} → (k : ℕ) → (Vector3 α k → Prop) → Prop
参数：k : ℕ；Vector3 α k → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Curried" exists, i.e. `∃ x₁ ... xₙ, f [x₁, ..., xₙ]`.
-/
def VectorEx : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∃ x : α, VectorEx k fun v => f (x :: v)

/-- "Curried" forall, i.e. `∀ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
/-
**VectorAll** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_1} → (k : ℕ) → (Vector3 α k → Prop) → Prop
参数：k : ℕ；Vector3 α k → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Curried" forall, i.e. `∀ x₁ ... xₙ, f [x₁, ..., xₙ]`.
-/
def VectorAll : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∀ x : α, VectorAll k fun v => f (x :: v)
/-
**exists_vector_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_vector_zero (f : Vector3 α 0 -> Prop) : Exists f ↔ f []
参数：f : Vector3 α 0 -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Vector3.eq_nil`：eq_nil (v : Vector3 α 0) : v = []
-/
theorem exists_vector_zero (f : Vector3 α 0 → Prop) : Exists f ↔ f [] :=
  ⟨fun ⟨v, fv⟩ => by rw [← eq_nil v]; exact fv, fun f0 => ⟨[], f0⟩⟩
/-
**exists_vector_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_vector_succ (f : Vector3 α (succ n) -> Prop) : Exists f ↔ exists x 
v, f (x :: v)
参数：f : Vector3 α (succ n) -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Vector3.cons_head_tail`：cons_head_tail (v : Vector3 α (n + 1)) : (head v
 :: tail v) = v
-/
theorem exists_vector_succ (f : Vector3 α (succ n) → Prop) : Exists f ↔ ∃ x v, f (x :: v) :=
  ⟨fun ⟨v, fv⟩ => ⟨_, _, by rw [cons_head_tail v]; exact fv⟩, fun ⟨_, _, fxv⟩ => ⟨_, fxv⟩⟩
/-
**vectorEx_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (f : Vector3 α n → Prop), VectorEx n f ↔ Exists f
参数：f : Vector3 α n → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vectorEx_iff_exists : ∀ {n} (f : Vector3 α n → Prop), VectorEx n f ↔ Exists f
  | 0, f => (exists_vector_zero f).symm
  | succ _, f =>
    Iff.trans (exists_congr fun _ => vectorEx_iff_exists _) (exists_vector_succ f).symm
/-
**vectorAll_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (f : Vector3 α n → Prop), VectorAll n f ↔ ∀ (v : 
Vector3 α n), f v
参数：f : Vector3 α n → Prop；v : Vector3 α n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vectorAll_iff_forall : ∀ {n} (f : Vector3 α n → Prop), VectorAll n f ↔ ∀ v, f v
  | 0, _ => ⟨fun f0 v => v.nilElim f0, fun al => al []⟩
  | succ _, f =>
    (forall_congr' fun x => vectorAll_iff_forall fun v => f (x :: v)).trans
      ⟨fun al v => v.consElim al, fun al x v => al (x :: v)⟩

/-- `VectorAllP p v` is equivalent to `∀ i, p (v i)`, but unfolds directly to a conjunction,
  i.e. `VectorAllP p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
/-
**VectorAllP** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：VectorAllP (p : α -> Prop) (v : Vector3 α n) : Prop
参数：p : α -> Prop；v : Vector3 α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`VectorAllP p v` is equivalent to `∀ i, p (v i)`, but unfolds directly to a conj
unction,
  i.e. `VectorAllP p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`.
-/
def VectorAllP (p : α → Prop) (v : Vector3 α n) : Prop :=
  Vector3.recOn v True fun a v IH =>
    @Vector3.recOn _ (fun _ => Prop) _ v (p a) fun _ _ _ => p a ∧ IH

@[simp]
/-
**vectorAllP_nil** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorAllP_nil (p : α -> Prop) : VectorAllP p [] = True
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vectorAllP_nil (p : α → Prop) : VectorAllP p [] = True :=
  rfl

@[simp]
/-
**vectorAllP_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorAllP_singleton (p : α -> Prop) (x : α) : VectorAllP p (cons x []) = 
p x
参数：p : α -> Prop；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vectorAllP_singleton (p : α → Prop) (x : α) : VectorAllP p (cons x []) = p x :=
  rfl

@[simp]
/-
**vectorAllP_cons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorAllP_cons (p : α -> Prop) (x : α) (v : Vector3 α n) : VectorAllP p (
x :: v) ↔ p x ∧ VectorAllP p v
参数：p : α -> Prop；x : α；v : Vector3 α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem vectorAllP_cons (p : α → Prop) (x : α) (v : Vector3 α n) :
    VectorAllP p (x :: v) ↔ p x ∧ VectorAllP p v :=
  Vector3.recOn v (iff_of_eq (and_true _)).symm fun _ _ _ => Iff.rfl
/-
**vectorAllP_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorAllP_iff_forall (p : α -> Prop) (v : Vector3 α n) : VectorAllP p v ↔
 forall i, p (v i)
参数：p : α -> Prop；v : Vector3 α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
-/
theorem vectorAllP_iff_forall (p : α → Prop) (v : Vector3 α n) :
    VectorAllP p v ↔ ∀ i, p (v i) := by
  refine v.recOn ?_ ?_
  · exact ⟨fun _ => Fin2.elim0, fun _ => trivial⟩
  · simp only [vectorAllP_cons]
    refine fun {n} a v IH =>
      (and_congr_right fun _ => IH).trans
        ⟨fun ⟨pa, h⟩ i => by
          refine i.cases' ?_ ?_
          exacts [pa, h], fun h => ⟨?_, fun i => ?_⟩⟩
    · simpa using h fz
    · simpa using h (fs i)
/-
**VectorAllP.imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：VectorAllP.imp {p q : α -> Prop} (h : forall x, p x -> q x) {v : Vector3 α
 n} (al : VectorAllP p v) : VectorAllP q v
参数：h : forall x, p x -> q x；al : VectorAllP p v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vectorAllP_iff_forall`：vectorAllP_iff_forall (p : α -> Prop) (v : Vector
3 α n) : VectorAllP p v ↔ forall i, p (v i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem VectorAllP.imp {p q : α → Prop} (h : ∀ x, p x → q x) {v : Vector3 α n}
    (al : VectorAllP p v) : VectorAllP q v :=
  (vectorAllP_iff_forall _ _).2 fun _ => h _ <| (vectorAllP_iff_forall _ _).1 al _

end Vector3

