/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Control.Lawful
public import Batteries.Tactic.Congr
public import Batteries.Lean.Except

/-!
# Continuation Monad

Monad encapsulating continuation passing programming style, similar to
Haskell's `Cont`, `ContT` and `MonadCont`:
<https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html>
<https://hackage.haskell.org/package/transformers-0.6.2.0/docs/Control-Monad-Trans-Cont.html>
-/

@[expose] public section

universe u v w u₀ u₁ v₀ v₁

/-
**MonadCont.Label** 是 Mathlib 中的一个归纳类型，位于命名空间 `MonadCont`。
形式化陈述：Type w → (Type u → Type v) → Type u → Type (max v w)
参数：Type u → Type v；max v w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure MonadCont.Label (α : Type w) (m : Type u → Type v) (β : Type u) where
  apply : α → m β
/-
**MonadCont.goto** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MonadCont.goto {α β} {m : Type u -> Type v} (f : MonadCont.Label α m β) (x
 : α)
参数：f : MonadCont.Label α m β；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev MonadCont.goto {α β} {m : Type u → Type v} (f : MonadCont.Label α m β) (x : α) :=
  f.apply x
/-
**MonadCont** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(Type u → Type v) → Type (max (u + 1) v)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class MonadCont (m : Type u → Type v) where
  callCC : ∀ {α β}, (MonadCont.Label α m β → m α) → m α

open MonadCont
/-
**LawfulMonadCont** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(m : Type u → Type v) → [Monad m] → [MonadCont m] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class LawfulMonadCont (m : Type u → Type v) [Monad m] [MonadCont m] : Prop
    extends LawfulMonad m where
  callCC_bind_right {α ω γ} (cmd : m α) (next : Label ω m γ → α → m ω) :
    (callCC fun f => cmd >>= next f) = cmd >>= fun x => callCC fun f => next f x
  callCC_bind_left {α} (β) (x : α) (dead : Label α m β → β → m α) :
    (callCC fun f : Label α m β => goto f x >>= dead f) = pure x
  callCC_dummy {α β} (dummy : m α) : (callCC fun _ : Label α m β => dummy) = dummy

export LawfulMonadCont (callCC_bind_right callCC_bind_left callCC_dummy)
/-
**ContT** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContT (r : Type u) (m : Type u -> Type v) (α : Type w)
参数：r : Type u；m : Type u -> Type v；α : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ContT (r : Type u) (m : Type u → Type v) (α : Type w) :=
  (α → m r) → m r
/-
**Cont** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Cont (r : Type u) (α : Type w)
参数：r : Type u；α : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Cont (r : Type u) (α : Type w) :=
  ContT r Id α

namespace ContT

export MonadCont (Label goto)

variable {r : Type u} {m : Type u → Type v} {α β : Type w}

/-- Build a `ContT` from a function taking a continuation callback. -/
/-
**ContT.mk** 是 Mathlib 中的一个定义，位于命名空间 `ContT`。
形式化陈述：mk (f : (α -> m r) -> m r) : ContT r m α
参数：f : (α -> m r) -> m r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `ContT` from a function taking a continuation callback.
-/
def mk (f : (α → m r) → m r) : ContT r m α := f

/-- Run a `ContT` with a provided callback. -/
/-
**ContT.run** 是 Mathlib 中的一个定义，位于命名空间 `ContT`。
形式化陈述：run (x : ContT r m α) : (α -> m r) -> m r
参数：x : ContT r m α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Run a `ContT` with a provided callback.
-/
def run (x : ContT r m α) : (α → m r) → m r := x
/-
**ContT.map** 是 Mathlib 中的一个定义，位于命名空间 `ContT`。
形式化陈述：map (f : m r -> m r) (x : ContT r m α) : ContT r m α
参数：f : m r -> m r；x : ContT r m α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (f : m r → m r) (x : ContT r m α) : ContT r m α :=
  f ∘ x
/-
**ContT.run_contT_map_contT** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_contT_map_contT (f : m r -> m r) (x : ContT r m α) : run (map f x) = f
 ∘ run x
参数：f : m r -> m r；x : ContT r m α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_contT_map_contT (f : m r → m r) (x : ContT r m α) : run (map f x) = f ∘ run x :=
  rfl
/-
**ContT.withContT** 是 Mathlib 中的一个定义，位于命名空间 `ContT`。
形式化陈述：withContT (f : (β -> m r) -> α -> m r) (x : ContT r m α) : ContT r m β
参数：f : (β -> m r) -> α -> m r；x : ContT r m α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def withContT (f : (β → m r) → α → m r) (x : ContT r m α) : ContT r m β := fun g => x <| f g
/-
**ContT.run_withContT** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_withContT (f : (β -> m r) -> α -> m r) (x : ContT r m α) : run (withCo
ntT f x) = run x ∘ f
参数：f : (β -> m r) -> α -> m r；x : ContT r m α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_withContT (f : (β → m r) → α → m r) (x : ContT r m α) :
    run (withContT f x) = run x ∘ f :=
  rfl

@[ext]
/-
**ContT.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：∀ {r : Type u} {m : Type u → Type v} {α : Type w} {x y : ContT r m α}, (∀ 
(f : α → m r), x.run f = y.run f) → x = y
参数：∀ (f : α → m r), x.run f = y.run f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem ext {x y : ContT r m α} (h : ∀ f, x.run f = y.run f) : x = y := by
  unfold ContT; ext; apply h
/-
**ContT.** 是 Mathlib 中的一个实例，位于命名空间 `ContT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monad (ContT r m) where
  pure x f := f x
  bind x f g := x fun i => f i g

@[simp]
/-
**ContT.run_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_mk (f : (α -> m r) -> m r) (k : α -> m r) : (.mk f : ContT r m α).run 
k = f k
参数：f : (α -> m r) -> m r；k : α -> m r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_mk (f : (α → m r) → m r) (k : α → m r) : (.mk f : ContT r m α).run k = f k := rfl

@[simp]
/-
**ContT.run_pure** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_pure (a : α) (k : α -> m r) : (pure a : ContT r m α).run k = k a
参数：a : α；k : α -> m r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_pure (a : α) (k : α → m r) : (pure a : ContT r m α).run k = k a := rfl

@[simp]
/-
**ContT.run_bind** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_bind (x : ContT r m α) (f : α -> ContT r m β) (k : β -> m r) : (x >>= 
f).run k = x.run fun x => (f x).run k
参数：x : ContT r m α；f : α -> ContT r m β；k : β -> m r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_bind (x : ContT r m α) (f : α → ContT r m β) (k : β → m r) :
    (x >>= f).run k = x.run fun x => (f x).run k := rfl

@[simp]
/-
**ContT.run_map** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_map (f : α -> β) (x : ContT r m α) (k : β -> m r) : (f <$> x).run k = 
x.run (k ∘ f)
参数：f : α -> β；x : ContT r m α；k : β -> m r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_map (f : α → β) (x : ContT r m α) (k : β → m r) :
    (f <$> x).run k = x.run (k ∘ f) := rfl

@[simp]
/-
**ContT.run_seq** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_seq (f : ContT r m (α -> β)) (x : ContT r m α) (k : β -> m r) : (f <*>
 x).run k = f.run fun f => x.run (k ∘ f)
参数：f : ContT r m (α -> β)；x : ContT r m α；k : β -> m r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_seq (f : ContT r m (α → β)) (x : ContT r m α) (k : β → m r) :
    (f <*> x).run k = f.run fun f => x.run (k ∘ f) := rfl

@[simp]
/-
**ContT.run_seqLeft** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_seqLeft (x : ContT r m α) (y : ContT r m β) (k : α -> m r) : (x <* y).
run k = x.run fun x => y.run fun _ => k x
参数：x : ContT r m α；y : ContT r m β；k : α -> m r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_seqLeft (x : ContT r m α) (y : ContT r m β) (k : α → m r) :
    (x <* y).run k = x.run fun x => y.run fun _ => k x := rfl

@[simp]
/-
**ContT.run_seqRight** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_seqRight (x : ContT r m α) (y : ContT r m β) (k : β -> m r) : (x *> y)
.run k = x.run fun _ => y.run k
参数：x : ContT r m α；y : ContT r m β；k : β -> m r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_seqRight (x : ContT r m α) (y : ContT r m β) (k : β → m r) :
    (x *> y).run k = x.run fun _ => y.run k := rfl
/-
**ContT.** 是 Mathlib 中的一个实例，位于命名空间 `ContT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad (ContT r m) := LawfulMonad.mk'
  (id_map := by intros; rfl)
  (pure_bind := by intros; ext; rfl)
  (bind_assoc := by intros; ext; rfl)
/-
**ContT.** 是 Mathlib 中的一个实例，位于命名空间 `ContT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monad m] : MonadLift m (ContT r m) where
  monadLift x := .mk fun k => x >>= k

@[simp]
/-
**ContT.run_monadLift** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_monadLift [Monad m] {α} (x : m α) (k : α -> m r) : (monadLift x : Cont
T r m α).run k = x >>= k
参数：x : m α；k : α -> m r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_monadLift [Monad m] {α} (x : m α) (k : α → m r) :
    (monadLift x : ContT r m α).run k = x >>= k := rfl
/-
**ContT.monadLift_bind** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：monadLift_bind [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α -> m β) : 
(monadLift (x >>= f) : ContT r m β) = monadLift x >>= monadLift ∘ f
参数：x : m α；f : α -> m β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContT.ext`：∀ {r : Type u} {m : Type u → Type v} {α : Type w} {x y : Cont
T r m α}, (∀ (f : α → m r), x.run f = y.run f) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulMonad.bind_assoc`：∀ {m : Type u → Type v} {inst : Monad m} [self :
 LawfulMonad m] {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),   x >>= 
f >>= g = x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem monadLift_bind [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α → m β) :
    (monadLift (x >>= f) : ContT r m β) = monadLift x >>= monadLift ∘ f := by
  ext
  simp only [bind_assoc, run_bind, run_monadLift, Function.comp_apply]
/-
**ContT.** 是 Mathlib 中的一个实例，位于命名空间 `ContT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonadCont (ContT r m) where
  callCC f := .mk fun k => f ⟨fun x => .mk fun _ => k x⟩ k

@[simp]
/-
**ContT.run_callCC** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_callCC (f : Label α (ContT r m) β -> ContT r m α) (k : α -> m r) : (ca
llCC f).run k = (f ⟨fun x => .mk fun _ => k x⟩).run k
参数：f : Label α (ContT r m) β -> ContT r m α；k : α -> m r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_callCC (f : Label α (ContT r m) β → ContT r m α) (k : α → m r) :
    (callCC f).run k = (f ⟨fun x => .mk fun _ => k x⟩).run k := rfl
/-
**ContT.** 是 Mathlib 中的一个实例，位于命名空间 `ContT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonadCont (ContT r m) where
  callCC_bind_right := by intros; ext; rfl
  callCC_bind_left := by intros; ext; rfl
  callCC_dummy := by intros; ext; rfl

/-- Note that `tryCatch` does not have correct behavior in this monad:
```
def foo : ContT Bool (Except String) Bool := do
  let x ← try
    pure true
  catch _ =>
    return false
  throw s!"oh no {x}"
#eval foo.run pure
-- `Except.ok false`, no error
```
Here, the `throwError` is being run inside the `try`.
See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/MonadExcept.20in.20the.20ContT.20monad/near/375341221)
for further discussion.
-/
/-
**ContT.** 是 Mathlib 中的一个实例，位于命名空间 `ContT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that `tryCatch` does not have correct behavior in this monad:
```
def foo : ContT Bool (Except String) Bool := do
  let x ← try
    pure true
  catch _ =>
    return false
  throw s!"oh no {x}"
#eval foo.run pure
-- `Except.ok false`, no error
```
Here, the `throwError` is being run inside the `try`.
See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topi
c/MonadExcept.20in.20the.20ContT.20monad/near/375341221)
for further discussion.
-/
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (ContT r m) where
  throw e := .mk fun _ => throw e
  tryCatch act h := .mk fun k => tryCatch (act.run k) fun e => (h e).run k

@[simp]
/-
**ContT.run_throw** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_throw {ε} [MonadExceptOf ε m] (e : ε) (f : α -> m r) : (throw e : Cont
T r m α).run f = throw e
参数：e : ε；f : α -> m r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_throw {ε} [MonadExceptOf ε m]
    (e : ε) (f : α → m r) :
    (throw e : ContT r m α).run f = throw e := rfl

@[simp]
/-
**ContT.run_tryCatch** 是 Mathlib 中的一个定理，位于命名空间 `ContT`。
形式化陈述：run_tryCatch {ε} [MonadExceptOf ε m] (act : ContT r m α) (h : ε -> ContT r
 m α) (f : α -> m r) : (tryCatch act h : ContT r m α).run f = tryCatch (act.run 
f) fun e => (h e).run f
参数：act : ContT r m α；h : ε -> ContT r m α；f : α -> m r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_tryCatch {ε} [MonadExceptOf ε m]
    (act : ContT r m α) (h : ε → ContT r m α) (f : α → m r) :
    (tryCatch act h : ContT r m α).run f = tryCatch (act.run f) fun e => (h e).run f := rfl

end ContT

variable {m : Type u → Type v}

section
variable [Monad m]

/-
**ExceptT.mkLabel** 是 Mathlib 中的一个定义，位于命名空间 `ExceptT`。
形式化陈述：{m : Type u → Type v} →   [Monad m] → {α β ε : Type u} → MonadCont.Label (
Except ε α) m β → MonadCont.Label α (ExceptT ε m) β
参数：Except ε α；ExceptT ε m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ExceptT.mkLabel {α β ε} : Label (Except.{u, u} ε α) m β → Label α (ExceptT ε m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (Except.ok a)⟩
/-
**ExceptT.goto_mkLabel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExceptT.goto_mkLabel {α β ε : Type _} (x : Label (Except.{u, u} ε α) m β) 
(i : α) : goto (ExceptT.mkLabel x) i = ExceptT.mk (Except.ok <$> goto x (Except.
ok i))
参数：x : Label (Except.{u, u} ε α) m β；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ExceptT.goto_mkLabel {α β ε : Type _} (x : Label (Except.{u, u} ε α) m β) (i : α) :
    goto (ExceptT.mkLabel x) i = ExceptT.mk (Except.ok <$> goto x (Except.ok i)) := by
  cases x; rfl

nonrec def ExceptT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ExceptT ε m) β → ExceptT ε m α) : ExceptT ε m α :=
  ExceptT.mk (callCC fun x : Label _ m β => ExceptT.run <| f (ExceptT.mkLabel x))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ε} [MonadCont m] : MonadCont (ExceptT ε m) where
  callCC := ExceptT.callCC
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ε} [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (ExceptT ε m) where
  callCC_bind_right := by
    intros; simp only [callCC, ExceptT.callCC, ExceptT.run_bind, callCC_bind_right]; ext
    dsimp
    congr with ⟨⟩ <;> simp [@callCC_dummy m _]
  callCC_bind_left := by
    intros
    simp only [callCC, ExceptT.callCC, ExceptT.goto_mkLabel, map_eq_bind_pure_comp, Function.comp,
      ExceptT.run_bind, ExceptT.run_mk, bind_assoc, pure_bind, @callCC_bind_left m _]
    ext; rfl
  callCC_dummy := by intros; simp only [callCC, ExceptT.callCC, @callCC_dummy m _]; ext; rfl
/-
**OptionT.mkLabel** 是 Mathlib 中的一个定义，位于命名空间 `OptionT`。
形式化陈述：{m : Type u → Type v} → [Monad m] → {α β : Type u} → MonadCont.Label (Opti
on α) m β → MonadCont.Label α (OptionT m) β
参数：Option α；OptionT m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def OptionT.mkLabel {α β} : Label (Option.{u} α) m β → Label α (OptionT m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (some a)⟩
/-
**OptionT.goto_mkLabel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OptionT.goto_mkLabel {α β : Type _} (x : Label (Option.{u} α) m β) (i : α)
 : goto (OptionT.mkLabel x) i = OptionT.mk (goto x (some i) >>= fun a => pure (s
ome a))
参数：x : Label (Option.{u} α) m β；i : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem OptionT.goto_mkLabel {α β : Type _} (x : Label (Option.{u} α) m β) (i : α) :
    goto (OptionT.mkLabel x) i = OptionT.mk (goto x (some i) >>= fun a => pure (some a)) :=
  (rfl)

nonrec def OptionT.callCC [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β → OptionT m α) :
    OptionT m α :=
  OptionT.mk (callCC fun x : Label _ m β => OptionT.run <| f (OptionT.mkLabel x) : m (Option α))

@[simp]
/-
**run_callCC** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：run_callCC [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β -> Opti
onT m α) : (OptionT.callCC f).run = (callCC fun x => OptionT.run <| f (OptionT.m
kLabel x))
参数：f : Label α (OptionT m) β -> OptionT m α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma run_callCC [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β → OptionT m α) :
    (OptionT.callCC f).run = (callCC fun x => OptionT.run <| f (OptionT.mkLabel x)) := (rfl)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MonadCont m] : MonadCont (OptionT m) where
  callCC := OptionT.callCC
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (OptionT m) where
  callCC_bind_right := by
    refine fun _ _ => OptionT.ext ?_
    simpa [callCC, Option.elimM, callCC_bind_right] using
      bind_congr fun | some _ => rfl | none => by simp [@callCC_dummy m _]
  callCC_bind_left := by
    intros
    ext
    simp [callCC, OptionT.goto_mkLabel, @callCC_bind_left m _]
  callCC_dummy := by intros; ext; simp [callCC, OptionT.callCC, @callCC_dummy m _]
/-
**WriterT.mkLabel** 是 Mathlib 中的一个定义，位于命名空间 `WriterT`。
形式化陈述：{m : Type u → Type v} →   [Monad m] →     {α : Type u_1} →       {β ω : Ty
pe u} → [EmptyCollection ω] → MonadCont.Label (α × ω) m β → MonadCont.Label α (W
riterT ω m) β
参数：α × ω；WriterT ω m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def WriterT.mkLabel {α β ω} [EmptyCollection ω] : Label (α × ω) m β → Label α (WriterT ω m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (a, ∅)⟩
/-
**WriterT.mkLabel'** 是 Mathlib 中的一个定义，位于命名空间 `WriterT`。
形式化陈述：{m : Type u → Type v} →   [Monad m] →     {α : Type u_1} → {β ω : Type u} 
→ [Monoid ω] → MonadCont.Label (α × ω) m β → MonadCont.Label α (WriterT ω m) β
参数：α × ω；WriterT ω m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def WriterT.mkLabel' {α β ω} [Monoid ω] : Label (α × ω) m β → Label α (WriterT ω m) β
  | ⟨f⟩ => ⟨fun a => monadLift <| f (a, 1)⟩
/-
**WriterT.goto_mkLabel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WriterT.goto_mkLabel {α β ω : Type _} [EmptyCollection ω] (x : Label (α × 
ω) m β) (i : α) : goto (WriterT.mkLabel x) i = monadLift (goto x (i, ∅))
参数：x : Label (α × ω) m β；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem WriterT.goto_mkLabel {α β ω : Type _} [EmptyCollection ω] (x : Label (α × ω) m β) (i : α) :
    goto (WriterT.mkLabel x) i = monadLift (goto x (i, ∅)) := by cases x; rfl
/-
**WriterT.goto_mkLabel'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WriterT.goto_mkLabel' {α β ω : Type _} [Monoid ω] (x : Label (α × ω) m β) 
(i : α) : goto (WriterT.mkLabel' x) i = monadLift (goto x (i, 1))
参数：x : Label (α × ω) m β；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem WriterT.goto_mkLabel' {α β ω : Type _} [Monoid ω] (x : Label (α × ω) m β) (i : α) :
    goto (WriterT.mkLabel' x) i = monadLift (goto x (i, 1)) := by cases x; rfl

nonrec def WriterT.callCC [MonadCont m] {α β ω : Type _} [EmptyCollection ω]
    (f : Label α (WriterT ω m) β → WriterT ω m α) : WriterT ω m α :=
  WriterT.mk <| callCC (WriterT.run ∘ f ∘ WriterT.mkLabel : Label (α × ω) m β → m (α × ω))
/-
**WriterT.callCC'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WriterT.callCC' [MonadCont m] {α β ω : Type _} [Monoid ω] (f : Label α (Wr
iterT ω m) β -> WriterT ω m α) : WriterT ω m α
参数：f : Label α (WriterT ω m) β -> WriterT ω m α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def WriterT.callCC' [MonadCont m] {α β ω : Type _} [Monoid ω]
    (f : Label α (WriterT ω m) β → WriterT ω m α) : WriterT ω m α :=
  WriterT.mk <|
    MonadCont.callCC (WriterT.run ∘ f ∘ WriterT.mkLabel' : Label (α × ω) m β → m (α × ω))

end

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (ω) [Monad m] [EmptyCollection ω] [MonadCont m] : MonadCont (WriterT ω m) where
  callCC := WriterT.callCC
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (ω) [Monad m] [Monoid ω] [MonadCont m] : MonadCont (WriterT ω m) where
  callCC := WriterT.callCC'
/-
**StateT.mkLabel** 是 Mathlib 中的一个定义，位于命名空间 `StateT`。
形式化陈述：{m : Type u → Type v} → {α β σ : Type u} → MonadCont.Label (α × σ) m (β × 
σ) → MonadCont.Label α (StateT σ m) β
参数：α × σ；β × σ；StateT σ m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def StateT.mkLabel {α β σ : Type u} : Label (α × σ) m (β × σ) → Label α (StateT σ m) β
  | ⟨f⟩ => ⟨fun a => StateT.mk (fun s => f (a, s))⟩
/-
**StateT.goto_mkLabel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StateT.goto_mkLabel {α β σ : Type u} (x : Label (α × σ) m (β × σ)) (i : α)
 : goto (StateT.mkLabel x) i = StateT.mk (fun s => goto x (i, s))
参数：x : Label (α × σ) m (β × σ)；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem StateT.goto_mkLabel {α β σ : Type u} (x : Label (α × σ) m (β × σ)) (i : α) :
    goto (StateT.mkLabel x) i = StateT.mk (fun s => goto x (i, s)) := by cases x; rfl

nonrec def StateT.callCC {σ} [MonadCont m] {α β : Type _}
    (f : Label α (StateT σ m) β → StateT σ m α) : StateT σ m α :=
  StateT.mk (fun r => callCC fun f' => (f <| StateT.mkLabel f').run r)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ} [MonadCont m] : MonadCont (StateT σ m) where
  callCC := StateT.callCC
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ} [Monad m] [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (StateT σ m) where
  callCC_bind_right := by
    intros
    simp only [callCC, StateT.callCC, StateT.run_bind, callCC_bind_right]; ext; rfl
  callCC_bind_left := by
    intros
    simp only [callCC, StateT.callCC, StateT.goto_mkLabel, StateT.run_bind, StateT.run_mk,
      callCC_bind_left]; ext; rfl
  callCC_dummy := by
    intros
    simp only [callCC, StateT.callCC, @callCC_dummy m _]
    ext; rfl
/-
**ReaderT.mkLabel** 是 Mathlib 中的一个定义，位于命名空间 `ReaderT`。
形式化陈述：{m : Type u → Type v} →   {α : Type u_1} → {β : Type u} → (ρ : Type u) → M
onadCont.Label α m β → MonadCont.Label α (ReaderT ρ m) β
参数：ρ : Type u；ReaderT ρ m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ReaderT.mkLabel {α β} (ρ) : Label α m β → Label α (ReaderT ρ m) β
  | ⟨f⟩ => ⟨monadLift ∘ f⟩
/-
**ReaderT.goto_mkLabel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ReaderT.goto_mkLabel {α ρ β} (x : Label α m β) (i : α) : goto (ReaderT.mkL
abel ρ x) i = monadLift (goto x i)
参数：x : Label α m β；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ReaderT.goto_mkLabel {α ρ β} (x : Label α m β) (i : α) :
    goto (ReaderT.mkLabel ρ x) i = monadLift (goto x i) := by cases x; rfl

nonrec def ReaderT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ReaderT ε m) β → ReaderT ε m α) : ReaderT ε m α :=
  ReaderT.mk (fun r => callCC fun f' => (f <| ReaderT.mkLabel _ f').run r)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ρ} [MonadCont m] : MonadCont (ReaderT ρ m) where
  callCC := ReaderT.callCC
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ρ} [Monad m] [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (ReaderT ρ m) where
  callCC_bind_right := by intros; simp only [callCC, ReaderT.callCC, ReaderT.run_bind,
                                    callCC_bind_right]; ext; rfl
  callCC_bind_left := by
    intros; simp only [callCC, ReaderT.callCC, ReaderT.goto_mkLabel, ReaderT.run_bind,
      ReaderT.run_monadLift, monadLift_self, callCC_bind_left]
    ext; rfl
  callCC_dummy := by intros; simp only [callCC, ReaderT.callCC, @callCC_dummy m _]; ext; rfl

/-- reduce the equivalence between two continuation passing monads to the equivalence between
their underlying monad -/
/-
**ContT.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContT.equiv {m₁ : Type u₀ -> Type v₀} {m₂ : Type u₁ -> Type v₁} {α₁ r₁ : T
ype u₀} {α₂ r₂ : Type u₁} (F : m₁ r₁ ≃ m₂ r₂) (G : α₁ ≃ α₂) : ContT r₁ m₁ α₁ ≃ C
ontT r₂ m₂ α₂ where toFun f r
参数：F : m₁ r₁ ≃ m₂ r₂；G : α₁ ≃ α₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
reduce the equivalence between two continuation passing monads to the equivalenc
e between
their underlying monad
-/
def ContT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ r₁ : Type u₀}
    {α₂ r₂ : Type u₁} (F : m₁ r₁ ≃ m₂ r₂) (G : α₁ ≃ α₂) : ContT r₁ m₁ α₁ ≃ ContT r₂ m₂ α₂ where
  toFun f r := F <| f fun x => F.symm <| r <| G x
  invFun f r := F.symm <| f fun x => F <| r <| G.symm x
  left_inv f := by funext r; simp
  right_inv f := by funext r; simp
