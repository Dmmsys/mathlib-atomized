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

/--
Definition of `MonadCont.Label` / `MonadCont.Label` 的定义

English:
structure MonadCont.Label
  parameters: (α : Type w) (m : Type u -> Type v) (β : Type u)
  axioms and operations (1):
    - apply : α -> m β

中文:
结构 MonadCont.Label
  参数: (α : Type w) (m : 类型u -> 类型v) (β : 类型u)
  公理与运算 (1 个):
    - apply : α -> m β
-/
structure MonadCont.Label (α : Type w) (m : Type u -> Type v) (β : Type u) where
  apply : α -> m β

/--
Definition of `MonadCont.goto` / `MonadCont.goto` 的定义

English:
abbreviation MonadCont.goto
  signature: {α β} {m : Type u -> Type v} (f : MonadCont.Label α m β) (x : α)
  body: f.apply x

中文:
缩写 MonadCont.goto
  签名: {α β} {m : 类型u -> 类型v} (f : MonadCont.Label α m β) (x : α)
  定义体: f.apply x

Depends on / 依赖: f.apply
-/
abbrev MonadCont.goto {α β} {m : Type u -> Type v} (f : MonadCont.Label α m β) (x : α) :=
  f.apply x

/--
Definition of `MonadCont` / `MonadCont` 的定义

English:
class MonadCont
  parameters: (m : Type u -> Type v)
  axioms and operations (1):
    - callCC : forall {α β}, (MonadCont.Label α m β -> m α) -> m α

中文:
类 MonadCont
  参数: (m : 类型u -> 类型v)
  公理与运算 (1 个):
    - callCC : 对任意 {α β}, (MonadCont.Label α m β -> m α) -> m α
-/
class MonadCont (m : Type u -> Type v) where
  callCC : forall {α β}, (MonadCont.Label α m β -> m α) -> m α

open MonadCont

/--
Definition of `LawfulMonadCont` / `LawfulMonadCont` 的定义

English:
class LawfulMonadCont
  parameters: (m : Type u -> Type v) [Monad m] [MonadCont m]
  extends: LawfulMonad m
  axioms and operations (3):
    - callCC_bind_right({α ω γ} (cmd : m α) (next : Label ω m γ -> α -> m ω)) : (callCC fun f => cmd >>= next f) = cmd >>= fun x => callCC fun f => next f x
    - callCC_bind_left({α} (β) (x : α) (dead : Label α m β -> β -> m α)) : (callCC fun f : Label α m β => goto f x >>= dead f) = pure x
    - callCC_dummy({α β} (dummy : m α)) : (callCC fun _ : Label α m β => dummy) = dummy

中文:
类 LawfulMonadCont
  参数: (m : 类型u -> 类型v) [Monad m] [MonadCont m]
  继承: LawfulMonad m
  公理与运算 (3 个):
    - callCC_bind_right({α ω γ} (cmd : m α) (next : Label ω m γ -> α -> m ω)) : (callCC fun f => cmd >>= next f) = cmd >>= fun x => callCC fun f => next f x
    - callCC_bind_left({α} (β) (x : α) (dead : Label α m β -> β -> m α)) : (callCC fun f : Label α m β => goto f x >>= dead f) = pure x
    - callCC_dummy({α β} (dummy : m α)) : (callCC fun _ : Label α m β => dummy) = dummy
-/
class LawfulMonadCont (m : Type u -> Type v) [Monad m] [MonadCont m] : Prop
    extends LawfulMonad m where
  callCC_bind_right {α ω γ} (cmd : m α) (next : Label ω m γ -> α -> m ω) :
    (callCC fun f => cmd >>= next f) = cmd >>= fun x => callCC fun f => next f x
  callCC_bind_left {α} (β) (x : α) (dead : Label α m β -> β -> m α) :
    (callCC fun f : Label α m β => goto f x >>= dead f) = pure x
  callCC_dummy {α β} (dummy : m α) : (callCC fun _ : Label α m β => dummy) = dummy

export LawfulMonadCont (callCC_bind_right callCC_bind_left callCC_dummy)

/--
Definition of `ContT` / `ContT` 的定义

English:
definition ContT
  signature: (r : Type u) (m : Type u -> Type v) (α : Type w)
  body: (α -> m r) -> m r

中文:
定义 ContT
  签名: (r : 类型u) (m : 类型u -> 类型v) (α : Type w)
  定义体: (α -> m r) -> m r
-/
def ContT (r : Type u) (m : Type u -> Type v) (α : Type w) :=
  (α -> m r) -> m r

/--
Definition of `Cont` / `Cont` 的定义

English:
abbreviation Cont
  signature: (r : Type u) (α : Type w)
  body: ContT r Id α

中文:
缩写 Cont
  签名: (r : 类型u) (α : Type w)
  定义体: ContT r Id α
-/
abbrev Cont (r : Type u) (α : Type w) :=
  ContT r Id α

namespace ContT

export MonadCont (Label goto)

variable {r : Type u} {m : Type u -> Type v} {α β : Type w}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (f : (α -> m r) -> m r)
  body: f

中文:
定义 mk
  签名: (f : (α -> m r) -> m r)
  定义体: f
-/
def mk (f : (α -> m r) -> m r) : ContT r m α := f

/--
Definition of `run` / `run` 的定义

English:
definition run
  signature: (x : ContT r m α)
  body: x

中文:
定义 run
  签名: (x : ContT r m α)
  定义体: x
-/
def run (x : ContT r m α) : (α -> m r) -> m r := x

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : m r -> m r) (x : ContT r m α)
  body: f ∘ x

中文:
定义 map
  签名: (f : m r -> m r) (x : ContT r m α)
  定义体: f ∘ x
-/
def map (f : m r -> m r) (x : ContT r m α) : ContT r m α :=
  f ∘ x

/--
theorem `run_contT_map_contT` / 定理 `run_contT_map_contT`

English:
theorem run_contT_map_contT
  given: (f : m r -> m r) (x : ContT r m α)
  statement: run (map f x) = f ∘ run x
  proof: rfl

中文:
定理 run_contT_map_contT
  条件: (f : m r -> m r) (x : ContT r m α)
  结论: run (map f x) = f ∘ run x
  证明: rfl
-/
theorem run_contT_map_contT (f : m r -> m r) (x : ContT r m α) : run (map f x) = f ∘ run x :=
  rfl

/--
Definition of `withContT` / `withContT` 的定义

English:
definition withContT
  signature: (f : (β -> m r) -> α -> m r) (x : ContT r m α)
  body: fun g => x f g

中文:
定义 withContT
  签名: (f : (β -> m r) -> α -> m r) (x : ContT r m α)
  定义体: fun g => x f g
-/
def withContT (f : (β -> m r) -> α -> m r) (x : ContT r m α) : ContT r m β := fun g => x f g

/--
theorem `run_withContT` / 定理 `run_withContT`

English:
theorem run_withContT
  given: (f : (β -> m r) -> α -> m r) (x : ContT r m α)
  proof: rfl

@[ext]

中文:
定理 run_withContT
  条件: (f : (β -> m r) -> α -> m r) (x : ContT r m α)
  证明: rfl

@[ext]
-/
theorem run_withContT (f : (β -> m r) -> α -> m r) (x : ContT r m α) :
    run (withContT f x) = run x ∘ f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : ContT r m α} (h : forall f, x.run f = y.run f)
  statement: x = y
  proof: by
  unfold ContT; ext; apply h

中文:
定理 ext
  条件: {x y : ContT r m α} (h : 对任意 f, x.run f = y.run f)
  结论: x = y
  证明: by
  unfold ContT; ext; apply h
-/
protected theorem ext {x y : ContT r m α} (h : forall f, x.run f = y.run f) : x = y := by
  unfold ContT; ext; apply h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad (ContT r m)
  body: f x
  bind x f g := x fun i => f i g

@[simp]

中文:
实例 :
  签名: Monad (ContT r m)
  定义体: f x
  bind x f g := x fun i => f i g

@[simp]
-/
instance : Monad (ContT r m) where
  pure x f := f x
  bind x f g := x fun i => f i g

@[simp]
/--
theorem `run_mk` / 定理 `run_mk`

English:
theorem run_mk
  given: (f : (α -> m r) -> m r) (k : α -> m r)
  statement: (.mk f : ContT r m α).run k = f k
  proof: rfl

@[simp]

中文:
定理 run_mk
  条件: (f : (α -> m r) -> m r) (k : α -> m r)
  结论: (.mk f : ContT r m α).run k = f k
  证明: rfl

@[simp]
-/
theorem run_mk (f : (α -> m r) -> m r) (k : α -> m r) : (.mk f : ContT r m α).run k = f k := rfl

@[simp]
/--
theorem `run_pure` / 定理 `run_pure`

English:
theorem run_pure
  given: (a : α) (k : α -> m r)
  statement: (pure a : ContT r m α).run k = k a
  proof: rfl

@[simp]

中文:
定理 run_pure
  条件: (a : α) (k : α -> m r)
  结论: (pure a : ContT r m α).run k = k a
  证明: rfl

@[simp]
-/
theorem run_pure (a : α) (k : α -> m r) : (pure a : ContT r m α).run k = k a := rfl

@[simp]
/--
theorem `run_bind` / 定理 `run_bind`

English:
theorem run_bind
  given: (x : ContT r m α) (f : α -> ContT r m β) (k : β -> m r)
  proof: rfl

@[simp]

中文:
定理 run_bind
  条件: (x : ContT r m α) (f : α -> ContT r m β) (k : β -> m r)
  证明: rfl

@[simp]
-/
theorem run_bind (x : ContT r m α) (f : α -> ContT r m β) (k : β -> m r) :
    (x >>= f).run k = x.run fun x => (f x).run k := rfl

@[simp]
/--
theorem `run_map` / 定理 `run_map`

English:
theorem run_map
  given: (f : α -> β) (x : ContT r m α) (k : β -> m r)
  proof: rfl

@[simp]

中文:
定理 run_map
  条件: (f : α -> β) (x : ContT r m α) (k : β -> m r)
  证明: rfl

@[simp]
-/
theorem run_map (f : α -> β) (x : ContT r m α) (k : β -> m r) :
    (f <$> x).run k = x.run (k ∘ f) := rfl

@[simp]
/--
theorem `run_seq` / 定理 `run_seq`

English:
theorem run_seq
  given: (f : ContT r m (α -> β)) (x : ContT r m α) (k : β -> m r)
  proof: rfl

@[simp]

中文:
定理 run_seq
  条件: (f : ContT r m (α -> β)) (x : ContT r m α) (k : β -> m r)
  证明: rfl

@[simp]
-/
theorem run_seq (f : ContT r m (α -> β)) (x : ContT r m α) (k : β -> m r) :
    (f <*> x).run k = f.run fun f => x.run (k ∘ f) := rfl

@[simp]
/--
theorem `run_seqLeft` / 定理 `run_seqLeft`

English:
theorem run_seqLeft
  given: (x : ContT r m α) (y : ContT r m β) (k : α -> m r)
  proof: rfl

@[simp]

中文:
定理 run_seqLeft
  条件: (x : ContT r m α) (y : ContT r m β) (k : α -> m r)
  证明: rfl

@[simp]
-/
theorem run_seqLeft (x : ContT r m α) (y : ContT r m β) (k : α -> m r) :
    (x <* y).run k = x.run fun x => y.run fun _ => k x := rfl

@[simp]
/--
theorem `run_seqRight` / 定理 `run_seqRight`

English:
theorem run_seqRight
  given: (x : ContT r m α) (y : ContT r m β) (k : β -> m r)
  proof: rfl

中文:
定理 run_seqRight
  条件: (x : ContT r m α) (y : ContT r m β) (k : β -> m r)
  证明: rfl
-/
theorem run_seqRight (x : ContT r m α) (y : ContT r m β) (k : β -> m r) :
    (x *> y).run k = x.run fun _ => y.run k := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad (ContT r m)
  body: LawfulMonad.mk'
  (id_map := by intros; rfl)
  (pure_bind := by intros; ext; rfl)
  (bind_assoc := by intros; ext; rfl)

中文:
实例 :
  签名: LawfulMonad (ContT r m)
  定义体: LawfulMonad.mk'
  (id_map := by intros; rfl)
  (pure_bind := by intros; ext; rfl)
  (bind_assoc := by intros; ext; rfl)

Depends on / 依赖: LawfulMonad, LawfulMonad.mk
-/
instance : LawfulMonad (ContT r m) := LawfulMonad.mk'
  (id_map := by intros; rfl)
  (pure_bind := by intros; ext; rfl)
  (bind_assoc := by intros; ext; rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monad
  signature: m] : MonadLift m (ContT r m) where
  body: .mk fun k => x >>= k

@[simp]

中文:
实例 [Monad
  签名: m] : MonadLift m (ContT r m) where
  定义体: .mk fun k => x >>= k

@[simp]
-/
instance [Monad m] : MonadLift m (ContT r m) where
  monadLift x := .mk fun k => x >>= k

@[simp]
/--
theorem `run_monadLift` / 定理 `run_monadLift`

English:
theorem run_monadLift
  given: [Monad m] {α} (x : m α) (k : α -> m r)
  proof: rfl

中文:
定理 run_monadLift
  条件: [Monad m] {α} (x : m α) (k : α -> m r)
  证明: rfl
-/
theorem run_monadLift [Monad m] {α} (x : m α) (k : α -> m r) :
    (monadLift x : ContT r m α).run k = x >>= k := rfl

/--
theorem `monadLift_bind` / 定理 `monadLift_bind`

English:
theorem monadLift_bind
  given: [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α -> m β)
  proof: by
  ext
  simp only [bind_assoc, run_bind, run_monadLift, Function.comp_apply]

中文:
定理 monadLift_bind
  条件: [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α -> m β)
  证明: by
  ext
  simp only [bind_assoc, run_bind, run_monadLift, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, bind_assoc, comp_apply, run_bind, run_monadLift
-/
theorem monadLift_bind [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α -> m β) :
    (monadLift (x >>= f) : ContT r m β) = monadLift x >>= monadLift ∘ f := by
  ext
  simp only [bind_assoc, run_bind, run_monadLift, Function.comp_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonadCont (ContT r m)
  body: .mk fun k => f ⟨fun x => .mk fun _ => k x⟩ k

@[simp]

中文:
实例 :
  签名: MonadCont (ContT r m)
  定义体: .mk fun k => f ⟨fun x => .mk fun _ => k x⟩ k

@[simp]
-/
instance : MonadCont (ContT r m) where
  callCC f := .mk fun k => f ⟨fun x => .mk fun _ => k x⟩ k

@[simp]
/--
theorem `run_callCC` / 定理 `run_callCC`

English:
theorem run_callCC
  given: (f : Label α (ContT r m) β -> ContT r m α) (k : α -> m r)
  proof: rfl

中文:
定理 run_callCC
  条件: (f : Label α (ContT r m) β -> ContT r m α) (k : α -> m r)
  证明: rfl
-/
theorem run_callCC (f : Label α (ContT r m) β -> ContT r m α) (k : α -> m r) :
    (callCC f).run k = (f ⟨fun x => .mk fun _ => k x⟩).run k := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonadCont (ContT r m)
  body: by intros; ext; rfl
  callCC_bind_left := by intros; ext; rfl
  callCC_dummy := by intros; ext; rfl

中文:
实例 :
  签名: LawfulMonadCont (ContT r m)
  定义体: by intros; ext; rfl
  callCC_bind_left := by intros; ext; rfl
  callCC_dummy := by intros; ext; rfl

Depends on / 依赖: callCC_bind_left, callCC_dummy, intros
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
instance (ε) [MonadExceptOf ε m] : MonadExceptOf ε (ContT r m) where
  throw e := .mk fun _ => throw e
  tryCatch act h := .mk fun k => tryCatch (act.run k) fun e => (h e).run k

@[simp]
/--
theorem `run_throw` / 定理 `run_throw`

English:
theorem run_throw
  statement: {ε} [MonadExceptOf ε m]
  proof: rfl

@[simp]

中文:
定理 run_throw
  结论: {ε} [MonadExceptOf ε m]
  证明: rfl

@[simp]
-/
theorem run_throw {ε} [MonadExceptOf ε m]
    (e : ε) (f : α -> m r) :
    (throw e : ContT r m α).run f = throw e := rfl

@[simp]
/--
theorem `run_tryCatch` / 定理 `run_tryCatch`

English:
theorem run_tryCatch
  statement: {ε} [MonadExceptOf ε m]
  proof: rfl

中文:
定理 run_tryCatch
  结论: {ε} [MonadExceptOf ε m]
  证明: rfl
-/
theorem run_tryCatch {ε} [MonadExceptOf ε m]
    (act : ContT r m α) (h : ε -> ContT r m α) (f : α -> m r) :
    (tryCatch act h : ContT r m α).run f = tryCatch (act.run f) fun e => (h e).run f := rfl

end ContT

variable {m : Type u -> Type v}

section
variable [Monad m]

/--
Definition of `ExceptT.mkLabel` / `ExceptT.mkLabel` 的定义

English:
definition ExceptT.mkLabel
  signature: {α β ε}

中文:
定义 ExceptT.mkLabel
  签名: {α β ε}
-/
def ExceptT.mkLabel {α β ε} : Label (Except.{u, u} ε α) m β -> Label α (ExceptT ε m) β
| ⟨f⟩ => ⟨fun a => monadLift f (Except.ok a)⟩

/--
theorem `ExceptT.goto_mkLabel` / 定理 `ExceptT.goto_mkLabel`

English:
theorem ExceptT.goto_mkLabel
  given: {α β ε : Type _} (x : Label (Except.{u, u} ε α) m β) (i : α)
  proof: by
  cases x; rfl

nonrec def ExceptT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ExceptT ε m) β -> ExceptT ε m α) : ExceptT ε m α :=
  ExceptT.mk (callCC fun x : Label _ m β => ExceptT.run <| f (ExceptT.mkLabel x))

中文:
定理 ExceptT.goto_mkLabel
  条件: {α β ε : Type _} (x : Label (Except.{u, u} ε α) m β) (i : α)
  证明: by
  cases x; rfl

nonrec def ExceptT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ExceptT ε m) β -> ExceptT ε m α) : ExceptT ε m α :=
  ExceptT.mk (callCC fun x : Label _ m β => ExceptT.run <| f (ExceptT.mkLabel x))
-/
theorem ExceptT.goto_mkLabel {α β ε : Type _} (x : Label (Except.{u, u} ε α) m β) (i : α) :
    goto (ExceptT.mkLabel x) i = ExceptT.mk (Except.ok <$> goto x (Except.ok i)) := by
  cases x; rfl

nonrec def ExceptT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ExceptT ε m) β -> ExceptT ε m α) : ExceptT ε m α :=
  ExceptT.mk (callCC fun x : Label _ m β => ExceptT.run <| f (ExceptT.mkLabel x))

instance {ε} [MonadCont m] : MonadCont (ExceptT ε m) where
  callCC := ExceptT.callCC

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

/--
Definition of `OptionT.mkLabel` / `OptionT.mkLabel` 的定义

English:
definition OptionT.mkLabel
  signature: {α β}

中文:
定义 OptionT.mkLabel
  签名: {α β}
-/
def OptionT.mkLabel {α β} : Label (Option.{u} α) m β -> Label α (OptionT m) β
| ⟨f⟩ => ⟨fun a => monadLift f (some a)⟩

/--
theorem `OptionT.goto_mkLabel` / 定理 `OptionT.goto_mkLabel`

English:
theorem OptionT.goto_mkLabel
  given: {α β : Type _} (x : Label (Option.{u} α) m β) (i : α)
  proof: (rfl)

nonrec def OptionT.callCC [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β -> OptionT m α) :
    OptionT m α :=
  OptionT.mk (callCC fun x : Label _ m β => OptionT.run <| f (OptionT.mkLabel x) : m (Option α))

@[simp]

中文:
定理 OptionT.goto_mkLabel
  条件: {α β : Type _} (x : Label (Option.{u} α) m β) (i : α)
  证明: (rfl)

nonrec def OptionT.callCC [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β -> OptionT m α) :
    OptionT m α :=
  OptionT.mk (callCC fun x : Label _ m β => OptionT.run <| f (OptionT.mkLabel x) : m (Option α))

@[simp]
-/
theorem OptionT.goto_mkLabel {α β : Type _} (x : Label (Option.{u} α) m β) (i : α) :
    goto (OptionT.mkLabel x) i = OptionT.mk (goto x (some i) >>= fun a => pure (some a)) :=
  (rfl)

nonrec def OptionT.callCC [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β -> OptionT m α) :
    OptionT m α :=
  OptionT.mk (callCC fun x : Label _ m β => OptionT.run <| f (OptionT.mkLabel x) : m (Option α))

@[simp]
/--
lemma `run_callCC` / 引理 `run_callCC`

English:
lemma run_callCC
  given: [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β -> OptionT m α)
  proof: (rfl)

中文:
引理 run_callCC
  条件: [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β -> OptionT m α)
  证明: (rfl)
-/
lemma run_callCC [MonadCont m] {α β : Type _} (f : Label α (OptionT m) β -> OptionT m α) :
    (OptionT.callCC f).run = (callCC fun x => OptionT.run <| f (OptionT.mkLabel x)) := (rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonadCont
  signature: m] : MonadCont (OptionT m) where
  body: OptionT.callCC

中文:
实例 [MonadCont
  签名: m] : MonadCont (OptionT m) where
  定义体: OptionT.callCC

Depends on / 依赖: OptionT, OptionT.callCC, callCC
-/
instance [MonadCont m] : MonadCont (OptionT m) where
  callCC := OptionT.callCC

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonadCont
  signature: m] [LawfulMonadCont m] : LawfulMonadCont (OptionT m) where
  body: by
    refine fun _ _ => OptionT.ext ?_
    simpa [callCC, Option.elimM, callCC_bind_right] using
      bind_congr fun | some _ => rfl | none => by simp [@callCC_dummy m _]
  callCC_bind_left := by
    intros
    ext
    simp [callCC, OptionT.goto_mkLabel, @callCC_bind_left m _]
  callCC_dummy := by

中文:
实例 [MonadCont
  签名: m] [LawfulMonadCont m] : LawfulMonadCont (OptionT m) where
  定义体: by
    refine fun _ _ => OptionT.ext ?_
    simpa [callCC, Option.elimM, callCC_bind_right] using
      bind_congr fun | some _ => rfl | none => by simp [@callCC_dummy m _]
  callCC_bind_left := by
    intros
    ext
    simp [callCC, OptionT.goto_mkLabel, @callCC_bind_left m _]
  callCC_dummy := by

Depends on / 依赖: Option.elimM, OptionT, OptionT.callCC, OptionT.ext, OptionT.goto_mkLabel, bind_congr, callCC, callCC_bind_left, callCC_bind_right, callCC_dummy, goto_mkLabel, intros
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

/--
Definition of `WriterT.mkLabel` / `WriterT.mkLabel` 的定义

English:
definition WriterT.mkLabel
  signature: {α β ω} [EmptyCollection ω]

中文:
定义 WriterT.mkLabel
  签名: {α β ω} [EmptyCollection ω]
-/
def WriterT.mkLabel {α β ω} [EmptyCollection ω] : Label (α × ω) m β -> Label α (WriterT ω m) β
| ⟨f⟩ => ⟨fun a => monadLift f (a, ∅)⟩

/--
Definition of `WriterT.mkLabel'` / `WriterT.mkLabel'` 的定义

English:
definition WriterT.mkLabel'
  signature: {α β ω} [Monoid ω]

中文:
定义 WriterT.mkLabel'
  签名: {α β ω} [Monoid ω]
-/
def WriterT.mkLabel' {α β ω} [Monoid ω] : Label (α × ω) m β -> Label α (WriterT ω m) β
| ⟨f⟩ => ⟨fun a => monadLift f (a, 1)⟩

/--
theorem `WriterT.goto_mkLabel` / 定理 `WriterT.goto_mkLabel`

English:
theorem WriterT.goto_mkLabel
  given: {α β ω : Type _} [EmptyCollection ω] (x : Label (α × ω) m β) (i : α)
  proof: by cases x; rfl

中文:
定理 WriterT.goto_mkLabel
  条件: {α β ω : Type _} [EmptyCollection ω] (x : Label (α × ω) m β) (i : α)
  证明: by cases x; rfl
-/
theorem WriterT.goto_mkLabel {α β ω : Type _} [EmptyCollection ω] (x : Label (α × ω) m β) (i : α) :
    goto (WriterT.mkLabel x) i = monadLift (goto x (i, ∅)) := by cases x; rfl

/--
theorem `WriterT.goto_mkLabel'` / 定理 `WriterT.goto_mkLabel'`

English:
theorem WriterT.goto_mkLabel'
  given: {α β ω : Type _} [Monoid ω] (x : Label (α × ω) m β) (i : α)
  proof: by cases x; rfl

nonrec def WriterT.callCC [MonadCont m] {α β ω : Type _} [EmptyCollection ω]
    (f : Label α (WriterT ω m) β -> WriterT ω m α) : WriterT ω m α :=
WriterT.mk callCC (WriterT.run ∘ f ∘ WriterT.mkLabel : Label (α × ω) m β -> m (α × ω))

中文:
定理 WriterT.goto_mkLabel'
  条件: {α β ω : Type _} [Monoid ω] (x : Label (α × ω) m β) (i : α)
  证明: by cases x; rfl

nonrec def WriterT.callCC [MonadCont m] {α β ω : Type _} [EmptyCollection ω]
    (f : Label α (WriterT ω m) β -> WriterT ω m α) : WriterT ω m α :=
WriterT.mk callCC (WriterT.run ∘ f ∘ WriterT.mkLabel : Label (α × ω) m β -> m (α × ω))
-/
theorem WriterT.goto_mkLabel' {α β ω : Type _} [Monoid ω] (x : Label (α × ω) m β) (i : α) :
    goto (WriterT.mkLabel' x) i = monadLift (goto x (i, 1)) := by cases x; rfl

nonrec def WriterT.callCC [MonadCont m] {α β ω : Type _} [EmptyCollection ω]
    (f : Label α (WriterT ω m) β -> WriterT ω m α) : WriterT ω m α :=
WriterT.mk callCC (WriterT.run ∘ f ∘ WriterT.mkLabel : Label (α × ω) m β -> m (α × ω))

/--
Definition of `WriterT.callCC'` / `WriterT.callCC'` 的定义

English:
definition WriterT.callCC'
  signature: [MonadCont m] {α β ω : Type _} [Monoid ω]
  body: WriterT.mk
    MonadCont.callCC (WriterT.run ∘ f ∘ WriterT.mkLabel' : Label (α × ω) m β -> m (α × ω))

中文:
定义 WriterT.callCC'
  签名: [MonadCont m] {α β ω : Type _} [Monoid ω]
  定义体: WriterT.mk
    MonadCont.callCC (WriterT.run ∘ f ∘ WriterT.mkLabel' : Label (α × ω) m β -> m (α × ω))

Depends on / 依赖: MonadCont, MonadCont.callCC, WriterT, WriterT.mk, WriterT.mkLabel, WriterT.run, callCC, mkLabel
-/
def WriterT.callCC' [MonadCont m] {α β ω : Type _} [Monoid ω]
    (f : Label α (WriterT ω m) β -> WriterT ω m α) : WriterT ω m α :=
WriterT.mk
    MonadCont.callCC (WriterT.run ∘ f ∘ WriterT.mkLabel' : Label (α × ω) m β -> m (α × ω))

end

instance (ω) [Monad m] [EmptyCollection ω] [MonadCont m] : MonadCont (WriterT ω m) where
  callCC := WriterT.callCC

instance (ω) [Monad m] [Monoid ω] [MonadCont m] : MonadCont (WriterT ω m) where
  callCC := WriterT.callCC'

/--
Definition of `StateT.mkLabel` / `StateT.mkLabel` 的定义

English:
definition StateT.mkLabel
  signature: {α β σ : Type u}

中文:
定义 StateT.mkLabel
  签名: {α β σ : 类型u}

Depends on / 依赖: Nat.xor_assoc, xor_assoc
-/
def StateT.mkLabel {α β σ : Type u} : Label (α × σ) m (β × σ) -> Label α (StateT σ m) β
  | ⟨f⟩ => ⟨fun a => StateT.mk (fun s => f (a, s))⟩

/--
theorem `StateT.goto_mkLabel` / 定理 `StateT.goto_mkLabel`

English:
theorem StateT.goto_mkLabel
  given: {α β σ : Type u} (x : Label (α × σ) m (β × σ)) (i : α)
  proof: by cases x; rfl

nonrec def StateT.callCC {σ} [MonadCont m] {α β : Type _}
    (f : Label α (StateT σ m) β -> StateT σ m α) : StateT σ m α :=
  StateT.mk (fun r => callCC fun f' => (f <| StateT.mkLabel f').run r)

中文:
定理 StateT.goto_mkLabel
  条件: {α β σ : 类型u} (x : Label (α × σ) m (β × σ)) (i : α)
  证明: by cases x; rfl

nonrec def StateT.callCC {σ} [MonadCont m] {α β : Type _}
    (f : Label α (StateT σ m) β -> StateT σ m α) : StateT σ m α :=
  StateT.mk (fun r => callCC fun f' => (f <| StateT.mkLabel f').run r)

Depends on / 依赖: Fin.xor_assoc, xor_assoc
-/
theorem StateT.goto_mkLabel {α β σ : Type u} (x : Label (α × σ) m (β × σ)) (i : α) :
    goto (StateT.mkLabel x) i = StateT.mk (fun s => goto x (i, s)) := by cases x; rfl

nonrec def StateT.callCC {σ} [MonadCont m] {α β : Type _}
    (f : Label α (StateT σ m) β -> StateT σ m α) : StateT σ m α :=
  StateT.mk (fun r => callCC fun f' => (f <| StateT.mkLabel f').run r)

instance {σ} [MonadCont m] : MonadCont (StateT σ m) where
  callCC := StateT.callCC

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

/--
Definition of `ReaderT.mkLabel` / `ReaderT.mkLabel` 的定义

English:
definition ReaderT.mkLabel
  signature: {α β} (ρ)

中文:
定义 ReaderT.mkLabel
  签名: {α β} (ρ)

Depends on / 依赖: BitVec, BitVec.xor_assoc, xor_assoc
-/
def ReaderT.mkLabel {α β} (ρ) : Label α m β -> Label α (ReaderT ρ m) β
  | ⟨f⟩ => ⟨monadLift ∘ f⟩

/--
theorem `ReaderT.goto_mkLabel` / 定理 `ReaderT.goto_mkLabel`

English:
theorem ReaderT.goto_mkLabel
  given: {α ρ β} (x : Label α m β) (i : α)
  proof: by cases x; rfl

nonrec def ReaderT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ReaderT ε m) β -> ReaderT ε m α) : ReaderT ε m α :=
  ReaderT.mk (fun r => callCC fun f' => (f <| ReaderT.mkLabel _ f').run r)

中文:
定理 ReaderT.goto_mkLabel
  条件: {α ρ β} (x : Label α m β) (i : α)
  证明: by cases x; rfl

nonrec def ReaderT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ReaderT ε m) β -> ReaderT ε m α) : ReaderT ε m α :=
  ReaderT.mk (fun r => callCC fun f' => (f <| ReaderT.mkLabel _ f').run r)
-/
theorem ReaderT.goto_mkLabel {α ρ β} (x : Label α m β) (i : α) :
    goto (ReaderT.mkLabel ρ x) i = monadLift (goto x i) := by cases x; rfl

nonrec def ReaderT.callCC {ε} [MonadCont m] {α β : Type _}
    (f : Label α (ReaderT ε m) β -> ReaderT ε m α) : ReaderT ε m α :=
  ReaderT.mk (fun r => callCC fun f' => (f <| ReaderT.mkLabel _ f').run r)

instance {ρ} [MonadCont m] : MonadCont (ReaderT ρ m) where
  callCC := ReaderT.callCC

instance {ρ} [Monad m] [MonadCont m] [LawfulMonadCont m] : LawfulMonadCont (ReaderT ρ m) where
  callCC_bind_right := by intros; simp only [callCC, ReaderT.callCC, ReaderT.run_bind,
                                    callCC_bind_right]; ext; rfl
  callCC_bind_left := by
    intros; simp only [callCC, ReaderT.callCC, ReaderT.goto_mkLabel, ReaderT.run_bind,
      ReaderT.run_monadLift, monadLift_self, callCC_bind_left]
    ext; rfl
  callCC_dummy := by intros; simp only [callCC, ReaderT.callCC, @callCC_dummy m _]; ext; rfl

/--
Definition of `ContT.equiv` / `ContT.equiv` 的定义

English:
definition ContT.equiv
  signature: {m₁ : Type u₀ -> Type v₀} {m₂ : Type u₁ -> Type v₁} {α₁ r₁ : Type u₀}
  body: F f fun x => F.symm r G x
invFun f r := F.symm f fun x => F r G.symm x
  left_inv f := by funext r; simp
  right_inv f := by funext r; simp

中文:
定义 ContT.equiv
  签名: {m₁ : 类型u₀ -> 类型v₀} {m₂ : 类型u₁ -> 类型v₁} {α₁ r₁ : 类型u₀}
  定义体: F f fun x => F.symm r G x
invFun f r := F.symm f fun x => F r G.symm x
  left_inv f := by funext r; simp
  right_inv f := by funext r; simp

Depends on / 依赖: F.symm
-/
def ContT.equiv {m₁ : Type u₀ -> Type v₀} {m₂ : Type u₁ -> Type v₁} {α₁ r₁ : Type u₀}
    {α₂ r₂ : Type u₁} (F : m₁ r₁ ≃ m₂ r₂) (G : α₁ ≃ α₂) : ContT r₁ m₁ α₁ ≃ ContT r₂ m₂ α₂ where
toFun f r := F f fun x => F.symm r G x
invFun f r := F.symm f fun x => F r G.symm x
  left_inv f := by funext r; simp
  right_inv f := by funext r; simp
