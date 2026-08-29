/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Edward Ayers, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Logic.Equiv.Defs

/-!
# Writer monads

This file introduces monads for managing immutable, appendable state.
Common applications are logging monads where the monad logs messages as the
computation progresses.

## References
- https://hackage.haskell.org/package/mtl-2.2.1/docs/Control-Monad-Writer-Class.html
- [Original Mark P Jones article introducing `Writer`](https://web.cecs.pdx.edu/~mpj/pubs/springschool.html)

-/

@[expose] public section

universe u v

/--
Definition of `WriterT` / `WriterT` 的定义

English:
definition WriterT
  signature: (ω : Type u) (M : Type u -> Type v) (α : Type u)
  body: M (α × ω)

中文:
定义 WriterT
  签名: (ω : 类型u) (M : 类型u -> 类型v) (α : 类型u)
  定义体: M (α × ω)
-/
def WriterT (ω : Type u) (M : Type u -> Type v) (α : Type u) : Type v :=
  M (α × ω)

/--
Definition of `Writer` / `Writer` 的定义

English:
abbreviation Writer
  signature: ω
  body: WriterT ω Id

中文:
缩写 Writer
  签名: ω
  定义体: WriterT ω Id

Depends on / 依赖: WriterT
-/
abbrev Writer ω := WriterT ω Id

/--
Definition of `MonadWriter` / `MonadWriter` 的定义

English:
class MonadWriter
  parameters: (ω : outParam (Type u)) (M : Type u -> Type v)
  axioms and operations (3):
    - tell((w : ω)) : M PUnit
    - listen({α} (f : M α)) : M (α × ω)
    - pass({α} (f : M (α × (ω -> ω)))) : M α

中文:
类 MonadWriter
  参数: (ω : outParam (类型u)) (M : 类型u -> 类型v)
  公理与运算 (3 个):
    - tell((w : ω)) : M 命题单元
    - listen({α} (f : M α)) : M (α × ω)
    - pass({α} (f : M (α × (ω -> ω)))) : M α
-/
class MonadWriter (ω : outParam (Type u)) (M : Type u -> Type v) where
  /-- Emit an output `w`. -/
  tell (w : ω) : M PUnit
  /-- Capture the output produced by `f`, without intercepting. -/
  listen {α} (f : M α) : M (α × ω)
  /-- Buffer the output produced by `f` as `w`, then emit `(← f).2 w` in its place. -/
  pass {α} (f : M (α × (ω -> ω))) : M α

export MonadWriter (tell listen pass)

variable {M : Type u -> Type v} {α β ω ρ σ : Type u}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonadWriter
  signature: ω M] : MonadWriter ω (ReaderT ρ M) where
  body: (tell w : M _)
listen x r := listen x r
pass x r := pass x r

中文:
实例 [MonadWriter
  签名: ω M] : MonadWriter ω (ReaderT ρ M) where
  定义体: (tell w : M _)
listen x r := listen x r
pass x r := pass x r

Depends on / 依赖: Int8.xor_assoc, xor_assoc
-/
instance [MonadWriter ω M] : MonadWriter ω (ReaderT ρ M) where
  tell w := (tell w : M _)
listen x r := listen x r
pass x r := pass x r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monad
  signature: M] [MonadWriter ω M] : MonadWriter ω (StateT σ M) where
  body: (tell w : M _)
listen x s := (fun ((a, w), s) => ((a, s), w)) < > listen (x s)
pass x s := pass (fun ((a, f), s) => ((a, s), f)) < > (x s)

中文:
实例 [单子
  签名: M] [MonadWriter ω M] : MonadWriter ω (StateT σ M) where
  定义体: (tell w : M _)
listen x s := (fun ((a, w), s) => ((a, s), w)) < > listen (x s)
pass x s := pass (fun ((a, f), s) => ((a, s), f)) < > (x s)

Depends on / 依赖: Int16.xor_assoc, xor_assoc
-/
instance [Monad M] [MonadWriter ω M] : MonadWriter ω (StateT σ M) where
  tell w := (tell w : M _)
listen x s := (fun ((a, w), s) => ((a, s), w)) < > listen (x s)
pass x s := pass (fun ((a, f), s) => ((a, s), f)) < > (x s)

namespace WriterT

@[inline]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {ω : Type u} (cmd : M (α × ω))
  body: cmd
@[inline]

中文:
定义 mk
  签名: {ω : 类型u} (cmd : M (α × ω))
  定义体: cmd
@[inline]
-/
protected def mk {ω : Type u} (cmd : M (α × ω)) : WriterT ω M α := cmd
@[inline]
/--
Definition of `run` / `run` 的定义

English:
definition run
  signature: {ω : Type u} (cmd : WriterT ω M α)
  body: cmd

中文:
定义 run
  签名: {ω : 类型u} (cmd : WriterT ω M α)
  定义体: cmd
-/
protected def run {ω : Type u} (cmd : WriterT ω M α) : M (α × ω) := cmd

/--
Definition of `runThe` / `runThe` 的定义

English:
abbreviation runThe
  signature: (ω : Type u) (cmd : WriterT ω M α)
  body: cmd.run

中文:
缩写 runThe
  签名: (ω : 类型u) (cmd : WriterT ω M α)
  定义体: cmd.run

Depends on / 依赖: cmd.run
-/
abbrev runThe (ω : Type u) (cmd : WriterT ω M α) : M (α × ω) := cmd.run

/--
theorem `run_mk` / 定理 `run_mk`

English:
theorem run_mk
  given: {ω : Type u} (cmd : M (α × ω))
  statement: (WriterT.mk cmd).run = cmd
  proof: rfl

@[ext]

中文:
定理 run_mk
  条件: {ω : 类型u} (cmd : M (α × ω))
  结论: (WriterT.mk cmd).run = cmd
  证明: rfl

@[ext]
-/
@[simp] theorem run_mk {ω : Type u} (cmd : M (α × ω)) : (WriterT.mk cmd).run = cmd := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {ω : Type u} (x x' : WriterT ω M α) (h : x.run = x'.run)
  statement: x = x'
  proof: h

中文:
定理 ext
  条件: {ω : 类型u} (x x' : WriterT ω M α) (h : x.run = x'.run)
  结论: x = x'
  证明: h
-/
protected theorem ext {ω : Type u} (x x' : WriterT ω M α) (h : x.run = x'.run) : x = x' := h

variable [Monad M]

/-- Creates an instance of `Monad`, with explicitly given `empty` and `append` operations.

Previously, this would have used an instance of `[Monoid ω]` as input.
In practice, however, `WriterT` is used for logging and creating lists so restricting to
monoids with `Mul` and `One` can make `WriterT` cumbersome to use.

This is used to derive instances for both `[EmptyCollection ω] [Append ω]` and `[Monoid ω]`.
-/
@[reducible, inline]
/--
Definition of `monad` / `monad` 的定义

English:
definition monad
  signature: (empty : ω) (append : ω -> ω -> ω)
  body: fun f cmd => WriterT.mk (fun (a, w) => (f a, w)) < > cmd.run
  pure := fun a => pure (f := M) (a, empty)
  bind := fun cmd f =>
WriterT.mk cmd.run >>= fun (a, w₁) =>
(fun (b, w₂) => (b, append w₁ w₂)) < > (f a).run

@[simp]

中文:
定义 monad
  签名: (empty : ω) (append : ω -> ω -> ω)
  定义体: fun f cmd => WriterT.mk (fun (a, w) => (f a, w)) < > cmd.run
  pure := fun a => pure (f := M) (a, empty)
  bind := fun cmd f =>
WriterT.mk cmd.run >>= fun (a, w₁) =>
(fun (b, w₂) => (b, append w₁ w₂)) < > (f a).run

@[simp]

Depends on / 依赖: WriterT, WriterT.mk, cmd.run
-/
def monad (empty : ω) (append : ω -> ω -> ω) : Monad (WriterT ω M) where
map := fun f cmd => WriterT.mk (fun (a, w) => (f a, w)) < > cmd.run
  pure := fun a => pure (f := M) (a, empty)
  bind := fun cmd f =>
WriterT.mk cmd.run >>= fun (a, w₁) =>
(fun (b, w₂) => (b, append w₁ w₂)) < > (f a).run

@[simp]
/--
theorem `run_pure` / 定理 `run_pure`

English:
theorem run_pure
  given: (empty : ω) (append : ω -> ω -> ω) (a : α)
  proof: monad empty append
    (pure a : WriterT ω M α).run = pure (a, empty) :=
  rfl

@[simp]

中文:
定理 run_pure
  条件: (empty : ω) (append : ω -> ω -> ω) (a : α)
  证明: monad empty append
    (pure a : WriterT ω M α).run = pure (a, empty) :=
  rfl

@[simp]

Depends on / 依赖: append
-/
theorem run_pure (empty : ω) (append : ω -> ω -> ω) (a : α) :
    letI : Monad (WriterT ω M) := monad empty append
    (pure a : WriterT ω M α).run = pure (a, empty) :=
  rfl

@[simp]
/--
theorem `run_map` / 定理 `run_map`

English:
theorem run_map
  given: (empty : ω) (append : ω -> ω -> ω) (f : α -> β) (cmd : WriterT ω M α)
  proof: monad empty append
(f <$> cmd).run = (fun (a, w) => (f a, w)) < > cmd.run :=
  rfl

@[simp]

中文:
定理 run_map
  条件: (empty : ω) (append : ω -> ω -> ω) (f : α -> β) (cmd : WriterT ω M α)
  证明: monad empty append
(f <$> cmd).run = (fun (a, w) => (f a, w)) < > cmd.run :=
  rfl

@[simp]

Depends on / 依赖: append
-/
theorem run_map (empty : ω) (append : ω -> ω -> ω) (f : α -> β) (cmd : WriterT ω M α) :
    letI : Monad (WriterT ω M) := monad empty append
(f <$> cmd).run = (fun (a, w) => (f a, w)) < > cmd.run :=
  rfl

@[simp]
/--
theorem `run_bind` / 定理 `run_bind`

English:
theorem run_bind
  statement: (empty : ω) (append : ω -> ω -> ω)
  proof: monad empty append
    (cmd >>= f).run = cmd.run >>= fun (a, w₁) =>
(fun (b, w₂) => (b, append w₁ w₂)) < > (f a).run :=
  rfl

中文:
定理 run_bind
  结论: (empty : ω) (append : ω -> ω -> ω)
  证明: monad empty append
    (cmd >>= f).run = cmd.run >>= fun (a, w₁) =>
(fun (b, w₂) => (b, append w₁ w₂)) < > (f a).run :=
  rfl

Depends on / 依赖: append
-/
theorem run_bind (empty : ω) (append : ω -> ω -> ω)
    (cmd : WriterT ω M α) (f : α -> WriterT ω M β) :
    letI : Monad (WriterT ω M) := monad empty append
    (cmd >>= f).run = cmd.run >>= fun (a, w₁) =>
(fun (b, w₂) => (b, append w₁ w₂)) < > (f a).run :=
  rfl

/-- Lift an `M` to a `WriterT ω M`, using the given `empty` as the monoid unit. -/
@[inline, instance_reducible]
/--
Definition of `liftTell` / `liftTell` 的定义

English:
definition liftTell
  signature: (empty : ω)
  body: fun cmd => WriterT.mk (fun a => (a, empty)) < > cmd

@[simp]

中文:
定义 liftTell
  签名: (empty : ω)
  定义体: fun cmd => WriterT.mk (fun a => (a, empty)) < > cmd

@[simp]
-/
protected def liftTell (empty : ω) : MonadLift M (WriterT ω M) where
monadLift := fun cmd => WriterT.mk (fun a => (a, empty)) < > cmd

@[simp]
/--
theorem `run_liftM` / 定理 `run_liftM`

English:
theorem run_liftM
  given: (empty : ω) (cmd : M α)
  proof: WriterT.liftTell empty
(cmd : WriterT ω M α).run = (fun a => (a, empty)) < > cmd :=
  rfl

中文:
定理 run_liftM
  条件: (empty : ω) (cmd : M α)
  证明: WriterT.liftTell empty
(cmd : WriterT ω M α).run = (fun a => (a, empty)) < > cmd :=
  rfl

Depends on / 依赖: WriterT, WriterT.liftTell, liftTell
-/
theorem run_liftM (empty : ω) (cmd : M α) :
    letI : MonadLift M (WriterT ω M) := WriterT.liftTell empty
(cmd : WriterT ω M α).run = (fun a => (a, empty)) < > cmd :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EmptyCollection
  signature: ω] [Append ω] : Monad (WriterT ω M)
  body: monad ∅ (· ++ ·)

中文:
实例 [EmptyCollection
  签名: ω] [Append ω] : 单子 (WriterT ω M)
  定义体: monad ∅ (· ++ ·)
-/
instance [EmptyCollection ω] [Append ω] : Monad (WriterT ω M) := monad ∅ (· ++ ·)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EmptyCollection
  signature: ω] : MonadLift M (WriterT ω M)
  body: WriterT.liftTell ∅

中文:
实例 [EmptyCollection
  签名: ω] : MonadLift M (WriterT ω M)
  定义体: WriterT.liftTell ∅

Depends on / 依赖: WriterT, WriterT.liftTell, liftTell
-/
instance [EmptyCollection ω] : MonadLift M (WriterT ω M) := WriterT.liftTell ∅
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: ω] : Monad (WriterT ω M)
  body: monad 1 (· * ·)

中文:
实例 [幺半群
  签名: ω] : 单子 (WriterT ω M)
  定义体: monad 1 (· * ·)
-/
instance [Monoid ω] : Monad (WriterT ω M) := monad 1 (· * ·)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: ω] : MonadLift M (WriterT ω M)
  body: WriterT.liftTell 1

中文:
实例 [幺半群
  签名: ω] : MonadLift M (WriterT ω M)
  定义体: WriterT.liftTell 1

Depends on / 依赖: WriterT, WriterT.liftTell, liftTell
-/
instance [Monoid ω] : MonadLift M (WriterT ω M) := WriterT.liftTell 1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: ω] [LawfulMonad M] : LawfulMonad (WriterT ω M)
  body: LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => by ext; simp)
  (id_map := fun _ => by ext; simp)
  (pure_bind := fun _ _ => by ext; simp)
  (bind_assoc := fun _ _ _ => by ext; simp [mul_assoc])

中文:
实例 [幺半群
  签名: ω] [合法单子 M] : 合法单子 (WriterT ω M)
  定义体: LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => by ext; simp)
  (id_map := fun _ => by ext; simp)
  (pure_bind := fun _ _ => by ext; simp)
  (bind_assoc := fun _ _ _ => by ext; simp [mul_assoc])

Depends on / 依赖: LawfulMonad, LawfulMonad.mk
-/
instance [Monoid ω] [LawfulMonad M] : LawfulMonad (WriterT ω M) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => by ext; simp)
  (id_map := fun _ => by ext; simp)
  (pure_bind := fun _ _ => by ext; simp)
  (bind_assoc := fun _ _ _ => by ext; simp [mul_assoc])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonadWriter ω (WriterT ω M)
  body: fun w => WriterT.mk pure (⟨⟩, w)
listen := fun cmd => WriterT.mk (fun (a, w) => ((a, w), w)) < > cmd.run
pass := fun cmd => WriterT.mk (fun ((a, f), w) => (a, f w)) < > cmd.run

@[simp]

中文:
实例 :
  签名: MonadWriter ω (WriterT ω M)
  定义体: fun w => WriterT.mk pure (⟨⟩, w)
listen := fun cmd => WriterT.mk (fun (a, w) => ((a, w), w)) < > cmd.run
pass := fun cmd => WriterT.mk (fun ((a, f), w) => (a, f w)) < > cmd.run

@[simp]

Depends on / 依赖: WriterT, WriterT.mk
-/
instance : MonadWriter ω (WriterT ω M) where
tell := fun w => WriterT.mk pure (⟨⟩, w)
listen := fun cmd => WriterT.mk (fun (a, w) => ((a, w), w)) < > cmd.run
pass := fun cmd => WriterT.mk (fun ((a, f), w) => (a, f w)) < > cmd.run

@[simp]
/--
theorem `run_tell` / 定理 `run_tell`

English:
theorem run_tell
  given: (w : ω)
  proof: rfl

@[simp]

中文:
定理 run_tell
  条件: (w : ω)
  证明: rfl

@[simp]
-/
theorem run_tell (w : ω) :
    WriterT.run (MonadWriter.tell w : WriterT ω M PUnit) = pure (⟨⟩, w) := rfl

@[simp]
/--
theorem `run_listen` / 定理 `run_listen`

English:
theorem run_listen
  given: (cmd : WriterT ω M α)
  proof: rfl

@[simp]

中文:
定理 run_listen
  条件: (cmd : WriterT ω M α)
  证明: rfl

@[simp]
-/
theorem run_listen (cmd : WriterT ω M α) :
WriterT.run (MonadWriter.listen cmd) = (fun (a, w) => ((a, w), w)) < > cmd.run :=
  rfl

@[simp]
/--
theorem `run_pass` / 定理 `run_pass`

English:
theorem run_pass
  given: (cmd : WriterT ω M (α × (ω -> ω)))
  proof: rfl

中文:
定理 run_pass
  条件: (cmd : WriterT ω M (α × (ω -> ω)))
  证明: rfl
-/
theorem run_pass (cmd : WriterT ω M (α × (ω -> ω))) :
WriterT.run (MonadWriter.pass cmd) = (fun ((a, f), w) => (a, f w)) < > cmd.run :=
  rfl

instance {ε : Type*} [MonadExceptOf ε M] : MonadExceptOf ε (WriterT ω M) where
throw := fun e => WriterT.mk throw e
tryCatch := fun cmd c => WriterT.mk tryCatch cmd.run fun e => (c e).run

@[simp]
/--
theorem `run_throw` / 定理 `run_throw`

English:
theorem run_throw
  given: {M} {ε : Type*} [MonadExceptOf ε M] (e : ε)
  proof: rfl

@[simp]

中文:
定理 run_throw
  条件: {M} {ε : 类型} [MonadExceptOf ε M] (e : ε)
  证明: rfl

@[simp]
-/
theorem run_throw {M} {ε : Type*} [MonadExceptOf ε M] (e : ε) :
    (throw e : WriterT ω M α).run = throw e :=
  rfl

@[simp]
/--
theorem `run_tryCatch` / 定理 `run_tryCatch`

English:
theorem run_tryCatch
  statement: {M} {ε : Type*} [MonadExceptOf ε M]
  proof: rfl

中文:
定理 run_tryCatch
  结论: {M} {ε : 类型} [MonadExceptOf ε M]
  证明: rfl
-/
theorem run_tryCatch {M} {ε : Type*} [MonadExceptOf ε M]
    (cmd : WriterT ω M α) (c : ε -> WriterT ω M α) :
    (tryCatch cmd c : WriterT ω M α).run = tryCatch cmd.run fun e => (c e).run :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonadLiftT
  signature: M (WriterT ω M)] : MonadControl M (WriterT ω M) where
  body: fun α => α × ω
liftWith f := liftM f fun x => x.run
  restoreM := WriterT.mk

中文:
实例 [MonadLiftT
  签名: M (WriterT ω M)] : MonadControl M (WriterT ω M) where
  定义体: fun α => α × ω
liftWith f := liftM f fun x => x.run
  restoreM := WriterT.mk
-/
instance [MonadLiftT M (WriterT ω M)] : MonadControl M (WriterT ω M) where
  stM := fun α => α × ω
liftWith f := liftM f fun x => x.run
  restoreM := WriterT.mk

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonadFunctor M (WriterT ω M)
  body: fun k (w : M _) => WriterT.mk k w

中文:
实例 :
  签名: MonadFunctor M (WriterT ω M)
  定义体: fun k (w : M _) => WriterT.mk k w

Depends on / 依赖: WriterT, WriterT.mk
-/
instance : MonadFunctor M (WriterT ω M) where
monadMap := fun k (w : M _) => WriterT.mk k w

/--
Definition of `adapt` / `adapt` 的定义

English:
definition adapt
  signature: {ω' : Type u} {α : Type u} (f : ω -> ω')
  body: fun cmd => WriterT.mk Prod.map id f < > cmd

中文:
定义 adapt
  签名: {ω' : 类型u} {α : 类型u} (f : ω -> ω')
  定义体: fun cmd => WriterT.mk Prod.map id f < > cmd
-/
@[inline] protected def adapt {ω' : Type u} {α : Type u} (f : ω -> ω') :
    WriterT ω M α -> WriterT ω' M α :=
fun cmd => WriterT.mk Prod.map id f < > cmd

end WriterT

/--
Definition of `MonadWriterAdapter` / `MonadWriterAdapter` 的定义

English:
class MonadWriterAdapter
  parameters: (ω : outParam (Type u)) (m : Type u -> Type v)
  axioms and operations (1):
    - adaptWriter({α : Type u}) : (ω -> ω) -> m α -> m α

中文:
类 MonadWriterAdapter
  参数: (ω : outParam (类型u)) (m : 类型u -> 类型v)
  公理与运算 (1 个):
    - adaptWriter({α : 类型u}) : (ω -> ω) -> m α -> m α
-/
class MonadWriterAdapter (ω : outParam (Type u)) (m : Type u -> Type v) where
  adaptWriter {α : Type u} : (ω -> ω) -> m α -> m α

export MonadWriterAdapter (adaptWriter)

variable {m : Type u -> Type*}
/-- Transitivity.

see Note [lower instance priority] -/
instance (priority := 100) monadWriterAdapterTrans {n : Type u -> Type v}
    [MonadWriterAdapter ω m] [MonadFunctor m n] : MonadWriterAdapter ω n where
  adaptWriter f := monadMap (fun {α} => (adaptWriter f : m α -> m α))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monad
  signature: m] : MonadWriterAdapter ω (WriterT ω m) where
  body: WriterT.adapt

universe u₀ u₁ v₀ v₁ in

中文:
实例 [单子
  签名: m] : MonadWriterAdapter ω (WriterT ω m) where
  定义体: WriterT.adapt

universe u₀ u₁ v₀ v₁ in

Depends on / 依赖: WriterT, WriterT.adapt
-/
instance [Monad m] : MonadWriterAdapter ω (WriterT ω m) where
  adaptWriter := WriterT.adapt

universe u₀ u₁ v₀ v₁ in
/--
Definition of `WriterT.equiv` / `WriterT.equiv` 的定义

English:
definition WriterT.equiv
  signature: {m₁ : Type u₀ -> Type v₀} {m₂ : Type u₁ -> Type v₁}
  body: WriterT.mk F f
invFun (f : m₂ _) := WriterT.mk F.symm f
left_inv (f : m₁ _) := congr_arg WriterT.mk F.left_inv f
right_inv (f : m₂ _) := congr_arg WriterT.mk F.right_inv f

中文:
定义 WriterT.equiv
  签名: {m₁ : 类型u₀ -> 类型v₀} {m₂ : 类型u₁ -> 类型v₁}
  定义体: WriterT.mk F f
invFun (f : m₂ _) := WriterT.mk F.symm f
left_inv (f : m₁ _) := congr_arg WriterT.mk F.left_inv f
right_inv (f : m₂ _) := congr_arg WriterT.mk F.right_inv f

Depends on / 依赖: WriterT, WriterT.mk
-/
def WriterT.equiv {m₁ : Type u₀ -> Type v₀} {m₂ : Type u₁ -> Type v₁}
    {α₁ ω₁ : Type u₀} {α₂ ω₂ : Type u₁} (F : (m₁ (α₁ × ω₁)) ≃ (m₂ (α₂ × ω₂))) :
    WriterT ω₁ m₁ α₁ ≃ WriterT ω₂ m₂ α₂ where
toFun (f : m₁ _) := WriterT.mk F f
invFun (f : m₂ _) := WriterT.mk F.symm f
left_inv (f : m₁ _) := congr_arg WriterT.mk F.left_inv f
right_inv (f : m₂ _) := congr_arg WriterT.mk F.right_inv f
