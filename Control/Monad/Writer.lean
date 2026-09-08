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

/-- Adds a writable output of type `ω` to a monad.

The instances on this type assume that either `[Monoid ω]` or `[EmptyCollection ω] [Append ω]`.

Use `WriterT.run` to obtain the final value of this output. -/
/-
**WriterT** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WriterT (ω : Type u) (M : Type u -> Type v) (α : Type u) : Type v
参数：ω : Type u；M : Type u -> Type v；α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adds a writable output of type `ω` to a monad.

The instances on this type assume that either `[Monoid ω]` or `[EmptyCollection 
ω] [Append ω]`.

Use `WriterT.run` to obtain the final value of this output.
-/
def WriterT (ω : Type u) (M : Type u → Type v) (α : Type u) : Type v :=
  M (α × ω)
/-
**Writer** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Writer ω
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Writer ω := WriterT ω Id
/-
**MonadWriter** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：outParam (Type u) → (Type u → Type v) → Type (max (u + 1) v)
参数：Type u；Type u → Type v；max (u + 1) v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class MonadWriter (ω : outParam (Type u)) (M : Type u → Type v) where
  /-- Emit an output `w`. -/
  tell (w : ω) : M PUnit
  /-- Capture the output produced by `f`, without intercepting. -/
  listen {α} (f : M α) : M (α × ω)
  /-- Buffer the output produced by `f` as `w`, then emit `(← f).2 w` in its place. -/
  pass {α} (f : M (α × (ω → ω))) : M α

export MonadWriter (tell listen pass)

variable {M : Type u → Type v} {α β ω ρ σ : Type u}
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MonadWriter ω M] : MonadWriter ω (ReaderT ρ M) where
  tell w := (tell w : M _)
  listen x r := listen <| x r
  pass x r := pass <| x r
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monad M] [MonadWriter ω M] : MonadWriter ω (StateT σ M) where
  tell w := (tell w : M _)
  listen x s := (fun ((a, w), s) ↦ ((a, s), w)) <$> listen (x s)
  pass x s := pass <| (fun ((a, f), s) ↦ ((a, s), f)) <$> (x s)

namespace WriterT

@[inline]
/-
**WriterT.mk** 是 Mathlib 中的一个定义，位于命名空间 `WriterT`。
形式化陈述：{M : Type u → Type v} → {α ω : Type u} → M (α × ω) → WriterT ω M α
参数：α × ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def mk {ω : Type u} (cmd : M (α × ω)) : WriterT ω M α := cmd
@[inline]
/-
**WriterT.run** 是 Mathlib 中的一个定义，位于命名空间 `WriterT`。
形式化陈述：{M : Type u → Type v} → {α ω : Type u} → WriterT ω M α → M (α × ω)
参数：α × ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def run {ω : Type u} (cmd : WriterT ω M α) : M (α × ω) := cmd
/-
**WriterT.runThe** 是 Mathlib 中的一个缩写定义，位于命名空间 `WriterT`。
形式化陈述：runThe (ω : Type u) (cmd : WriterT ω M α) : M (α × ω)
参数：ω : Type u；cmd : WriterT ω M α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev runThe (ω : Type u) (cmd : WriterT ω M α) : M (α × ω) := cmd.run
/-
**WriterT.run_mk** 是 Mathlib 中的一个定理，位于命名空间 `WriterT`。
形式化陈述：∀ {M : Type u → Type v} {α ω : Type u} (cmd : M (α × ω)), (WriterT.mk cmd)
.run = cmd
参数：cmd : M (α × ω)；WriterT.mk cmd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem run_mk {ω : Type u} (cmd : M (α × ω)) : (WriterT.mk cmd).run = cmd := rfl

@[ext]
/-
**WriterT.ext** 是 Mathlib 中的一个定理，位于命名空间 `WriterT`。
形式化陈述：∀ {M : Type u → Type v} {α ω : Type u} (x x' : WriterT ω M α), x.run = x'.
run → x = x'
参数：x x' : WriterT ω M α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**WriterT.monad** 是 Mathlib 中的一个定义，位于命名空间 `WriterT`。
形式化陈述：monad (empty : ω) (append : ω -> ω -> ω) : Monad (WriterT ω M) where map
参数：empty : ω；append : ω -> ω -> ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Creates an instance of `Monad`, with explicitly given `empty` and `append` opera
tions.

Previously, this would have used an instance of `[Monoid ω]` as input.
In practice, however, `WriterT` is used for logging and creating lists so restri
cting to
monoids with `Mul` and `One` can make `WriterT` cumbersome to use.

This is used to derive instances for both `[EmptyCollection ω] [Append ω]` and `
[Monoid ω]`.
-/
def monad (empty : ω) (append : ω → ω → ω) : Monad (WriterT ω M) where
  map := fun f cmd ↦ WriterT.mk <| (fun (a, w) ↦ (f a, w)) <$> cmd.run
  pure := fun a ↦ pure (f := M) (a, empty)
  bind := fun cmd f ↦
    WriterT.mk <| cmd.run >>= fun (a, w₁) ↦
      (fun (b, w₂) ↦ (b, append w₁ w₂)) <$> (f a).run

@[simp]
/-
**WriterT.run_pure** 是 Mathlib 中的一个定理，位于命名空间 `WriterT`。
形式化陈述：run_pure (empty : ω) (append : ω -> ω -> ω) (a : α) : letI : Monad (Writer
T ω M)
参数：empty : ω；append : ω -> ω -> ω；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_pure (empty : ω) (append : ω → ω → ω) (a : α) :
    letI : Monad (WriterT ω M) := monad empty append
    (pure a : WriterT ω M α).run = pure (a, empty) :=
  rfl

@[simp]
/-
**WriterT.run_map** 是 Mathlib 中的一个定理，位于命名空间 `WriterT`。
形式化陈述：run_map (empty : ω) (append : ω -> ω -> ω) (f : α -> β) (cmd : WriterT ω M
 α) : letI : Monad (WriterT ω M)
参数：empty : ω；append : ω -> ω -> ω；f : α -> β；cmd : WriterT ω M α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_map (empty : ω) (append : ω → ω → ω) (f : α → β) (cmd : WriterT ω M α) :
    letI : Monad (WriterT ω M) := monad empty append
    (f <$> cmd).run = (fun (a, w) ↦ (f a, w)) <$> cmd.run :=
  rfl

@[simp]
/-
**WriterT.run_bind** 是 Mathlib 中的一个定理，位于命名空间 `WriterT`。
形式化陈述：run_bind (empty : ω) (append : ω -> ω -> ω) (cmd : WriterT ω M α) (f : α -
> WriterT ω M β) : letI : Monad (WriterT ω M)
参数：empty : ω；append : ω -> ω -> ω；cmd : WriterT ω M α；f : α -> WriterT ω M β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_bind (empty : ω) (append : ω → ω → ω)
    (cmd : WriterT ω M α) (f : α → WriterT ω M β) :
    letI : Monad (WriterT ω M) := monad empty append
    (cmd >>= f).run = cmd.run >>= fun (a, w₁) ↦
      (fun (b, w₂) ↦ (b, append w₁ w₂)) <$> (f a).run :=
  rfl

/-- Lift an `M` to a `WriterT ω M`, using the given `empty` as the monoid unit. -/
@[inline, instance_reducible]
/-
**WriterT.liftTell** 是 Mathlib 中的一个定义，位于命名空间 `WriterT`。
形式化陈述：{M : Type u → Type v} → {ω : Type u} → [Monad M] → ω → MonadLift M (Writer
T ω M)
参数：WriterT ω M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift an `M` to a `WriterT ω M`, using the given `empty` as the monoid unit.
-/
protected def liftTell (empty : ω) : MonadLift M (WriterT ω M) where
  monadLift := fun cmd ↦ WriterT.mk <| (fun a ↦ (a, empty)) <$> cmd

@[simp]
/-
**WriterT.run_liftM** 是 Mathlib 中的一个定理，位于命名空间 `WriterT`。
形式化陈述：run_liftM (empty : ω) (cmd : M α) : letI : MonadLift M (WriterT ω M)
参数：empty : ω；cmd : M α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_liftM (empty : ω) (cmd : M α) :
    letI : MonadLift M (WriterT ω M) := WriterT.liftTell empty
    (cmd : WriterT ω M α).run = (fun a ↦ (a, empty)) <$> cmd :=
  rfl
/-
**WriterT.** 是 Mathlib 中的一个实例，位于命名空间 `WriterT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EmptyCollection ω] [Append ω] : Monad (WriterT ω M) := monad ∅ (· ++ ·)
/-
**WriterT.** 是 Mathlib 中的一个实例，位于命名空间 `WriterT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EmptyCollection ω] : MonadLift M (WriterT ω M) := WriterT.liftTell ∅
/-
**WriterT.** 是 Mathlib 中的一个实例，位于命名空间 `WriterT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid ω] : Monad (WriterT ω M) := monad 1 (· * ·)
/-
**WriterT.** 是 Mathlib 中的一个实例，位于命名空间 `WriterT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid ω] : MonadLift M (WriterT ω M) := WriterT.liftTell 1
/-
**WriterT.** 是 Mathlib 中的一个实例，位于命名空间 `WriterT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid ω] [LawfulMonad M] : LawfulMonad (WriterT ω M) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => by ext; simp)
  (id_map := fun _ => by ext; simp)
  (pure_bind := fun _ _ => by ext; simp)
  (bind_assoc := fun _ _ _ => by ext; simp [mul_assoc])
/-
**WriterT.** 是 Mathlib 中的一个实例，位于命名空间 `WriterT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonadWriter ω (WriterT ω M) where
  tell := fun w ↦ WriterT.mk <| pure (⟨⟩, w)
  listen := fun cmd ↦ WriterT.mk <| (fun (a, w) ↦ ((a, w), w)) <$> cmd.run
  pass := fun cmd ↦ WriterT.mk <| (fun ((a, f), w) ↦ (a, f w)) <$> cmd.run

@[simp]
/-
**WriterT.run_tell** 是 Mathlib 中的一个定理，位于命名空间 `WriterT`。
形式化陈述：run_tell (w : ω) : WriterT.run (MonadWriter.tell w : WriterT ω M PUnit) = 
pure (⟨⟩, w)
参数：w : ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_tell (w : ω) :
    WriterT.run (MonadWriter.tell w : WriterT ω M PUnit) = pure (⟨⟩, w) := rfl

@[simp]
/-
**WriterT.run_listen** 是 Mathlib 中的一个定理，位于命名空间 `WriterT`。
形式化陈述：run_listen (cmd : WriterT ω M α) : WriterT.run (MonadWriter.listen cmd) = 
(fun (a, w) => ((a, w), w)) < > cmd.run
参数：cmd : WriterT ω M α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_listen (cmd : WriterT ω M α) :
    WriterT.run (MonadWriter.listen cmd) = (fun (a, w) ↦ ((a, w), w)) <$> cmd.run :=
  rfl

@[simp]
/-
**WriterT.run_pass** 是 Mathlib 中的一个定理，位于命名空间 `WriterT`。
形式化陈述：run_pass (cmd : WriterT ω M (α × (ω -> ω))) : WriterT.run (MonadWriter.pas
s cmd) = (fun ((a, f), w) => (a, f w)) < > cmd.run
参数：cmd : WriterT ω M (α × (ω -> ω))。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_pass (cmd : WriterT ω M (α × (ω → ω))) :
    WriterT.run (MonadWriter.pass cmd) = (fun ((a, f), w) ↦ (a, f w)) <$> cmd.run :=
  rfl
/-
**WriterT.** 是 Mathlib 中的一个实例，位于命名空间 `WriterT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ε : Type*} [MonadExceptOf ε M] : MonadExceptOf ε (WriterT ω M) where
  throw := fun e ↦ WriterT.mk <| throw e
  tryCatch := fun cmd c ↦ WriterT.mk <| tryCatch cmd.run fun e ↦ (c e).run

@[simp]
/-
**WriterT.run_throw** 是 Mathlib 中的一个定理，位于命名空间 `WriterT`。
形式化陈述：run_throw {M} {ε : Type*} [MonadExceptOf ε M] (e : ε) : (throw e : WriterT
 ω M α).run = throw e
参数：e : ε。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_throw {M} {ε : Type*} [MonadExceptOf ε M] (e : ε) :
    (throw e : WriterT ω M α).run = throw e :=
  rfl

@[simp]
/-
**WriterT.run_tryCatch** 是 Mathlib 中的一个定理，位于命名空间 `WriterT`。
形式化陈述：run_tryCatch {M} {ε : Type*} [MonadExceptOf ε M] (cmd : WriterT ω M α) (c 
: ε -> WriterT ω M α) : (tryCatch cmd c : WriterT ω M α).run = tryCatch cmd.run 
fun e => (c e).run
参数：cmd : WriterT ω M α；c : ε -> WriterT ω M α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_tryCatch {M} {ε : Type*} [MonadExceptOf ε M]
    (cmd : WriterT ω M α) (c : ε → WriterT ω M α) :
    (tryCatch cmd c : WriterT ω M α).run = tryCatch cmd.run fun e ↦ (c e).run :=
  rfl
/-
**WriterT.** 是 Mathlib 中的一个实例，位于命名空间 `WriterT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MonadLiftT M (WriterT ω M)] : MonadControl M (WriterT ω M) where
  stM := fun α ↦ α × ω
  liftWith f := liftM <| f fun x ↦ x.run
  restoreM := WriterT.mk
/-
**WriterT.** 是 Mathlib 中的一个实例，位于命名空间 `WriterT`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonadFunctor M (WriterT ω M) where
  monadMap := fun k (w : M _) ↦ WriterT.mk <| k w
/-
**WriterT.adapt** 是 Mathlib 中的一个定义，位于命名空间 `WriterT`。
形式化陈述：{M : Type u → Type v} → {ω : Type u} → [Monad M] → {ω' α : Type u} → (ω → 
ω') → WriterT ω M α → WriterT ω' M α
参数：ω → ω'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[inline] protected def adapt {ω' : Type u} {α : Type u} (f : ω → ω') :
    WriterT ω M α → WriterT ω' M α :=
  fun cmd ↦ WriterT.mk <| Prod.map id f <$> cmd

end WriterT

/-- Adapt a monad stack, changing the type of its top-most environment.

This class is comparable to [Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify),
but does not use lenses (why would it), and is derived automatically for any transformer
implementing `MonadFunctor`.
-/
/-
**MonadWriterAdapter** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：outParam (Type u) → (Type u → Type v) → Type (max (u + 1) v)
参数：Type u；Type u → Type v；max (u + 1) v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adapt a monad stack, changing the type of its top-most environment.

This class is comparable to [Control.Lens.Magnify](https://hackage.haskell.org/p
ackage/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify),
but does not use lenses (why would it), and is derived automatically for any tra
nsformer
implementing `MonadFunctor`.
-/
class MonadWriterAdapter (ω : outParam (Type u)) (m : Type u → Type v) where
  adaptWriter {α : Type u} : (ω → ω) → m α → m α

export MonadWriterAdapter (adaptWriter)

variable {m : Type u → Type*}
/-- Transitivity.

see Note [lower instance priority] -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transitivity.

see Note [lower instance priority]
-/
instance (priority := 100) monadWriterAdapterTrans {n : Type u → Type v}
    [MonadWriterAdapter ω m] [MonadFunctor m n] : MonadWriterAdapter ω n where
  adaptWriter f := monadMap (fun {α} ↦ (adaptWriter f : m α → m α))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monad m] : MonadWriterAdapter ω (WriterT ω m) where
  adaptWriter := WriterT.adapt

universe u₀ u₁ v₀ v₁ in
/-- reduce the equivalence between two writer monads to the equivalence between
their underlying monad -/
/-
**WriterT.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WriterT.equiv {m₁ : Type u₀ -> Type v₀} {m₂ : Type u₁ -> Type v₁} {α₁ ω₁ :
 Type u₀} {α₂ ω₂ : Type u₁} (F : (m₁ (α₁ × ω₁)) ≃ (m₂ (α₂ × ω₂))) : WriterT ω₁ m
₁ α₁ ≃ WriterT ω₂ m₂ α₂ where toFun (f : m₁ _)
参数：F : (m₁ (α₁ × ω₁)) ≃ (m₂ (α₂ × ω₂))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
reduce the equivalence between two writer monads to the equivalence between
their underlying monad
-/
def WriterT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
    {α₁ ω₁ : Type u₀} {α₂ ω₂ : Type u₁} (F : (m₁ (α₁ × ω₁)) ≃ (m₂ (α₂ × ω₂))) :
    WriterT ω₁ m₁ α₁ ≃ WriterT ω₂ m₂ α₂ where
  toFun (f : m₁ _) := WriterT.mk <| F f
  invFun (f : m₂ _) := WriterT.mk <| F.symm f
  left_inv (f : m₁ _) := congr_arg WriterT.mk <| F.left_inv f
  right_inv (f : m₂ _) := congr_arg WriterT.mk <| F.right_inv f
