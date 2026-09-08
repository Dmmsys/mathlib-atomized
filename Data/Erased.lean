/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.Defs

/-!
# A type for VM-erased data

This file defines a type `Erased α` which is classically isomorphic to `α`,
but erased in the VM. That is, at runtime every value of `Erased α` is
represented as `0`, just like types and proofs.
-/

@[expose] public section


universe u

/-- `Erased α` is the same as `α`, except that the elements
  of `Erased α` are erased in the VM in the same way as types
  and proofs. This can be used to track data without storing it
  literally. -/
/-
**Erased** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Erased (α : Sort u) : Sort max 1 u
参数：α : Sort u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Erased α` is the same as `α`, except that the elements
  of `Erased α` are erased in the VM in the same way as types
  and proofs. This can be used to track data without storing it
  literally.
-/
def Erased (α : Sort u) : Sort max 1 u :=
  { s : α → Prop // ∃ a, (a = ·) = s }

namespace Erased

/-- Erase a value. -/
@[macro_inline]
/-
**Erased.mk** 是 Mathlib 中的一个定义，位于命名空间 `Erased`。
形式化陈述：mk {α} (a : α) : Erased α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Erase a value.
-/
def mk {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩

/-- Extracts the erased value, noncomputably. -/
/-
**Erased.out** 是 Mathlib 中的一个定义，位于命名空间 `Erased`。
形式化陈述：{α : Sort u_1} → Erased α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extracts the erased value, noncomputably.
-/
noncomputable def out {α} : Erased α → α
  | ⟨_, h⟩ => Classical.choose h

/-- Extracts the erased value, if it is a type.

Note: `(mk a).OutType` is not definitionally equal to `a`.
-/
/-
**Erased.OutType** 是 Mathlib 中的一个缩写定义，位于命名空间 `Erased`。
形式化陈述：OutType (a : Erased (Sort u)) : Sort u
参数：a : Erased (Sort u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extracts the erased value, if it is a type.

Note: `(mk a).OutType` is not definitionally equal to `a`.
-/
abbrev OutType (a : Erased (Sort u)) : Sort u :=
  out a

/-- Extracts the erased value, if it is a proof. -/
/-
**Erased.out_proof** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：out_proof {p : Prop} (a : Erased p) : p
参数：a : Erased p。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extracts the erased value, if it is a proof.
-/
theorem out_proof {p : Prop} (a : Erased p) : p :=
  out a

@[simp]
/-
**Erased.out_mk** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：out_mk {α} (a : α) : (mk a).out = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem out_mk {α} (a : α) : (mk a).out = a := by
  let h := (mk a).2; change Classical.choose h = a
  have := Classical.choose_spec h
  exact cast (congr_fun this a).symm rfl

@[simp]
/-
**Erased.mk_out** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：∀ {α : Sort u_1} (a : Erased α), Erased.mk a.out = a
参数：a : Erased α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem mk_out {α} : ∀ a : Erased α, mk (out a) = a
  | ⟨s, h⟩ => by simp only [mk]; congr; exact Classical.choose_spec h

@[ext]
/-
**Erased.out_inj** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：out_inj {α} (a b : Erased α) (h : a.out = b.out) : a = b
参数：a b : Erased α；h : a.out = b.out。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Erased.mk_out`：∀ {α : Sort u_1} (a : Erased α), Erased.mk a.out = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem out_inj {α} (a b : Erased α) (h : a.out = b.out) : a = b := by simpa using congr_arg mk h

/-- Equivalence between `Erased α` and `α`. -/
/-
**Erased.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Erased`。
形式化陈述：equiv (α) : Erased α ≃ α
参数：α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Erased.mk_out`：∀ {α : Sort u_1} (a : Erased α), Erased.mk a.out = a
· 使用定理 `Erased.out_mk`：out_mk {α} (a : α) : (mk a).out = a

--- 原说明 ---
Equivalence between `Erased α` and `α`.
-/
noncomputable def equiv (α) : Erased α ≃ α :=
  ⟨out, mk, mk_out, out_mk⟩
/-
**Erased.** 是 Mathlib 中的一个实例，位于命名空间 `Erased`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type u) : Repr (Erased α) :=
  ⟨fun _ _ => "Erased"⟩
/-
**Erased.** 是 Mathlib 中的一个实例，位于命名空间 `Erased`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type u) : ToString (Erased α) :=
  ⟨fun _ => "Erased"⟩

/-- Computably produce an erased value from a proof of nonemptiness. -/
/-
**Erased.choice** 是 Mathlib 中的一个定义，位于命名空间 `Erased`。
形式化陈述：choice {α} (h : Nonempty α) : Erased α
参数：h : Nonempty α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computably produce an erased value from a proof of nonemptiness.
-/
def choice {α} (h : Nonempty α) : Erased α :=
  mk (Classical.choice h)

@[simp]
/-
**Erased.nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：nonempty_iff {α} : Nonempty (Erased α) ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_iff {α} : Nonempty (Erased α) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ => ⟨a.out⟩, fun ⟨a⟩ => ⟨mk a⟩⟩
/-
**Erased.** 是 Mathlib 中的一个实例，位于命名空间 `Erased`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [h : Nonempty α] : Inhabited (Erased α) :=
  ⟨choice h⟩

/-- `(>>=)` operation on `Erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `Monad`).
-/
/-
**Erased.bind** 是 Mathlib 中的一个定义，位于命名空间 `Erased`。
形式化陈述：bind {α β} (a : Erased α) (f : α -> Erased β) : Erased β
参数：a : Erased α；f : α -> Erased β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(>>=)` operation on `Erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `Monad`).
-/
def bind {α β} (a : Erased α) (f : α → Erased β) : Erased β :=
  ⟨fun b => (f a.out).1 b, (f a.out).2⟩

@[simp]
/-
**Erased.bind_eq_out** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：bind_eq_out {α β} (a f) : @bind α β a f = f a.out
参数：a f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_eq_out {α β} (a f) : @bind α β a f = f a.out := rfl

/-- Collapses two levels of erasure.
-/
/-
**Erased.join** 是 Mathlib 中的一个定义，位于命名空间 `Erased`。
形式化陈述：join {α} (a : Erased (Erased α)) : Erased α
参数：a : Erased (Erased α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Collapses two levels of erasure.
-/
def join {α} (a : Erased (Erased α)) : Erased α :=
  bind a id

@[simp]
/-
**Erased.join_eq_out** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：join_eq_out {α} (a) : @join α a = a.out
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem join_eq_out {α} (a) : @join α a = a.out :=
  rfl

/-- `(<$>)` operation on `Erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `Functor`).
-/
/-
**Erased.map** 是 Mathlib 中的一个定义，位于命名空间 `Erased`。
形式化陈述：map {α β} (f : α -> β) (a : Erased α) : Erased β
参数：f : α -> β；a : Erased α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(<$>)` operation on `Erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `Functor`).
-/
def map {α β} (f : α → β) (a : Erased α) : Erased β :=
  bind a (mk ∘ f)

@[simp]
/-
**Erased.map_out** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：map_out {α β} {f : α -> β} (a : Erased α) : (a.map f).out = f a.out
参数：a : Erased α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Erased.out_mk`：out_mk {α} (a : α) : (mk a).out = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_out {α β} {f : α → β} (a : Erased α) : (a.map f).out = f a.out := by simp [map]
/-
**Erased.Monad** 是 Mathlib 中的一个定义，位于命名空间 `Erased`。
形式化陈述：Monad Erased
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance Monad : Monad Erased where
  pure := @mk
  bind := @bind
  map := @map

@[simp]
/-
**Erased.pure_def** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：pure_def {α} : (pure : α -> Erased α) = @mk _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_def {α} : (pure : α → Erased α) = @mk _ :=
  rfl

@[simp]
/-
**Erased.bind_def** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：bind_def {α β} : ((· >>= ·) : Erased α -> (α -> Erased β) -> Erased β) = @
bind _ _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_def {α β} : ((· >>= ·) : Erased α → (α → Erased β) → Erased β) = @bind _ _ :=
  rfl

@[simp]
/-
**Erased.map_def** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：map_def {α β} : ((· <$> ·) : (α -> β) -> Erased α -> Erased β) = @map _ _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_def {α β} : ((· <$> ·) : (α → β) → Erased α → Erased β) = @map _ _ :=
  rfl
/-
**Erased.instLawfulMonad** 是 Mathlib 中的一个定理，位于命名空间 `Erased`。
形式化陈述：LawfulMonad Erased
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Erased.out_inj`：out_inj {α} (a b : Erased α) (h : a.out = b.out) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Erased.map_out`：map_out {α β} {f : α -> β} (a : Erased α) : (a.map f).ou
t = f a.out
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Erased.out_mk`：out_mk {α} (a : α) : (mk a).out = a
· 使用定理 `Erased.mk_out`：∀ {α : Sort u_1} (a : Erased α), Erased.mk a.out = a
-/
protected instance instLawfulMonad : LawfulMonad Erased :=
  { id_map := by intros; ext; simp
    map_const := by intros; ext; simp [Functor.mapConst]
    pure_bind := by intros; ext; simp
    bind_assoc := by intros; ext; simp
    bind_pure_comp := by intros; ext; simp
    bind_map := by intros; ext; simp [Seq.seq]
    seqLeft_eq := by intros; ext; simp [Seq.seq, SeqLeft.seqLeft]
    seqRight_eq := by intros; ext; simp [Seq.seq, SeqRight.seqRight]
    pure_seq := by intros; ext; simp [Seq.seq] }

end Erased

