/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jannis Limperg
-/
module

public import Mathlib.Init
/-!
# Monadic instances for `ULift` and `PLift`

In this file we define `Monad` and `IsLawfulMonad` instances on `PLift` and `ULift`. -/

@[expose] public section

universe u v u' v'

namespace PLift

variable {α : Sort u} {β : Sort v}

/-- Functorial action. -/
/-
**PLift.map** 是 Mathlib 中的一个定义，位于命名空间 `PLift`。
形式化陈述：{α : Sort u} → {β : Sort v} → (α → β) → PLift α → PLift β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functorial action.
-/
protected def map (f : α → β) (a : PLift α) : PLift β :=
  PLift.up (f a.down)

@[simp]
/-
**PLift.map_up** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：map_up (f : α -> β) (a : α) : (PLift.up a).map f = PLift.up (f a)
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_up (f : α → β) (a : α) : (PLift.up a).map f = PLift.up (f a) :=
  rfl

/-- Embedding of pure values. -/
@[simp]
/-
**PLift.pure** 是 Mathlib 中的一个定义，位于命名空间 `PLift`。
形式化陈述：{α : Sort u} → α → PLift α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of pure values.
-/
protected def pure : α → PLift α :=
  up

/-- Applicative sequencing. -/
/-
**PLift.seq** 是 Mathlib 中的一个定义，位于命名空间 `PLift`。
形式化陈述：{α : Sort u} → {β : Sort v} → PLift (α → β) → (Unit → PLift α) → PLift β
参数：α → β；Unit → PLift α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applicative sequencing.
-/
protected def seq (f : PLift (α → β)) (x : Unit → PLift α) : PLift β :=
  PLift.up (f.down (x ()).down)

@[simp]
/-
**PLift.seq_up** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：seq_up (f : α -> β) (x : α) : (PLift.up f).seq (fun _ => PLift.up x) = PLi
ft.up (f x)
参数：f : α -> β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seq_up (f : α → β) (x : α) : (PLift.up f).seq (fun _ => PLift.up x) = PLift.up (f x) :=
  rfl

/-- Monadic bind. -/
/-
**PLift.bind** 是 Mathlib 中的一个定义，位于命名空间 `PLift`。
形式化陈述：{α : Sort u} → {β : Sort v} → PLift α → (α → PLift β) → PLift β
参数：α → PLift β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monadic bind.
-/
protected def bind (a : PLift α) (f : α → PLift β) : PLift β :=
  f a.down

@[simp]
/-
**PLift.bind_up** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：bind_up (a : α) (f : α -> PLift β) : (PLift.up a).bind f = f a
参数：a : α；f : α -> PLift β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_up (a : α) (f : α → PLift β) : (PLift.up a).bind f = f a :=
  rfl
/-
**PLift.** 是 Mathlib 中的一个实例，位于命名空间 `PLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monad PLift where
  map := @PLift.map
  pure := @PLift.pure
  seq := @PLift.seq
  bind := @PLift.bind
/-
**PLift.** 是 Mathlib 中的一个实例，位于命名空间 `PLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulFunctor PLift where
  id_map := @fun _ ⟨_⟩ => rfl
  comp_map := @fun _ _ _ _ _ ⟨_⟩ => rfl
  map_const := @fun _ _ => rfl
/-
**PLift.** 是 Mathlib 中的一个实例，位于命名空间 `PLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulApplicative PLift where
  seqLeft_eq := @fun _ _ _ _ => rfl
  seqRight_eq := @fun _ _ _ _ => rfl
  pure_seq := @fun _ _ _ ⟨_⟩ => rfl
  map_pure := @fun _ _ _ _ => rfl
  seq_pure := @fun _ _ ⟨_⟩ _ => rfl
  seq_assoc := @fun _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩ => rfl
/-
**PLift.** 是 Mathlib 中的一个实例，位于命名空间 `PLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad PLift where
  bind_pure_comp := @fun _ _ _ ⟨_⟩ => rfl
  bind_map := @fun _ _ ⟨_⟩ ⟨_⟩ => rfl
  pure_bind := @fun _ _ _ _ => rfl
  bind_assoc := @fun _ _ _ ⟨_⟩ _ _ => rfl

@[simp]
/-
**PLift.rec.constant** 是 Mathlib 中的一个定理，位于命名空间 `PLift.rec`。
形式化陈述：∀ {α : Sort u} {β : Type v} (b : β), (PLift.rec fun x => b) = fun x => b
参数：b : β；PLift.rec fun x => b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rec.constant {α : Sort u} {β : Type v} (b : β) :
    (@PLift.rec α (fun _ => β) fun _ => b) = fun _ => b := rfl

end PLift

namespace ULift

variable {α : Type u} {β : Type v}

/-- Functorial action. -/
/-
**ULift.map** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{α : Type u} → {β : Type v} → (α → β) → ULift.{u', u} α → ULift.{v', v} β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functorial action.
-/
protected def map (f : α → β) (a : ULift.{u'} α) : ULift.{v'} β := ULift.up.{v'} (f a.down)

@[simp]
/-
**ULift.map_up** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：map_up (f : α -> β) (a : α) : (ULift.up.{u'} a).map f = ULift.up.{v'} (f a
)
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_up (f : α → β) (a : α) : (ULift.up.{u'} a).map f = ULift.up.{v'} (f a) := rfl

/-- Embedding of pure values. -/
@[simp]
/-
**ULift.pure** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{α : Type u} → α → ULift.{u_1, u} α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of pure values.
-/
protected def pure : α → ULift α :=
  up

/-- Applicative sequencing. -/
/-
**ULift.seq** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → ULift.{u_3, max u_1 u_2} (α → β) → (Unit
 → ULift.{u_4, u_1} α) → ULift.{u, u_2} β
参数：α → β；Unit → ULift.{u_4, u_1} α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applicative sequencing.
-/
protected def seq {α β} (f : ULift (α → β)) (x : Unit → ULift α) : ULift β :=
  ULift.up.{u} (f.down (x ()).down)

@[simp]
/-
**ULift.seq_up** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：seq_up (f : α -> β) (x : α) : (ULift.up f).seq (fun _ => ULift.up x) = ULi
ft.up (f x)
参数：f : α -> β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seq_up (f : α → β) (x : α) : (ULift.up f).seq (fun _ => ULift.up x) = ULift.up (f x) :=
  rfl

/-- Monadic bind. -/
/-
**ULift.bind** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{α : Type u} → {β : Type v} → ULift.{u_1, u} α → (α → ULift.{u_2, v} β) → 
ULift.{u_2, v} β
参数：α → ULift.{u_2, v} β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monadic bind.
-/
protected def bind (a : ULift α) (f : α → ULift β) : ULift β :=
  f a.down

@[simp]
/-
**ULift.bind_up** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：bind_up (a : α) (f : α -> ULift β) : (ULift.up a).bind f = f a
参数：a : α；f : α -> ULift β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_up (a : α) (f : α → ULift β) : (ULift.up a).bind f = f a :=
  rfl
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monad ULift where
  map := @ULift.map
  pure := @ULift.pure
  seq := @ULift.seq
  bind := @ULift.bind
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulFunctor ULift where
  id_map := @fun _ ⟨_⟩ => rfl
  comp_map := @fun _ _ _ _ _ ⟨_⟩ => rfl
  map_const := @fun _ _ => rfl
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulApplicative ULift where
  seqLeft_eq := @fun _ _ _ _ => rfl
  seqRight_eq := @fun _ _ _ _ => rfl
  pure_seq := @fun _ _ _ ⟨_⟩ => rfl
  map_pure := @fun _ _ _ _ => rfl
  seq_pure := @fun _ _ ⟨_⟩ _ => rfl
  seq_assoc := @fun _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩ => rfl
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad ULift where
  bind_pure_comp := @fun _ _ _ ⟨_⟩ => rfl
  bind_map := @fun _ _ ⟨_⟩ ⟨_⟩ => rfl
  pure_bind := @fun _ _ _ _ => rfl
  bind_assoc := @fun _ _ _ ⟨_⟩ _ _ => rfl

@[simp]
/-
**ULift.rec.constant** 是 Mathlib 中的一个定理，位于命名空间 `ULift.rec`。
形式化陈述：∀ {α : Type u} {β : Sort v} (b : β), (ULift.rec fun x => b) = fun x => b
参数：b : β；ULift.rec fun x => b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rec.constant {α : Type u} {β : Sort v} (b : β) :
    (@ULift.rec α (fun _ => β) fun _ => b) = fun _ => b := rfl

end ULift

