/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Init
public import Batteries.Control.AlternativeMonad
/-!
# Monad instances for `List`
-/

@[expose] public section

universe u

namespace List

variable {α : Type u}

/-
**List.instMonad** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：instMonad : Monad List.{u} where pure x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonad : Monad List.{u} where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f
/-
**List.pure_def** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (a : α), pure a = [a]
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem pure_def (a : α) : pure a = [a] := rfl
/-
**List.instLawfulMonad** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：instLawfulMonad : LawfulMonad List.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulMonad.mk'`：∀ (m : Type u → Type v) [inst : Monad m],   (∀ {α : Typ
e u} (x : m α), id <$> x = x) →     (∀ {α β : Type u} (x : α) (f : α → m β), pur
e x >…
· 使用定理 `List.map_id`：∀ {α : Type u_1} (l : List α), List.map id l = l
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.flatMap_assoc`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : 
List α} {f : α → List β} {g : β → List γ},   List.flatMap g (List.flatMap f l) =
 List.fl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_eq_flatMap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Li
st α}, List.map f l = List.flatMap (fun x => [f x]) l
-/
instance instLawfulMonad : LawfulMonad List.{u} := LawfulMonad.mk'
  (id_map := map_id)
  (pure_bind := fun _ _ => List.append_nil _)
  (bind_assoc := fun _ _ _ => List.flatMap_assoc)
  (bind_pure_comp := fun _ _ => map_eq_flatMap.symm)
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AlternativeMonad List.{u} where
  failure := @List.nil
  orElse l l' := List.append l (l' ())
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulAlternative List where
  map_failure _ := List.map_nil
  failure_seq _ := List.flatMap_nil
  orElse_failure _ := List.append_nil _
  failure_orElse _ := List.nil_append _
  orElse_assoc _ _ _ := List.append_assoc _ _ _ |>.symm
  map_orElse _ _ _ := List.map_append

end List

