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

/--
Instance `instMonad` / 实例 `instMonad`

English:
instance instMonad
  signature: : Monad List.{u} where
  body: [x]
  bind l f := l.flatMap f
  map f l := l.map f

中文:
实例 instMonad
  签名: : 单子 列表.{u} where
  定义体: [x]
  bind l f := l.flatMap f
  map f l := l.map f
-/
instance instMonad : Monad List.{u} where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

/--
theorem `pure_def` / 定理 `pure_def`

English:
theorem pure_def
  given: (a : α)
  statement: pure a = [a]
  proof: rfl

中文:
定理 pure_def
  条件: (a : α)
  结论: pure a = [a]
  证明: rfl
-/
@[simp] theorem pure_def (a : α) : pure a = [a] := rfl

/--
Instance `instLawfulMonad` / 实例 `instLawfulMonad`

English:
instance instLawfulMonad
  signature: : LawfulMonad List.{u}
  body: LawfulMonad.mk'
  (id_map := map_id)
  (pure_bind := fun _ _ => List.append_nil _)
  (bind_assoc := fun _ _ _ => List.flatMap_assoc)
  (bind_pure_comp := fun _ _ => map_eq_flatMap.symm)

中文:
实例 instLawfulMonad
  签名: : 合法单子 列表.{u}
  定义体: LawfulMonad.mk'
  (id_map := map_id)
  (pure_bind := fun _ _ => List.append_nil _)
  (bind_assoc := fun _ _ _ => List.flatMap_assoc)
  (bind_pure_comp := fun _ _ => map_eq_flatMap.symm)

Depends on / 依赖: LawfulMonad, LawfulMonad.mk
-/
instance instLawfulMonad : LawfulMonad List.{u} := LawfulMonad.mk'
  (id_map := map_id)
  (pure_bind := fun _ _ => List.append_nil _)
  (bind_assoc := fun _ _ _ => List.flatMap_assoc)
  (bind_pure_comp := fun _ _ => map_eq_flatMap.symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AlternativeMonad List.{u}
  body: @List.nil
  orElse l l' := List.append l (l' ())

中文:
实例 :
  签名: AlternativeMonad 列表.{u}
  定义体: @List.nil
  orElse l l' := List.append l (l' ())

Depends on / 依赖: List.nil
-/
instance : AlternativeMonad List.{u} where
  failure := @List.nil
  orElse l l' := List.append l (l' ())

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulAlternative List
  body: List.map_nil
  failure_seq _ := List.flatMap_nil
  orElse_failure _ := List.append_nil _
  failure_orElse _ := List.nil_append _
.symm orElse_assoc _ _ _ := List.append_assoc _ _ _
  map_orElse _ _ _ := List.map_append

中文:
实例 :
  签名: LawfulAlternative 列表
  定义体: List.map_nil
  failure_seq _ := List.flatMap_nil
  orElse_failure _ := List.append_nil _
  failure_orElse _ := List.nil_append _
.symm orElse_assoc _ _ _ := List.append_assoc _ _ _
  map_orElse _ _ _ := List.map_append

Depends on / 依赖: List.map_nil, map_nil
-/
instance : LawfulAlternative List where
  map_failure _ := List.map_nil
  failure_seq _ := List.flatMap_nil
  orElse_failure _ := List.append_nil _
  failure_orElse _ := List.nil_append _
.symm orElse_assoc _ _ _ := List.append_assoc _ _ _
  map_orElse _ _ _ := List.map_append

end List
