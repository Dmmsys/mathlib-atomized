/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Free monoids have unique products
-/

public section

assert_not_exists Cardinal Subsemiring Algebra Submodule StarModule

open Finset

/--
Instance `FreeMonoid.instTwoUniqueProds` / 实例 `FreeMonoid.instTwoUniqueProds`

English:
instance FreeMonoid.instTwoUniqueProds
  signature: {κ : Type*}
  body: .of_mulHom ⟨Multiplicative.ofAdd ∘ List.length, fun _ _ => congr_arg _ List.length_append⟩
    (fun _ _ _ _ h h' => List.append_inj h <| Equiv.injective Multiplicative.ofAdd h'.1)

中文:
实例 FreeMonoid.instTwoUniqueProds
  签名: {κ : 类型}
  定义体: .of_mulHom ⟨Multiplicative.ofAdd ∘ List.length, fun _ _ => congr_arg _ List.length_append⟩
    (fun _ _ _ _ h h' => List.append_inj h <| Equiv.injective Multiplicative.ofAdd h'.1)

Depends on / 依赖: Equiv.injective, List.append_inj, List.length, List.length_append, Multiplicative, Multiplicative.ofAdd, append_inj, congr_arg, injective, length, length_append, of_mulHom
-/
instance FreeMonoid.instTwoUniqueProds {κ : Type*} : TwoUniqueProds (FreeMonoid κ) :=
  .of_mulHom ⟨Multiplicative.ofAdd ∘ List.length, fun _ _ => congr_arg _ List.length_append⟩
    (fun _ _ _ _ h h' => List.append_inj h <| Equiv.injective Multiplicative.ofAdd h'.1)

/--
Instance `FreeAddMonoid.instTwoUniqueSums` / 实例 `FreeAddMonoid.instTwoUniqueSums`

English:
instance FreeAddMonoid.instTwoUniqueSums
  signature: {κ : Type*}
  body: .of_addHom ⟨_, fun _ _ => List.length_append⟩ (fun _ _ _ _ h h' => List.append_inj h h'.1)

中文:
实例 FreeAddMonoid.instTwoUniqueSums
  签名: {κ : 类型}
  定义体: .of_addHom ⟨_, fun _ _ => List.length_append⟩ (fun _ _ _ _ h h' => List.append_inj h h'.1)

Depends on / 依赖: List.append_inj, List.length_append, append_inj, length_append, of_addHom
-/
instance FreeAddMonoid.instTwoUniqueSums {κ : Type*} : TwoUniqueSums (FreeAddMonoid κ) :=
  .of_addHom ⟨_, fun _ _ => List.length_append⟩ (fun _ _ _ _ h h' => List.append_inj h h'.1)
