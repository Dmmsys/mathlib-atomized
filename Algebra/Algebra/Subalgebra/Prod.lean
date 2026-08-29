/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Products of subalgebras

In this file we define the product of two subalgebras as a subalgebra of the product algebra.

## Main definitions

* `Subalgebra.prod`: the product of two subalgebras.
-/

@[expose] public section


namespace Subalgebra

open Algebra

variable {R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
         [Semiring C] [Algebra R C] [Semiring D] [Algebra R D]

variable (S : Subalgebra R A) (S₁ : Subalgebra R B)

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : Subalgebra R (A × B)
  body: { S.toSubsemiring.prod S₁.toSubsemiring with
    carrier := S ×ˢ S₁
    algebraMap_mem' := fun _ => ⟨algebraMap_mem _ _, algebraMap_mem _ _⟩ }

@[simp, norm_cast]

中文:
定义 prod
  签名: : Subalgebra R (A × B)
  定义体: { S.toSubsemiring.prod S₁.toSubsemiring with
    carrier := S ×ˢ S₁
    algebraMap_mem' := fun _ => ⟨algebraMap_mem _ _, algebraMap_mem _ _⟩ }

@[simp, norm_cast]

Depends on / 依赖: S.toSubsemiring.prod, algebraMap_mem, carrier, toSubsemiring
-/
def prod : Subalgebra R (A × B) :=
  { S.toSubsemiring.prod S₁.toSubsemiring with
    carrier := S ×ˢ S₁
    algebraMap_mem' := fun _ => ⟨algebraMap_mem _ _, algebraMap_mem _ _⟩ }

@[simp, norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  statement: (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ (S₁ : Set B)
  proof: rfl

中文:
定理 coe_prod
  结论: (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ (S₁ : Set B)
  证明: rfl
-/
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ (S₁ : Set B) :=
  rfl

open Subalgebra in
/--
theorem `prod_toSubmodule` / 定理 `prod_toSubmodule`

English:
theorem prod_toSubmodule
  statement: toSubmodule (S.prod S₁) = (toSubmodule S).prod (toSubmodule S₁)
  proof: rfl

@[simp]

中文:
定理 prod_toSubmodule
  结论: toSubmodule (S.prod S₁) = (toSubmodule S).prod (toSubmodule S₁)
  证明: rfl

@[simp]
-/
theorem prod_toSubmodule : toSubmodule (S.prod S₁) = (toSubmodule S).prod (toSubmodule S₁) := rfl

@[simp]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {S : Subalgebra R A} {S₁ : Subalgebra R B} {x : A × B}
  proof: Set.mem_prod

@[simp]

中文:
定理 mem_prod
  条件: {S : Subalgebra R A} {S₁ : Subalgebra R B} {x : A × B}
  证明: Set.mem_prod

@[simp]

Depends on / 依赖: Set.mem_prod, mem_prod
-/
theorem mem_prod {S : Subalgebra R A} {S₁ : Subalgebra R B} {x : A × B} :
    x in prod S S₁ ↔ x.1 in S ∧ x.2 in S₁ := Set.mem_prod

@[simp]
/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  statement: (prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤
  proof: by ext; simp

中文:
定理 prod_top
  结论: (prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤
  证明: by ext; simp
-/
theorem prod_top : (prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤ := by ext; simp

/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B}
  proof: Set.prod_mono

@[simp]

中文:
定理 prod_mono
  条件: {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B}
  证明: Set.prod_mono

@[simp]

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} :
    S <= T -> S₁ <= T₁ -> prod S S₁ <= prod T T₁ :=
  Set.prod_mono

@[simp]
/--
theorem `prod_inf_prod` / 定理 `prod_inf_prod`

English:
theorem prod_inf_prod
  given: {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B}
  proof: SetLike.coe_injective Set.prod_inter_prod

中文:
定理 prod_inf_prod
  条件: {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B}
  证明: SetLike.coe_injective Set.prod_inter_prod

Depends on / 依赖: Set.prod_inter_prod, SetLike, SetLike.coe_injective, coe_injective, prod_inter_prod
-/
theorem prod_inf_prod {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod

/--
theorem `center_prod` / 定理 `center_prod`

English:
theorem center_prod
  statement: center R (A × B) = prod (center R A) (center R B)
  proof: SetLike.coe_injective Set.center_prod

@[simp]

中文:
定理 center_prod
  结论: center R (A × B) = prod (center R A) (center R B)
  证明: SetLike.coe_injective Set.center_prod

@[simp]
-/
protected theorem center_prod : center R (A × B) = prod (center R A) (center R B) :=
  SetLike.coe_injective Set.center_prod

@[simp]
/--
theorem `_root_.AlgHom.range_prodMap` / 定理 `_root_.AlgHom.range_prodMap`

English:
theorem _root_.AlgHom.range_prodMap
  given: (f : A ->ₐ[R] B) (g : C ->ₐ[R] D)
  proof: SetLike.coe_injective Set.range_prodMap

中文:
定理 _root_.AlgHom.range_prodMap
  条件: (f : A ->ₐ[R] B) (g : C ->ₐ[R] D)
  证明: SetLike.coe_injective Set.range_prodMap

Depends on / 依赖: Set.range_prodMap, SetLike, SetLike.coe_injective, coe_injective, range_prodMap
-/
theorem _root_.AlgHom.range_prodMap (f : A ->ₐ[R] B) (g : C ->ₐ[R] D) :
    (f.prodMap g).range = f.range.prod g.range :=
  SetLike.coe_injective Set.range_prodMap

end Subalgebra
