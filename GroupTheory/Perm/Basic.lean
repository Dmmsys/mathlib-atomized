/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Tactic.Common

/-!
# Extra lemmas about permutations

This file proves miscellaneous lemmas about `Equiv.Perm`.

## TODO

Most of the content of this file was moved to `Mathlib/Algebra/Group/End.lean` in
https://github.com/leanprover-community/mathlib4/pull/22141.
It would be good to merge the remaining lemmas with other files, e.g.
`GroupTheory.Perm.ViaEmbedding` looks like it could benefit from such a treatment (splitting into
the algebra and non-algebra parts).
-/

public section


universe u v

namespace Equiv

variable {α : Type u} {β : Type v}

section Swap

variable [DecidableEq α]

@[simp]
/--
theorem `swap_smul_self_smul` / 定理 `swap_smul_self_smul`

English:
theorem swap_smul_self_smul
  given: [MulAction (Perm α) β] (i j : α) (x : β)
  proof: by simp [smul_smul]

中文:
定理 swap_smul_self_smul
  条件: [乘法作用 (置换 α) β] (i j : α) (x : β)
  证明: by simp [smul_smul]

Depends on / 依赖: smul_smul
-/
theorem swap_smul_self_smul [MulAction (Perm α) β] (i j : α) (x : β) :
    swap i j • swap i j • x = x := by simp [smul_smul]

/--
theorem `swap_smul_involutive` / 定理 `swap_smul_involutive`

English:
theorem swap_smul_involutive
  given: [MulAction (Perm α) β] (i j : α)
  proof: swap_smul_self_smul i j

中文:
定理 swap_smul_involutive
  条件: [乘法作用 (置换 α) β] (i j : α)
  证明: swap_smul_self_smul i j

Depends on / 依赖: swap_smul_self_smul
-/
theorem swap_smul_involutive [MulAction (Perm α) β] (i j : α) :
    Function.Involutive (swap i j • · : β -> β) := swap_smul_self_smul i j

end Swap
end Equiv

open Equiv Function

namespace Set
variable {α : Type*} {f : Perm α} {s : Set α}

/--
lemma `BijOn.perm_inv` / 引理 `BijOn.perm_inv`

English:
lemma BijOn.perm_inv
  given: (hf : BijOn f s s)
  statement: BijOn ↑(f⁻¹) s s
  proof: hf.symm f.invOn

中文:
引理 双射限制.perm_inv
  条件: (hf : 双射限制 f s s)
  结论: 双射限制 ↑(f⁻¹) s s
  证明: hf.symm f.invOn

Depends on / 依赖: f.invOn, hf.symm
-/
lemma BijOn.perm_inv (hf : BijOn f s s) : BijOn ↑(f⁻¹) s s := hf.symm f.invOn

/--
lemma `MapsTo.perm_pow` / 引理 `MapsTo.perm_pow`

English:
lemma MapsTo.perm_pow
  statement: MapsTo f s s -> forall n : Nat, MapsTo (f ^ n) s s
  proof: by
  simp_rw [Equiv.Perm.coe_pow]; exact MapsTo.iterate

中文:
引理 映射到.perm_pow
  结论: 映射到 f s s -> 对任意 n : 自然数, 映射到 (f ^ n) s s
  证明: by
  simp_rw [Equiv.Perm.coe_pow]; exact MapsTo.iterate

Depends on / 依赖: Equiv.Perm.coe_pow, MapsTo, MapsTo.iterate, coe_pow, iterate, simp_rw
-/
lemma MapsTo.perm_pow : MapsTo f s s -> forall n : Nat, MapsTo (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact MapsTo.iterate
/--
lemma `SurjOn.perm_pow` / 引理 `SurjOn.perm_pow`

English:
lemma SurjOn.perm_pow
  statement: SurjOn f s s -> forall n : Nat, SurjOn (f ^ n) s s
  proof: by
  simp_rw [Equiv.Perm.coe_pow]; exact SurjOn.iterate

中文:
引理 满射限制.perm_pow
  结论: 满射限制 f s s -> 对任意 n : 自然数, 满射限制 (f ^ n) s s
  证明: by
  simp_rw [Equiv.Perm.coe_pow]; exact SurjOn.iterate

Depends on / 依赖: Equiv.Perm.coe_pow, SurjOn, SurjOn.iterate, coe_pow, iterate, simp_rw
-/
lemma SurjOn.perm_pow : SurjOn f s s -> forall n : Nat, SurjOn (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact SurjOn.iterate
/--
lemma `BijOn.perm_pow` / 引理 `BijOn.perm_pow`

English:
lemma BijOn.perm_pow
  statement: BijOn f s s -> forall n : Nat, BijOn (f ^ n) s s
  proof: by
  simp_rw [Equiv.Perm.coe_pow]; exact BijOn.iterate

中文:
引理 双射限制.perm_pow
  结论: 双射限制 f s s -> 对任意 n : 自然数, 双射限制 (f ^ n) s s
  证明: by
  simp_rw [Equiv.Perm.coe_pow]; exact BijOn.iterate

Depends on / 依赖: BijOn.iterate, Equiv.Perm.coe_pow, coe_pow, iterate, simp_rw
-/
lemma BijOn.perm_pow : BijOn f s s -> forall n : Nat, BijOn (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact BijOn.iterate

/--
lemma `BijOn.perm_zpow` / 引理 `BijOn.perm_zpow`

English:
lemma BijOn.perm_zpow
  given: (hf : BijOn f s s)
  statement: forall n : Int, BijOn (f ^ n) s s

中文:
引理 双射限制.perm_zpow
  条件: (hf : 双射限制 f s s)
  结论: 对任意 n : 整数, 双射限制 (f ^ n) s s
-/
lemma BijOn.perm_zpow (hf : BijOn f s s) : forall n : Int, BijOn (f ^ n) s s
  | Int.ofNat n => hf.perm_pow n
  | Int.negSucc n => (hf.perm_pow (n + 1)).perm_inv

end Set
