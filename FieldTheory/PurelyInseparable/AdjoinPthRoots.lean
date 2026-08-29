/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!

# The extension adjoining all p-th roots to a field of characteristic p.

In this file, we introduce the field extension adjoining all `p`-th roots to a
field of (exponential) characteristic `p`.

# Main definitions and results

* `AdjoinPthRoots`: the field extension adjoining all `p`-th roots to a field of
  (exponential) characteristic `p`.
* `AdjoinPthRoots.root`: for `k` a field of (exponential) characteristic `p`, the `p`-th root map
  `k → AdjoinPthRoots k`, mapping an element to its unique `p`-th root in `AdjoinPthRoots`,
  as a `RingEquiv`.

-/

public section

variable (k : Type*) [Field k]

-- Note: It is defined as a typeclass synonym of the field `k` itself
-- with a `k`-algebra structure given by the frobenius map.
/--
Definition of `AdjoinPthRoots` / `AdjoinPthRoots` 的定义

English:
definition AdjoinPthRoots
  body: k

@[no_expose]

中文:
定义 AdjoinPthRoots
  定义体: k

@[no_expose]
-/
def AdjoinPthRoots := k

@[no_expose]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Field (AdjoinPthRoots k)
  body: inferInstanceAs (Field k)

@[no_expose]

中文:
实例 :
  签名: Field (AdjoinPthRoots k)
  定义体: inferInstanceAs (Field k)

@[no_expose]
-/
noncomputable instance : Field (AdjoinPthRoots k) := inferInstanceAs (Field k)

@[no_expose]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra k (AdjoinPthRoots k)
  body: (frobenius k (ringExpChar k)).toAlgebra

中文:
实例 :
  签名: Algebra k (AdjoinPthRoots k)
  定义体: (frobenius k (ringExpChar k)).toAlgebra

Depends on / 依赖: frobenius, ringExpChar, toAlgebra
-/
noncomputable instance : Algebra k (AdjoinPthRoots k) := (frobenius k (ringExpChar k)).toAlgebra

instance (p : Nat) [ExpChar k p] : ExpChar (AdjoinPthRoots k) p := inferInstanceAs (ExpChar k p)

/--
Definition of `AdjoinPthRoots.root` / `AdjoinPthRoots.root` 的定义

English:
definition AdjoinPthRoots.root
  signature: : k ≃+* AdjoinPthRoots k
  body: RingEquiv.refl k

中文:
定义 AdjoinPthRoots.root
  签名: : k ≃+* AdjoinPthRoots k
  定义体: RingEquiv.refl k

Depends on / 依赖: RingEquiv, RingEquiv.refl
-/
noncomputable def AdjoinPthRoots.root : k ≃+* AdjoinPthRoots k := RingEquiv.refl k

variable {k} (p : Nat) [ExpChar k p]

@[simp]
/--
lemma `AdjoinPthRoots.root_pow` / 引理 `AdjoinPthRoots.root_pow`

English:
lemma AdjoinPthRoots.root_pow
  given: (x : k)
  proof: by
  rw [← ringExpChar.eq k p]
  rfl

中文:
引理 AdjoinPthRoots.root_pow
  条件: (x : k)
  证明: by
  rw [← ringExpChar.eq k p]
  rfl

Depends on / 依赖: ringExpChar, ringExpChar.eq
-/
lemma AdjoinPthRoots.root_pow (x : k) :
    (AdjoinPthRoots.root k x) ^ p = algebraMap k (AdjoinPthRoots k) x := by
  rw [← ringExpChar.eq k p]
  rfl

/--
lemma `AdjoinPthRoots.algebraMap_root_symm` / 引理 `AdjoinPthRoots.algebraMap_root_symm`

English:
lemma AdjoinPthRoots.algebraMap_root_symm
  given: (x : AdjoinPthRoots k)
  proof: by
  rw [← ringExpChar.eq k p]
  rfl

中文:
引理 AdjoinPthRoots.algebraMap_root_symm
  条件: (x : AdjoinPthRoots k)
  证明: by
  rw [← ringExpChar.eq k p]
  rfl

Depends on / 依赖: ringExpChar, ringExpChar.eq
-/
lemma AdjoinPthRoots.algebraMap_root_symm (x : AdjoinPthRoots k) :
    algebraMap k (AdjoinPthRoots k) ((AdjoinPthRoots.root k).symm x) = x ^ p := by
  rw [← ringExpChar.eq k p]
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPurelyInseparable k (AdjoinPthRoots k)
  body: by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  rw [isPurelyInseparable_iff_pow_mem k p]
  intro x
  use 1, (AdjoinPthRoots.root k).symm x
  simp [AdjoinPthRoots.algebraMap_root_symm p]

中文:
实例 :
  签名: IsPurelyInseparable k (AdjoinPthRoots k)
  定义体: by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  rw [isPurelyInseparable_iff_pow_mem k p]
  intro x
  use 1, (AdjoinPthRoots.root k).symm x
  simp [AdjoinPthRoots.algebraMap_root_symm p]

Depends on / 依赖: AdjoinPthRoots, AdjoinPthRoots.algebraMap_root_symm, AdjoinPthRoots.root, ExpChar, ExpChar.exists, algebraMap_root_symm, isPurelyInseparable_iff_pow_mem
-/
instance : IsPurelyInseparable k (AdjoinPthRoots k) := by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  rw [isPurelyInseparable_iff_pow_mem k p]
  intro x
  use 1, (AdjoinPthRoots.root k).symm x
  simp [AdjoinPthRoots.algebraMap_root_symm p]
