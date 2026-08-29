/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# The `ZMod n`-algebra structure on rings whose characteristic divides `n`
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace ZMod

variable (R : Type*) [Ring R]

instance (p : Nat) : Subsingleton (Algebra (ZMod p) R) :=
⟨fun _ _ => Algebra.algebra_ext _ _ RingHom.congr_fun Subsingleton.elim _ _⟩

section

variable {n : Nat} (m : Nat) [CharP R m]

/--
Definition of `algebra'` / `algebra'` 的定义

English:
abbreviation algebra'
  signature: (h : m ∣ n)
  body: ZMod.castHom h R
  smul := fun a r => cast a * r
  commutes' := fun a r =>
    show (cast a * r : R) = r * cast a by
      rcases ZMod.intCast_surjective a with ⟨k, rfl⟩
      change ZMod.castHom h R k * r = r * ZMod.castHom h R k
      rw [map_intCast]; rw [Int.cast_comm]
  smul_def' := fun _ _ => rfl

中文:
缩写 algebra'
  签名: (h : m ∣ n)
  定义体: ZMod.castHom h R
  smul := fun a r => cast a * r
  commutes' := fun a r =>
    show (cast a * r : R) = r * cast a by
      rcases ZMod.intCast_surjective a with ⟨k, rfl⟩
      change ZMod.castHom h R k * r = r * ZMod.castHom h R k
      rw [map_intCast]; rw [Int.cast_comm]
  smul_def' := fun _ _ => rfl

Depends on / 依赖: ZMod.castHom, castHom
-/
abbrev algebra' (h : m ∣ n) : Algebra (ZMod n) R where
  algebraMap := ZMod.castHom h R
  smul := fun a r => cast a * r
  commutes' := fun a r =>
    show (cast a * r : R) = r * cast a by
      rcases ZMod.intCast_surjective a with ⟨k, rfl⟩
      change ZMod.castHom h R k * r = r * ZMod.castHom h R k
      rw [map_intCast]; rw [Int.cast_comm]
  smul_def' := fun _ _ => rfl

end

/--
Definition of `algebra` / `algebra` 的定义

English:
abbreviation algebra
  signature: (p : Nat) [CharP R p]
  body: algebra' R p dvd_rfl

中文:
缩写 algebra
  签名: (p : 自然数) [特征p R p]
  定义体: algebra' R p dvd_rfl

Depends on / 依赖: algebra, dvd_rfl
-/
abbrev algebra (p : Nat) [CharP R p] : Algebra (ZMod p) R :=
  algebra' R p dvd_rfl

set_option backward.isDefEq.respectTransparency false in
/-- Any ring with a `ZMod p`-module structure can be upgraded to a `ZMod p`-algebra. Not an
instance because this is usually not the default way, and this will cause typeclass search loop. -/
@[instance_reducible]
/--
Definition of `algebraOfModule` / `algebraOfModule` 的定义

English:
definition algebraOfModule
  signature: (n : Nat) (R : Type*) [Ring R] [Module (ZMod n) R]
  body: Algebra.ofModule' (proof · · |>.1) (proof · · |>.2) where
  proof (r : ZMod n) (x : R) : r • 1 * x = r • x ∧ x * r • 1 = r • x := by
    obtain _ | n := n
    · obtain rfl : ((inferInstance : Module Int R)) = ‹_› := Subsingleton.elim _ _
      simp [ZMod, Int.cast_comm]
    · obtain ⟨r, rfl⟩ := ZMod.natCast_zmod_surjective r
      simp [Nat.cast_smul_eq_nsmul, Nat.cast_comm]

中文:
定义 algebraOfModule
  签名: (n : 自然数) (R : 类型) [环 R] [模 (ZMod n) R]
  定义体: Algebra.ofModule' (proof · · |>.1) (proof · · |>.2) where
  proof (r : ZMod n) (x : R) : r • 1 * x = r • x ∧ x * r • 1 = r • x := by
    obtain _ | n := n
    · obtain rfl : ((inferInstance : Module Int R)) = ‹_› := Subsingleton.elim _ _
      simp [ZMod, Int.cast_comm]
    · obtain ⟨r, rfl⟩ := ZMod.natCast_zmod_surjective r
      simp [Nat.cast_smul_eq_nsmul, Nat.cast_comm]

Depends on / 依赖: Algebra, Algebra.ofModule, Int.cast_comm, Module, Nat.cast_comm, Nat.cast_smul_eq_nsmul, Subsingleton, Subsingleton.elim, ZMod.natCast_zmod_surjective, cast_comm, cast_smul_eq_nsmul, natCast_zmod_surjective, ofModule
-/
def algebraOfModule (n : Nat) (R : Type*) [Ring R] [Module (ZMod n) R] : Algebra (ZMod n) R :=
  Algebra.ofModule' (proof · · |>.1) (proof · · |>.2) where
  proof (r : ZMod n) (x : R) : r • 1 * x = r • x ∧ x * r • 1 = r • x := by
    obtain _ | n := n
    · obtain rfl : ((inferInstance : Module Int R)) = ‹_› := Subsingleton.elim _ _
      simp [ZMod, Int.cast_comm]
    · obtain ⟨r, rfl⟩ := ZMod.natCast_zmod_surjective r
      simp [Nat.cast_smul_eq_nsmul, Nat.cast_comm]

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: (n : Nat) (R M : Type*) [Ring R] [AddCommGroup M]
  body: by
  let := ZMod.algebraOfModule n R
  let m₂ := Module.compHom M (algebraMap (ZMod n) R)
  obtain rfl : m₁ = m₂ := Subsingleton.elim _ _
  exact ⟨fun x y z => by rw [Algebra.smul_def, mul_smul]; rfl⟩

中文:
实例 instIsScalarTower
  签名: (n : 自然数) (R M : 类型) [环 R] [加法交换群 M]
  定义体: by
  let := ZMod.algebraOfModule n R
  let m₂ := Module.compHom M (algebraMap (ZMod n) R)
  obtain rfl : m₁ = m₂ := Subsingleton.elim _ _
  exact ⟨fun x y z => by rw [Algebra.smul_def, mul_smul]; rfl⟩

Depends on / 依赖: Algebra, Algebra.smul_def, Module, Module.compHom, Subsingleton, Subsingleton.elim, ZMod.algebraOfModule, algebraMap, algebraOfModule, compHom, mul_smul, smul_def
-/
instance instIsScalarTower (n : Nat) (R M : Type*) [Ring R] [AddCommGroup M]
    [Module (ZMod n) R] [m₁ : Module (ZMod n) M] [Module R M] :
    IsScalarTower (ZMod n) R M := by
  let := ZMod.algebraOfModule n R
  let m₂ := Module.compHom M (algebraMap (ZMod n) R)
  obtain rfl : m₁ = m₂ := Subsingleton.elim _ _
  exact ⟨fun x y z => by rw [Algebra.smul_def, mul_smul]; rfl⟩

end ZMod
