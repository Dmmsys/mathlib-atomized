/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Invertible

/-!
# Further basic results about modules.

-/

public section

assert_not_exists Nonneg.inv Multiset

open Function Set

universe u v

variable {α R M M₂ : Type*}

@[simp]
/--
theorem `Units.neg_smul` / 定理 `Units.neg_smul`

English:
theorem Units.neg_smul
  given: [Ring R] [AddCommGroup M] [Module R M] (u : Rˣ) (x : M)
  proof: by
  rw [Units.smul_def]; rw [Units.val_neg]; rw [_root_.neg_smul]; rw [Units.smul_def]

@[simp]

中文:
定理 单位群.neg_smul
  条件: [环 R] [加法交换群 M] [模 R M] (u : Rˣ) (x : M)
  证明: by
  rw [Units.smul_def]; rw [Units.val_neg]; rw [_root_.neg_smul]; rw [Units.smul_def]

@[simp]

Depends on / 依赖: Units.smul_def, Units.val_neg, _root_, _root_.neg_smul, neg_smul, smul_def, val_neg
-/
theorem Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u : Rˣ) (x : M) :
    -u • x = -(u • x) := by
  rw [Units.smul_def]; rw [Units.val_neg]; rw [_root_.neg_smul]; rw [Units.smul_def]

@[simp]
/--
theorem `invOf_two_smul_add_invOf_two_smul` / 定理 `invOf_two_smul_add_invOf_two_smul`

English:
theorem invOf_two_smul_add_invOf_two_smul
  statement: (R) [Semiring R] [AddCommMonoid M] [Module R M]
  proof: Convex.combo_self invOf_two_add_invOf_two _

中文:
定理 invOf_two_smul_add_invOf_two_smul
  结论: (R) [半环 R] [加法交换幺半群 M] [模 R M]
  证明: Convex.combo_self invOf_two_add_invOf_two _

Depends on / 依赖: Convex, Convex.combo_self, combo_self, invOf_two_add_invOf_two
-/
theorem invOf_two_smul_add_invOf_two_smul (R) [Semiring R] [AddCommMonoid M] [Module R M]
    [Invertible (2 : R)] (x : M) :
    (⅟2 : R) • x + (⅟2 : R) • x = x :=
  Convex.combo_self invOf_two_add_invOf_two _

/--
theorem `map_inv_natCast_smul` / 定理 `map_inv_natCast_smul`

English:
theorem map_inv_natCast_smul
  statement: [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
  proof: by
  by_cases hR : (n : R) = 0 <;> by_cases hS : (n : S) = 0
  · simp [hR, hS, map_zero f]
  · suffices forall y, f y = 0 by rw [this, this, smul_zero]
    clear x
    intro x
    rw [← inv_smul_smul₀ hS (f x)]; rw [← map_natCast_smul f R S]
    simp [hR, map_zero f]
  · suffices forall y, f y = 0 b

中文:
定理 map_inv_natCast_smul
  结论: [加法交换幺半群 M] [加法交换幺半群 M₂] {F : 类型} [函数状 F M M₂]
  证明: by
  by_cases hR : (n : R) = 0 <;> by_cases hS : (n : S) = 0
  · simp [hR, hS, map_zero f]
  · suffices forall y, f y = 0 by rw [this, this, smul_zero]
    clear x
    intro x
    rw [← inv_smul_smul₀ hS (f x)]; rw [← map_natCast_smul f R S]
    simp [hR, map_zero f]
  · suffices forall y, f y = 0 b

Depends on / 依赖: map_natCast_smul, map_zero, smul_zero, zero_smul
-/
theorem map_inv_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*)
    [DivisionSemiring R] [DivisionSemiring S] [Module R M]
    [Module S M₂] (n : Nat) (x : M) : f ((n⁻¹ : R) • x) = (n⁻¹ : S) • f x := by
  by_cases hR : (n : R) = 0 <;> by_cases hS : (n : S) = 0
  · simp [hR, hS, map_zero f]
  · suffices forall y, f y = 0 by rw [this, this, smul_zero]
    clear x
    intro x
    rw [← inv_smul_smul₀ hS (f x)]; rw [← map_natCast_smul f R S]
    simp [hR, map_zero f]
  · suffices forall y, f y = 0 by simp [this]
    clear x
    intro x
    rw [← smul_inv_smul₀ hR x]; rw [map_natCast_smul f R S]; rw [hS]; rw [zero_smul]
  · rw [← inv_smul_smul₀ hS (f _), ← map_natCast_smul f R S, smul_inv_smul₀ hR]

/--
theorem `map_inv_intCast_smul` / 定理 `map_inv_intCast_smul`

English:
theorem map_inv_intCast_smul
  statement: [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
  proof: by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [Int.cast_natCast, Int.cast_natCast, map_inv_natCast_smul _ R S]
  · simp_rw [Int.cast_neg, Int.cast_natCast, inv_neg, neg_smul, map_neg,
      map_inv_natCast_smul _ R S]

中文:
定理 map_inv_intCast_smul
  结论: [加法交换群 M] [加法交换群 M₂] {F : 类型} [函数状 F M M₂]
  证明: by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [Int.cast_natCast, Int.cast_natCast, map_inv_natCast_smul _ R S]
  · simp_rw [Int.cast_neg, Int.cast_natCast, inv_neg, neg_smul, map_neg,
      map_inv_natCast_smul _ R S]

Depends on / 依赖: Int.cast_natCast, Int.cast_neg, cast_natCast, cast_neg, eq_nat_or_neg, inv_neg, map_inv_natCast_smul, map_neg, neg_smul, simp_rw, z.eq_nat_or_neg
-/
theorem map_inv_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M]
    [Module S M₂] (z : Int) (x : M) : f ((z⁻¹ : R) • x) = (z⁻¹ : S) • f x := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [Int.cast_natCast, Int.cast_natCast, map_inv_natCast_smul _ R S]
  · simp_rw [Int.cast_neg, Int.cast_natCast, inv_neg, neg_smul, map_neg,
      map_inv_natCast_smul _ R S]

/--
theorem `inv_natCast_smul_eq` / 定理 `inv_natCast_smul_eq`

English:
theorem inv_natCast_smul_eq
  statement: {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
  proof: map_inv_natCast_smul (AddMonoidHom.id E) R S n x

中文:
定理 inv_natCast_smul_eq
  结论: {E : 类型} (R S : 类型) [加法交换幺半群 E] [除半环 R]
  证明: map_inv_natCast_smul (AddMonoidHom.id E) R S n x

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, map_inv_natCast_smul
-/
theorem inv_natCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [DivisionSemiring S] [Module R E] [Module S E] (n : Nat) (x : E) :
    (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_natCast_smul (AddMonoidHom.id E) R S n x

/--
theorem `inv_intCast_smul_eq` / 定理 `inv_intCast_smul_eq`

English:
theorem inv_intCast_smul_eq
  statement: {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
  proof: map_inv_intCast_smul (AddMonoidHom.id E) R S n x

中文:
定理 inv_intCast_smul_eq
  结论: {E : 类型} (R S : 类型) [加法交换群 E] [除环 R]
  证明: map_inv_intCast_smul (AddMonoidHom.id E) R S n x

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, map_inv_intCast_smul
-/
theorem inv_intCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (n : Int) (x : E) : (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_intCast_smul (AddMonoidHom.id E) R S n x

/--
theorem `inv_natCast_smul_comm` / 定理 `inv_natCast_smul_comm`

English:
theorem inv_natCast_smul_comm
  statement: {α E : Type*} (R : Type*) [AddCommMonoid E] [DivisionSemiring R]
  proof: (map_inv_natCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

中文:
定理 inv_natCast_smul_comm
  结论: {α E : 类型} (R : 类型) [加法交换幺半群 E] [除半环 R]
  证明: (map_inv_natCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, map_inv_natCast_smul, toAddMonoidHom
-/
theorem inv_natCast_smul_comm {α E : Type*} (R : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [Module R E] [DistribSMul α E] (n : Nat) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_natCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

/--
theorem `inv_intCast_smul_comm` / 定理 `inv_intCast_smul_comm`

English:
theorem inv_intCast_smul_comm
  statement: {α E : Type*} (R : Type*) [AddCommGroup E] [DivisionRing R]
  proof: (map_inv_intCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

中文:
定理 inv_intCast_smul_comm
  结论: {α E : 类型} (R : 类型) [加法交换群 E] [除环 R]
  证明: (map_inv_intCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, map_inv_intCast_smul, toAddMonoidHom
-/
theorem inv_intCast_smul_comm {α E : Type*} (R : Type*) [AddCommGroup E] [DivisionRing R]
    [Module R E] [DistribSMul α E] (n : Int) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_intCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

namespace Function

/--
lemma `support_smul_subset_left` / 引理 `support_smul_subset_left`

English:
lemma support_smul_subset_left
  given: [Zero R] [Zero M] [SMulWithZero R M] (f : α -> R) (g : α -> M)
  proof: fun x hfg hf =>
hfg by rw [Pi.smul_apply', hf, zero_smul]

中文:
引理 support_smul_subset_left
  条件: [零 R] [零 M] [带零标量乘法 R M] (f : α -> R) (g : α -> M)
  证明: fun x hfg hf =>
hfg by rw [Pi.smul_apply', hf, zero_smul]
-/
lemma support_smul_subset_left [Zero R] [Zero M] [SMulWithZero R M] (f : α -> R) (g : α -> M) :
    support (f • g) subseteq support f := fun x hfg hf =>
hfg by rw [Pi.smul_apply', hf, zero_smul]

-- Changed (2024-01-21): this lemma was generalised;
-- the old version is now called `support_const_smul_subset`.
/--
lemma `support_smul_subset_right` / 引理 `support_smul_subset_right`

English:
lemma support_smul_subset_right
  given: [Zero M] [SMulZeroClass R M] (f : α -> R) (g : α -> M)
  proof: fun x hbf hf => hbf by rw [Pi.smul_apply', hf, smul_zero]

中文:
引理 support_smul_subset_right
  条件: [零 M] [SMulZero类 R M] (f : α -> R) (g : α -> M)
  证明: fun x hbf hf => hbf by rw [Pi.smul_apply', hf, smul_zero]

Depends on / 依赖: Pi.smul_apply, smul_apply, smul_zero
-/
lemma support_smul_subset_right [Zero M] [SMulZeroClass R M] (f : α -> R) (g : α -> M) :
    support (f • g) subseteq support g :=
fun x hbf hf => hbf by rw [Pi.smul_apply', hf, smul_zero]

/--
lemma `support_const_smul_of_ne_zero` / 引理 `support_const_smul_of_ne_zero`

English:
lemma support_const_smul_of_ne_zero
  statement: [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
  proof: ext fun _ => smul_ne_zero_iff_right hc

中文:
引理 support_const_smul_of_ne_zero
  结论: [半环 R] [是整环 R] [加法交换幺半群 M] [模 R M]
  证明: ext fun _ => smul_ne_zero_iff_right hc

Depends on / 依赖: smul_ne_zero_iff_right
-/
lemma support_const_smul_of_ne_zero [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
    [Module.IsTorsionFree R M] (c : R) (g : α -> M) (hc : c != 0) : support (c • g) = support g :=
  ext fun _ => smul_ne_zero_iff_right hc

/--
lemma `support_smul` / 引理 `support_smul`

English:
lemma support_smul
  statement: [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
  proof: ext fun _ => smul_ne_zero_iff

中文:
引理 support_smul
  结论: [半环 R] [是整环 R] [加法交换幺半群 M] [模 R M]
  证明: ext fun _ => smul_ne_zero_iff

Depends on / 依赖: smul_ne_zero_iff
-/
lemma support_smul [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
    [Module.IsTorsionFree R M] (f : α -> R) (g : α -> M) : support (f • g) = support f inter support g :=
  ext fun _ => smul_ne_zero_iff

/--
lemma `support_const_smul_subset` / 引理 `support_const_smul_subset`

English:
lemma support_const_smul_subset
  given: [Zero M] [SMulZeroClass R M] (a : R) (f : α -> M)
  proof: support_smul_subset_right (fun _ => a) f

中文:
引理 support_const_smul_subset
  条件: [零 M] [SMulZero类 R M] (a : R) (f : α -> M)
  证明: support_smul_subset_right (fun _ => a) f

Depends on / 依赖: support_smul_subset_right
-/
lemma support_const_smul_subset [Zero M] [SMulZeroClass R M] (a : R) (f : α -> M) :
    support (a • f) subseteq support f := support_smul_subset_right (fun _ => a) f

end Function

namespace Set
section SMulZeroClass
variable [Zero M] [SMulZeroClass R M]

/--
lemma `indicator_smul_apply` / 引理 `indicator_smul_apply`

English:
lemma indicator_smul_apply
  given: (s : Set α) (r : α -> R) (f : α -> M) (a : α)
  proof: by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (smul_zero (r a)).symm]

中文:
引理 indicator_smul_apply
  条件: (s : 集合 α) (r : α -> R) (f : α -> M) (a : α)
  证明: by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (smul_zero (r a)).symm]

Depends on / 依赖: exacts, indicator, smul_zero, split_ifs
-/
lemma indicator_smul_apply (s : Set α) (r : α -> R) (f : α -> M) (a : α) :
    indicator s (fun a => r a • f a) a = r a • indicator s f a := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (smul_zero (r a)).symm]

/--
lemma `indicator_smul` / 引理 `indicator_smul`

English:
lemma indicator_smul
  given: (s : Set α) (r : α -> R) (f : α -> M)
  proof: funext indicator_smul_apply s r f

中文:
引理 indicator_smul
  条件: (s : 集合 α) (r : α -> R) (f : α -> M)
  证明: funext indicator_smul_apply s r f

Depends on / 依赖: indicator_smul_apply
-/
lemma indicator_smul (s : Set α) (r : α -> R) (f : α -> M) :
    indicator s (fun a => r a • f a) = fun a => r a • indicator s f a :=
funext indicator_smul_apply s r f

/--
lemma `indicator_const_smul_apply` / 引理 `indicator_const_smul_apply`

English:
lemma indicator_const_smul_apply
  given: (s : Set α) (r : R) (f : α -> M) (a : α)
  proof: indicator_smul_apply s (fun _ => r) f a

中文:
引理 indicator_const_smul_apply
  条件: (s : 集合 α) (r : R) (f : α -> M) (a : α)
  证明: indicator_smul_apply s (fun _ => r) f a

Depends on / 依赖: indicator_smul_apply
-/
lemma indicator_const_smul_apply (s : Set α) (r : R) (f : α -> M) (a : α) :
    indicator s (r • f ·) a = r • indicator s f a :=
  indicator_smul_apply s (fun _ => r) f a

/--
lemma `indicator_const_smul` / 引理 `indicator_const_smul`

English:
lemma indicator_const_smul
  given: (s : Set α) (r : R) (f : α -> M)
  proof: funext indicator_const_smul_apply s r f

中文:
引理 indicator_const_smul
  条件: (s : 集合 α) (r : R) (f : α -> M)
  证明: funext indicator_const_smul_apply s r f

Depends on / 依赖: indicator_const_smul_apply
-/
lemma indicator_const_smul (s : Set α) (r : R) (f : α -> M) :
    indicator s (r • f ·) = (r • indicator s f ·) :=
funext indicator_const_smul_apply s r f

end SMulZeroClass

section SMulWithZero
variable [Zero R] [Zero M] [SMulWithZero R M]

/--
lemma `indicator_smul_apply_left` / 引理 `indicator_smul_apply_left`

English:
lemma indicator_smul_apply_left
  given: (s : Set α) (r : α -> R) (f : α -> M) (a : α)
  proof: by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (zero_smul _ (f a)).symm]

中文:
引理 indicator_smul_apply_left
  条件: (s : 集合 α) (r : α -> R) (f : α -> M) (a : α)
  证明: by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (zero_smul _ (f a)).symm]

Depends on / 依赖: exacts, indicator, split_ifs, zero_smul
-/
lemma indicator_smul_apply_left (s : Set α) (r : α -> R) (f : α -> M) (a : α) :
    indicator s (fun a => r a • f a) a = indicator s r a • f a := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (zero_smul _ (f a)).symm]

/--
lemma `indicator_smul_left` / 引理 `indicator_smul_left`

English:
lemma indicator_smul_left
  given: (s : Set α) (r : α -> R) (f : α -> M)
  proof: funext indicator_smul_apply_left _ _ _

中文:
引理 indicator_smul_left
  条件: (s : 集合 α) (r : α -> R) (f : α -> M)
  证明: funext indicator_smul_apply_left _ _ _

Depends on / 依赖: indicator_smul_apply_left
-/
lemma indicator_smul_left (s : Set α) (r : α -> R) (f : α -> M) :
    indicator s (fun a => r a • f a) = fun a => indicator s r a • f a :=
funext indicator_smul_apply_left _ _ _

/--
lemma `indicator_smul_const_apply` / 引理 `indicator_smul_const_apply`

English:
lemma indicator_smul_const_apply
  given: (s : Set α) (r : α -> R) (m : M) (a : α)
  proof: indicator_smul_apply_left _ _ _ _

中文:
引理 indicator_smul_const_apply
  条件: (s : 集合 α) (r : α -> R) (m : M) (a : α)
  证明: indicator_smul_apply_left _ _ _ _

Depends on / 依赖: indicator_smul_apply_left
-/
lemma indicator_smul_const_apply (s : Set α) (r : α -> R) (m : M) (a : α) :
    indicator s (r · • m) a = indicator s r a • m := indicator_smul_apply_left _ _ _ _

/--
lemma `indicator_smul_const` / 引理 `indicator_smul_const`

English:
lemma indicator_smul_const
  given: (s : Set α) (r : α -> R) (m : M)
  proof: funext indicator_smul_const_apply _ _ _

中文:
引理 indicator_smul_const
  条件: (s : 集合 α) (r : α -> R) (m : M)
  证明: funext indicator_smul_const_apply _ _ _

Depends on / 依赖: indicator_smul_const_apply
-/
lemma indicator_smul_const (s : Set α) (r : α -> R) (m : M) :
    indicator s (r · • m) = (indicator s r · • m) :=
funext indicator_smul_const_apply _ _ _

end SMulWithZero

section MulZeroOneClass

variable [MulZeroOneClass R]

/--
lemma `smul_indicator_one_apply` / 引理 `smul_indicator_one_apply`

English:
lemma smul_indicator_one_apply
  given: (s : Set α) (r : R) (a : α)
  proof: by
  simp_rw [← indicator_const_smul_apply, Pi.one_apply, smul_eq_mul, mul_one]

中文:
引理 smul_indicator_one_apply
  条件: (s : 集合 α) (r : R) (a : α)
  证明: by
  simp_rw [← indicator_const_smul_apply, Pi.one_apply, smul_eq_mul, mul_one]

Depends on / 依赖: Pi.one_apply, indicator_const_smul_apply, mul_one, one_apply, simp_rw, smul_eq_mul
-/
lemma smul_indicator_one_apply (s : Set α) (r : R) (a : α) :
    r • s.indicator (1 : α -> R) a = s.indicator (fun _ => r) a := by
  simp_rw [← indicator_const_smul_apply, Pi.one_apply, smul_eq_mul, mul_one]

end MulZeroOneClass
end Set
