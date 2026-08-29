/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Endomorphisms of a module

In this file we define the type of linear endomorphisms of a module over a ring (`Module.End`).
We set up the basic theory,
including the action of `Module.End` on the module we are considering endomorphisms of.

## Main results

* `Module.End.instSemiring` and `Module.End.instRing`: the (semi)ring of endomorphisms formed by
  taking the additive structure above with composition as multiplication.
-/

@[expose] public section

universe u v

/--
Definition of `Module.End` / `Module.End` 的定义

English:
abbreviation Module.End
  signature: (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]
  body: M ->ₗ[R] M

中文:
缩写 模.End
  签名: (R : 类型u) (M : 类型v) [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: M ->ₗ[R] M
-/
abbrev Module.End (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] :=
  M ->ₗ[R] M

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

open Function LinearMap

/-!
## Monoid structure of endomorphisms
-/

namespace Module.End

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (Module.End R M)
  body: ⟨LinearMap.id⟩

中文:
实例 :
  签名: 幺 (模.End R M)
  定义体: ⟨LinearMap.id⟩

Depends on / 依赖: LinearMap, LinearMap.id
-/
instance : One (Module.End R M) := ⟨LinearMap.id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (Module.End R M)
  body: ⟨fun f g => LinearMap.comp f g⟩

中文:
实例 :
  签名: 乘法 (模.End R M)
  定义体: ⟨fun f g => LinearMap.comp f g⟩

Depends on / 依赖: LinearMap, LinearMap.comp
-/
instance : Mul (Module.End R M) := ⟨fun f g => LinearMap.comp f g⟩

/--
theorem `one_eq_id` / 定理 `one_eq_id`

English:
theorem one_eq_id
  statement: (1 : Module.End R M) = .id
  proof: rfl

中文:
定理 one_eq_id
  结论: (1 : 模.End R M) = .id
  证明: rfl
-/
theorem one_eq_id : (1 : Module.End R M) = .id := rfl

/--
theorem `mul_eq_comp` / 定理 `mul_eq_comp`

English:
theorem mul_eq_comp
  given: (f g : Module.End R M)
  statement: f * g = f.comp g
  proof: rfl

@[simp]

中文:
定理 mul_eq_comp
  条件: (f g : 模.End R M)
  结论: f * g = f.comp g
  证明: rfl

@[simp]
-/
theorem mul_eq_comp (f g : Module.End R M) : f * g = f.comp g := rfl

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x : M)
  statement: (1 : Module.End R M) x = x
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: (x : M)
  结论: (1 : 模.End R M) x = x
  证明: rfl

@[simp]
-/
theorem one_apply (x : M) : (1 : Module.End R M) x = x := rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (f g : Module.End R M) (x : M)
  statement: (f * g) x = f (g x)
  proof: rfl

中文:
定理 mul_apply
  条件: (f g : 模.End R M) (x : M)
  结论: (f * g) x = f (g x)
  证明: rfl
-/
theorem mul_apply (f g : Module.End R M) (x : M) : (f * g) x = f (g x) := rfl

/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : Module.End R M) = _root_.id
  proof: rfl

中文:
定理 coe_one
  结论: ⇑(1 : 模.End R M) = _root_.id
  证明: rfl
-/
theorem coe_one : ⇑(1 : Module.End R M) = _root_.id := rfl

/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : Module.End R M)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
定理 coe_mul
  条件: (f g : 模.End R M)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
theorem coe_mul (f g : Module.End R M) : ⇑(f * g) = f ∘ g := rfl

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [Nontrivial M]
  body: by
  obtain ⟨m, ne⟩ := exists_ne (0 : M)
  exact nontrivial_of_ne 1 0 fun p => ne (LinearMap.congr_fun p m)

中文:
实例 instNontrivial
  签名: [非平凡 M]
  定义体: by
  obtain ⟨m, ne⟩ := exists_ne (0 : M)
  exact nontrivial_of_ne 1 0 fun p => ne (LinearMap.congr_fun p m)

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, exists_ne, nontrivial_of_ne
-/
instance instNontrivial [Nontrivial M] : Nontrivial (Module.End R M) := by
  obtain ⟨m, ne⟩ := exists_ne (0 : M)
  exact nontrivial_of_ne 1 0 fun p => ne (LinearMap.congr_fun p m)

/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (Module.End R M) where
  body: LinearMap.ext fun _ => rfl
  mul_one := comp_id
  one_mul := id_comp

中文:
实例 instMonoid
  签名: : 幺半群 (模.End R M) where
  定义体: LinearMap.ext fun _ => rfl
  mul_one := comp_id
  one_mul := id_comp

Depends on / 依赖: LinearMap, LinearMap.ext
-/
instance instMonoid : Monoid (Module.End R M) where
  mul_assoc _ _ _ := LinearMap.ext fun _ => rfl
  mul_one := comp_id
  one_mul := id_comp

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: : Semiring (Module.End R M) where
  body: AddMonoidWithOne.unary
  __ := instMonoid
  __ := addCommMonoid
  mul_zero := comp_zero
  zero_mul := zero_comp
  left_distrib := fun _ _ _ => comp_add _ _ _
  right_distrib := fun _ _ _ => add_comp _ _ _
  natCast := fun n => n • (1 : M ->ₗ[R] M)
  natCast_zero := zero_smul Nat (1 : M ->ₗ[R] M)
  natCast_succ := fun n => AddMonoid.nsmul_succ n (1 : M ->ₗ[R] M)

中文:
实例 instSemiring
  签名: : 半环 (模.End R M) where
  定义体: AddMonoidWithOne.unary
  __ := instMonoid
  __ := addCommMonoid
  mul_zero := comp_zero
  zero_mul := zero_comp
  left_distrib := fun _ _ _ => comp_add _ _ _
  right_distrib := fun _ _ _ => add_comp _ _ _
  natCast := fun n => n • (1 : M ->ₗ[R] M)
  natCast_zero := zero_smul Nat (1 : M ->ₗ[R] M)
  natCast_succ := fun n => AddMonoid.nsmul_succ n (1 : M ->ₗ[R] M)

Depends on / 依赖: AddMonoidWithOne, AddMonoidWithOne.unary
-/
instance instSemiring : Semiring (Module.End R M) where
  __ := AddMonoidWithOne.unary
  __ := instMonoid
  __ := addCommMonoid
  mul_zero := comp_zero
  zero_mul := zero_comp
  left_distrib := fun _ _ _ => comp_add _ _ _
  right_distrib := fun _ _ _ => add_comp _ _ _
  natCast := fun n => n • (1 : M ->ₗ[R] M)
  natCast_zero := zero_smul Nat (1 : M ->ₗ[R] M)
  natCast_succ := fun n => AddMonoid.nsmul_succ n (1 : M ->ₗ[R] M)

/-- See also `Module.End.natCast_def`. -/
@[simp]
/--
theorem `natCast_apply` / 定理 `natCast_apply`

English:
theorem natCast_apply
  given: (n : Nat) (m : M)
  statement: (↑n : Module.End R M) m = n • m
  proof: rfl

@[simp]

中文:
定理 natCast_apply
  条件: (n : 自然数) (m : M)
  结论: (↑n : 模.End R M) m = n • m
  证明: rfl

@[simp]
-/
theorem natCast_apply (n : Nat) (m : M) : (↑n : Module.End R M) m = n • m := rfl

@[simp]
/--
theorem `ofNat_apply` / 定理 `ofNat_apply`

English:
theorem ofNat_apply
  given: (n : Nat) [n.AtLeastTwo] (m : M)
  proof: rfl

中文:
定理 of自然数_apply
  条件: (n : 自然数) [n.AtLeastTwo] (m : M)
  证明: rfl
-/
theorem ofNat_apply (n : Nat) [n.AtLeastTwo] (m : M) :
    (ofNat(n) : Module.End R M) m = ofNat(n) • m := rfl

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring (Module.End R N₁) where
  body: z • (1 : N₁ ->ₗ[R] N₁)
  intCast_ofNat := natCast_zsmul _
  intCast_negSucc := negSucc_zsmul _

中文:
实例 instRing
  签名: : 环 (模.End R N₁) where
  定义体: z • (1 : N₁ ->ₗ[R] N₁)
  intCast_ofNat := natCast_zsmul _
  intCast_negSucc := negSucc_zsmul _
-/
instance instRing : Ring (Module.End R N₁) where
  intCast z := z • (1 : N₁ ->ₗ[R] N₁)
  intCast_ofNat := natCast_zsmul _
  intCast_negSucc := negSucc_zsmul _

/-- See also `Module.End.intCast_def`. -/
@[simp]
/--
theorem `intCast_apply` / 定理 `intCast_apply`

English:
theorem intCast_apply
  given: (z : Int) (m : N₁)
  statement: (z : Module.End R N₁) m = z • m
  proof: rfl

中文:
定理 intCast_apply
  条件: (z : 整数) (m : N₁)
  结论: (z : 模.End R N₁) m = z • m
  证明: rfl
-/
theorem intCast_apply (z : Int) (m : N₁) : (z : Module.End R N₁) m = z • m :=
  rfl

section

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: :
  body: ⟨smul_comp⟩

中文:
实例 instIsScalarTower
  签名: :
  定义体: ⟨smul_comp⟩

Depends on / 依赖: smul_comp
-/
instance instIsScalarTower :
    IsScalarTower S (Module.End R M) (Module.End R M) :=
  ⟨smul_comp⟩

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMul S R] [IsScalarTower S R M]
  body: ⟨fun s _ _ => (comp_smul _ s _).symm⟩

中文:
实例 instSMulCommClass
  签名: [标量乘法 S R] [标量塔 S R M]
  定义体: ⟨fun s _ _ => (comp_smul _ s _).symm⟩

Depends on / 依赖: comp_smul
-/
instance instSMulCommClass [SMul S R] [IsScalarTower S R M] :
    SMulCommClass S (Module.End R M) (Module.End R M) :=
  ⟨fun s _ _ => (comp_smul _ s _).symm⟩

/--
Instance `instSMulCommClass'` / 实例 `instSMulCommClass'`

English:
instance instSMulCommClass'
  signature: [SMul S R] [IsScalarTower S R M]
  body: SMulCommClass.symm _ _ _

中文:
实例 instSMulCommClass'
  签名: [标量乘法 S R] [标量塔 S R M]
  定义体: SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance instSMulCommClass' [SMul S R] [IsScalarTower S R M] :
    SMulCommClass (Module.End R M) S (Module.End R M) :=
  SMulCommClass.symm _ _ _

/--
theorem `isUnit_apply_inv_apply_of_isUnit` / 定理 `isUnit_apply_inv_apply_of_isUnit`

English:
theorem isUnit_apply_inv_apply_of_isUnit
  given: {f : End R M} (h : IsUnit f) (x : M)
  proof: show (f * h.unit.inv) x = x by simp

中文:
定理 isUnit_apply_inv_apply_of_isUnit
  条件: {f : End R M} (h : 是单位 f) (x : M)
  证明: show (f * h.unit.inv) x = x by simp

Depends on / 依赖: h.unit.inv
-/
theorem isUnit_apply_inv_apply_of_isUnit {f : End R M} (h : IsUnit f) (x : M) :
    f (h.unit.inv x) = x :=
  show (f * h.unit.inv) x = x by simp

/--
theorem `isUnit_inv_apply_apply_of_isUnit` / 定理 `isUnit_inv_apply_apply_of_isUnit`

English:
theorem isUnit_inv_apply_apply_of_isUnit
  given: {f : End R M} (h : IsUnit f) (x : M)
  proof: (by simp : (h.unit.inv * f) x = x)

中文:
定理 isUnit_inv_apply_apply_of_isUnit
  条件: {f : End R M} (h : 是单位 f) (x : M)
  证明: (by simp : (h.unit.inv * f) x = x)

Depends on / 依赖: h.unit.inv
-/
theorem isUnit_inv_apply_apply_of_isUnit {f : End R M} (h : IsUnit f) (x : M) :
    h.unit.inv (f x) = x :=
  (by simp : (h.unit.inv * f) x = x)

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (f : End R M) (n : Nat)
  statement: ⇑(f ^ n) = f^[n]
  proof: hom_coe_pow _ rfl (fun _ _ => rfl) _ _

中文:
定理 coe_pow
  条件: (f : End R M) (n : 自然数)
  结论: ⇑(f ^ n) = f^[n]
  证明: hom_coe_pow _ rfl (fun _ _ => rfl) _ _

Depends on / 依赖: hom_coe_pow
-/
theorem coe_pow (f : End R M) (n : Nat) : ⇑(f ^ n) = f^[n] := hom_coe_pow _ rfl (fun _ _ => rfl) _ _

/--
theorem `pow_apply` / 定理 `pow_apply`

English:
theorem pow_apply
  given: (f : End R M) (n : Nat) (m : M)
  statement: (f ^ n) m = f^[n] m
  proof: congr_fun (coe_pow f n) m

中文:
定理 pow_apply
  条件: (f : End R M) (n : 自然数) (m : M)
  结论: (f ^ n) m = f^[n] m
  证明: congr_fun (coe_pow f n) m

Depends on / 依赖: coe_pow, congr_fun
-/
theorem pow_apply (f : End R M) (n : Nat) (m : M) : (f ^ n) m = f^[n] m := congr_fun (coe_pow f n) m

/--
theorem `pow_map_zero_of_le` / 定理 `pow_map_zero_of_le`

English:
theorem pow_map_zero_of_le
  statement: {f : End R M} {m : M} {k l : Nat} (hk : k <= l)
  proof: by
  rw [← Nat.sub_add_cancel hk]; rw [pow_add]; rw [mul_apply]; rw [hm]; rw [map_zero]

中文:
定理 pow_map_zero_of_le
  结论: {f : End R M} {m : M} {k l : 自然数} (hk : k <= l)
  证明: by
  rw [← Nat.sub_add_cancel hk]; rw [pow_add]; rw [mul_apply]; rw [hm]; rw [map_zero]

Depends on / 依赖: Nat.sub_add_cancel, map_zero, mul_apply, pow_add, sub_add_cancel
-/
theorem pow_map_zero_of_le {f : End R M} {m : M} {k l : Nat} (hk : k <= l)
    (hm : (f ^ k) m = 0) : (f ^ l) m = 0 := by
  rw [← Nat.sub_add_cancel hk]; rw [pow_add]; rw [mul_apply]; rw [hm]; rw [map_zero]

/--
theorem `commute_pow_left_of_commute` / 定理 `commute_pow_left_of_commute`

English:
theorem commute_pow_left_of_commute
  proof: by
  induction k with
  | zero => simp [one_eq_id]
  | succ k ih => rw [pow_succ', pow_succ', mul_eq_comp, LinearMap.comp_assoc, ih,
    ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, mul_eq_comp]

@[simp]

中文:
定理 commute_pow_left_of_commute
  证明: by
  induction k with
  | zero => simp [one_eq_id]
  | succ k ih => rw [pow_succ', pow_succ', mul_eq_comp, LinearMap.comp_assoc, ih,
    ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, mul_eq_comp]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, comp_assoc, mul_eq_comp, one_eq_id, pow_succ
-/
theorem commute_pow_left_of_commute
    [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R ->+* R₂}
    {f : M ->ₛₗ[σ₁₂] M₂} {g : Module.End R M} {g₂ : Module.End R₂ M₂}
    (h : g₂.comp f = f.comp g) (k : Nat) : (g₂ ^ k).comp f = f.comp (g ^ k) := by
  induction k with
  | zero => simp [one_eq_id]
  | succ k ih => rw [pow_succ', pow_succ', mul_eq_comp, LinearMap.comp_assoc, ih,
    ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, mul_eq_comp]

@[simp]
/--
theorem `id_pow` / 定理 `id_pow`

English:
theorem id_pow
  given: (n : Nat)
  statement: (id : End R M) ^ n = .id
  proof: one_pow n

中文:
定理 id_pow
  条件: (n : 自然数)
  结论: (id : End R M) ^ n = .id
  证明: one_pow n

Depends on / 依赖: one_pow
-/
theorem id_pow (n : Nat) : (id : End R M) ^ n = .id :=
  one_pow n

variable {f' : End R M}

/--
theorem `iterate_succ` / 定理 `iterate_succ`

English:
theorem iterate_succ
  given: (n : Nat)
  statement: f' ^ (n + 1) = .comp (f' ^ n) f'
  proof: by rw [pow_succ, mul_eq_comp]

中文:
定理 iterate_succ
  条件: (n : 自然数)
  结论: f' ^ (n + 1) = .comp (f' ^ n) f'
  证明: by rw [pow_succ, mul_eq_comp]

Depends on / 依赖: mul_eq_comp, pow_succ
-/
theorem iterate_succ (n : Nat) : f' ^ (n + 1) = .comp (f' ^ n) f' := by rw [pow_succ, mul_eq_comp]
/--
theorem `iterate_succ'` / 定理 `iterate_succ'`

English:
theorem iterate_succ'
  given: (n : Nat)
  statement: f' ^ (n + 1) = .comp f' (f' ^ n)
  proof: by rw [pow_succ', mul_eq_comp]

中文:
定理 iterate_succ'
  条件: (n : 自然数)
  结论: f' ^ (n + 1) = .comp f' (f' ^ n)
  证明: by rw [pow_succ', mul_eq_comp]

Depends on / 依赖: mul_eq_comp, pow_succ
-/
theorem iterate_succ' (n : Nat) : f' ^ (n + 1) = .comp f' (f' ^ n) := by rw [pow_succ', mul_eq_comp]

/--
theorem `iterate_surjective` / 定理 `iterate_surjective`

English:
theorem iterate_surjective
  given: (h : Surjective f')
  statement: forall n : Nat, Surjective (f' ^ n)

中文:
定理 iterate_surjective
  条件: (h : 满射 f')
  结论: 对任意 n : 自然数, 满射 (f' ^ n)
-/
theorem iterate_surjective (h : Surjective f') : forall n : Nat, Surjective (f' ^ n)
  | 0 => surjective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_surjective h n).comp h

/--
theorem `iterate_injective` / 定理 `iterate_injective`

English:
theorem iterate_injective
  given: (h : Injective f')
  statement: forall n : Nat, Injective (f' ^ n)

中文:
定理 iterate_injective
  条件: (h : 单射 f')
  结论: 对任意 n : 自然数, 单射 (f' ^ n)
-/
theorem iterate_injective (h : Injective f') : forall n : Nat, Injective (f' ^ n)
  | 0 => injective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_injective h n).comp h

/--
theorem `iterate_bijective` / 定理 `iterate_bijective`

English:
theorem iterate_bijective
  given: (h : Bijective f')
  statement: forall n : Nat, Bijective (f' ^ n)

中文:
定理 iterate_bijective
  条件: (h : 双射 f')
  结论: 对任意 n : 自然数, 双射 (f' ^ n)
-/
theorem iterate_bijective (h : Bijective f') : forall n : Nat, Bijective (f' ^ n)
  | 0 => bijective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_bijective h n).comp h

/--
theorem `injective_of_iterate_injective` / 定理 `injective_of_iterate_injective`

English:
theorem injective_of_iterate_injective
  given: {n : Nat} (hn : n != 0) (h : Injective (f' ^ n))
  proof: by
  rw [← Nat.succ_pred_eq_of_pos (show 0 < n by lia)]; rw [iterate_succ]; rw [coe_comp] at h
  exact h.of_comp

中文:
定理 injective_of_iterate_injective
  条件: {n : 自然数} (hn : n != 0) (h : 单射 (f' ^ n))
  证明: by
  rw [← Nat.succ_pred_eq_of_pos (show 0 < n by lia)]; rw [iterate_succ]; rw [coe_comp] at h
  exact h.of_comp

Depends on / 依赖: Nat.succ_pred_eq_of_pos, coe_comp, h.of_comp, iterate_succ, of_comp, succ_pred_eq_of_pos
-/
theorem injective_of_iterate_injective {n : Nat} (hn : n != 0) (h : Injective (f' ^ n)) :
    Injective f' := by
  rw [← Nat.succ_pred_eq_of_pos (show 0 < n by lia)]; rw [iterate_succ]; rw [coe_comp] at h
  exact h.of_comp

/--
theorem `surjective_of_iterate_surjective` / 定理 `surjective_of_iterate_surjective`

English:
theorem surjective_of_iterate_surjective
  given: {n : Nat} (hn : n != 0) (h : Surjective (f' ^ n))
  proof: by
  rw [← Nat.succ_pred_eq_of_pos (Nat.pos_iff_ne_zero.mpr hn)]; rw [pow_succ']; rw [coe_mul] at h
  exact Surjective.of_comp h

中文:
定理 surjective_of_iterate_surjective
  条件: {n : 自然数} (hn : n != 0) (h : 满射 (f' ^ n))
  证明: by
  rw [← Nat.succ_pred_eq_of_pos (Nat.pos_iff_ne_zero.mpr hn)]; rw [pow_succ']; rw [coe_mul] at h
  exact Surjective.of_comp h

Depends on / 依赖: Nat.pos_iff_ne_zero.mpr, Nat.succ_pred_eq_of_pos, Surjective, Surjective.of_comp, coe_mul, of_comp, pos_iff_ne_zero, pow_succ, succ_pred_eq_of_pos
-/
theorem surjective_of_iterate_surjective {n : Nat} (hn : n != 0) (h : Surjective (f' ^ n)) :
    Surjective f' := by
  rw [← Nat.succ_pred_eq_of_pos (Nat.pos_iff_ne_zero.mpr hn)]; rw [pow_succ']; rw [coe_mul] at h
  exact Surjective.of_comp h

/--
Definition of `smulLeft` / `smulLeft` 的定义

English:
definition smulLeft
  signature: (α : R) (hα : α in Set.center R)
  body: α • x
  map_add' := smul_add _
  map_smul' β _ := by simp [smul_smul, ((Set.mem_center_iff.mp hα).comm β).eq]

中文:
定义 smulLeft
  签名: (α : R) (hα : α in 集合.center R)
  定义体: α • x
  map_add' := smul_add _
  map_smul' β _ := by simp [smul_smul, ((Set.mem_center_iff.mp hα).comm β).eq]
-/
@[simps] def smulLeft (α : R) (hα : α in Set.center R) : End R M where
  toFun x := α • x
  map_add' := smul_add _
  map_smul' β _ := by simp [smul_smul, ((Set.mem_center_iff.mp hα).comm β).eq]

/--
lemma `smulLeft_eq` / 引理 `smulLeft_eq`

English:
lemma smulLeft_eq
  statement: {R : Type*} [CommSemiring R] [Module R M] (α : R)
  proof: rfl

中文:
引理 smulLeft_eq
  结论: {R : 类型} [交换半环 R] [模 R M] (α : R)
  证明: rfl
-/
@[simp] lemma smulLeft_eq {R : Type*} [CommSemiring R] [Module R M] (α : R)
    (hα : α in Set.center R := by simp) : smulLeft α hα = α • .id (M := M) := rfl

end

/-! ## Action by a module endomorphism. -/


/--
Instance `applyModule` / 实例 `applyModule`

English:
instance applyModule
  signature: : Module (Module.End R M) M where
  body: (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  add_smul := LinearMap.add_apply
  zero_smul := (LinearMap.zero_apply : forall m, (0 : M ->ₗ[R] M) m = 0)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]

中文:
实例 applyModule
  签名: : 模 (模.End R M) M where
  定义体: (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  add_smul := LinearMap.add_apply
  zero_smul := (LinearMap.zero_apply : forall m, (0 : M ->ₗ[R] M) m = 0)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
-/
instance applyModule : Module (Module.End R M) M where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  add_smul := LinearMap.add_apply
  zero_smul := (LinearMap.zero_apply : forall m, (0 : M ->ₗ[R] M) m = 0)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (f : Module.End R M) (a : M)
  statement: f • a = f a
  proof: rfl

中文:
定理 smul_def
  条件: (f : 模.End R M) (a : M)
  结论: f • a = f a
  证明: rfl
-/
protected theorem smul_def (f : Module.End R M) (a : M) : f • a = f a :=
  rfl

/--
Instance `apply_faithfulSMul` / 实例 `apply_faithfulSMul`

English:
instance apply_faithfulSMul
  signature: : FaithfulSMul (Module.End R M) M
  body: ⟨LinearMap.ext⟩

中文:
实例 apply_faithfulSMul
  签名: : 忠实标量乘法 (模.End R M) M
  定义体: ⟨LinearMap.ext⟩

Depends on / 依赖: LinearMap, LinearMap.ext
-/
instance apply_faithfulSMul : FaithfulSMul (Module.End R M) M :=
  ⟨LinearMap.ext⟩

/--
Instance `apply_smulCommClass` / 实例 `apply_smulCommClass`

English:
instance apply_smulCommClass
  signature: [SMul S R] [SMul S M] [IsScalarTower S R M]
  body: (e.map_smul_of_tower r m).symm

中文:
实例 apply_smulCommClass
  签名: [标量乘法 S R] [标量乘法 S M] [标量塔 S R M]
  定义体: (e.map_smul_of_tower r m).symm

Depends on / 依赖: e.map_smul_of_tower, map_smul_of_tower
-/
instance apply_smulCommClass [SMul S R] [SMul S M] [IsScalarTower S R M] :
    SMulCommClass S (Module.End R M) M where
  smul_comm r e m := (e.map_smul_of_tower r m).symm

/--
Instance `apply_smulCommClass'` / 实例 `apply_smulCommClass'`

English:
instance apply_smulCommClass'
  signature: [SMul S R] [SMul S M] [IsScalarTower S R M]
  body: SMulCommClass.symm _ _ _

中文:
实例 apply_smulCommClass'
  签名: [标量乘法 S R] [标量乘法 S M] [标量塔 S R M]
  定义体: SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance apply_smulCommClass' [SMul S R] [SMul S M] [IsScalarTower S R M] :
    SMulCommClass (Module.End R M) S M :=
  SMulCommClass.symm _ _ _

/--
Instance `apply_isScalarTower` / 实例 `apply_isScalarTower`

English:
instance apply_isScalarTower
  signature: [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]
  body: ⟨fun _ _ _ => rfl⟩

中文:
实例 apply_isScalarTower
  签名: [幺半群 S] [分配乘法作用 S M] [标量交换类 R S M]
  定义体: ⟨fun _ _ _ => rfl⟩
-/
instance apply_isScalarTower [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] :
    IsScalarTower S (Module.End R M) M :=
  ⟨fun _ _ _ => rfl⟩

end Module.End

section

/-! ## Actions as module endomorphisms -/

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable [Monoid S]

/-- Each element of the monoid defines a linear map.

This is a stronger version of `DistribSMul.toAddMonoidHom`. -/
@[simps]
/--
Definition of `DistribSMul.toLinearMap` / `DistribSMul.toLinearMap` 的定义

English:
definition DistribSMul.toLinearMap
  signature: [DistribSMul S M] [SMulCommClass S R M] (s : S)
  body: HSMul.hSMul s
  map_add' := smul_add s
  map_smul' _ _ := smul_comm _ _ _

中文:
定义 分配标量乘法.toLinearMap
  签名: [分配标量乘法 S M] [标量交换类 S R M] (s : S)
  定义体: HSMul.hSMul s
  map_add' := smul_add s
  map_smul' _ _ := smul_comm _ _ _

Depends on / 依赖: HSMul.hSMul
-/
def DistribSMul.toLinearMap [DistribSMul S M] [SMulCommClass S R M] (s : S) : M ->ₗ[R] M where
  toFun := HSMul.hSMul s
  map_add' := smul_add s
  map_smul' _ _ := smul_comm _ _ _

/-- Each element of the monoid defines a module endomorphism.

This is a stronger version of `DistribMulAction.toAddMonoidEnd`. -/
@[simps]
/--
Definition of `DistribMulAction.toModuleEnd` / `DistribMulAction.toModuleEnd` 的定义

English:
definition DistribMulAction.toModuleEnd
  signature: [DistribMulAction S M] [SMulCommClass S R M]
  body: DistribSMul.toLinearMap R M
map_one' := LinearMap.ext one_smul _
map_mul' _ _ := LinearMap.ext mul_smul _ _

@[deprecated (since := "2026-01-07")] alias DistribMulAction.toLinearMap := DistribSMul.toLinearMap

中文:
定义 分配乘法作用.toModuleEnd
  签名: [分配乘法作用 S M] [标量交换类 S R M]
  定义体: DistribSMul.toLinearMap R M
map_one' := LinearMap.ext one_smul _
map_mul' _ _ := LinearMap.ext mul_smul _ _

@[deprecated (since := "2026-01-07")] alias DistribMulAction.toLinearMap := DistribSMul.toLinearMap

Depends on / 依赖: DistribSMul, DistribSMul.toLinearMap, toLinearMap
-/
def DistribMulAction.toModuleEnd [DistribMulAction S M] [SMulCommClass S R M] :
    S ->* Module.End R M where
  toFun := DistribSMul.toLinearMap R M
map_one' := LinearMap.ext one_smul _
map_mul' _ _ := LinearMap.ext mul_smul _ _

@[deprecated (since := "2026-01-07")] alias DistribMulAction.toLinearMap := DistribSMul.toLinearMap

end

section Module

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable [Semiring S] [Module S M] [SMulCommClass S R M]

/-- Each element of the semiring defines a module endomorphism.

This is a stronger version of `DistribMulAction.toModuleEnd`. -/
@[simps]
/--
Definition of `Module.toModuleEnd` / `Module.toModuleEnd` 的定义

English:
definition Module.toModuleEnd
  signature: : S ->+* Module.End R M
  body: { DistribMulAction.toModuleEnd R M with
    toFun := DistribSMul.toLinearMap R M
map_zero' := LinearMap.ext zero_smul S
map_add' := fun _ _ => LinearMap.ext add_smul _ _ }

中文:
定义 模.toModuleEnd
  签名: : S ->+* 模.End R M
  定义体: { DistribMulAction.toModuleEnd R M with
    toFun := DistribSMul.toLinearMap R M
map_zero' := LinearMap.ext zero_smul S
map_add' := fun _ _ => LinearMap.ext add_smul _ _ }

Depends on / 依赖: DistribMulAction, DistribMulAction.toModuleEnd, DistribSMul, DistribSMul.toLinearMap, LinearMap, LinearMap.ext, add_smul, map_add, map_zero, toLinearMap, toModuleEnd, zero_smul
-/
def Module.toModuleEnd : S ->+* Module.End R M :=
  { DistribMulAction.toModuleEnd R M with
    toFun := DistribSMul.toLinearMap R M
map_zero' := LinearMap.ext zero_smul S
map_add' := fun _ _ => LinearMap.ext add_smul _ _ }

/-- The canonical (semi)ring isomorphism from `Rᵐᵒᵖ` to `Module.End R R` induced by the right
multiplication. -/
@[simps]
/--
Definition of `RingEquiv.moduleEndSelf` / `RingEquiv.moduleEndSelf` 的定义

English:
definition RingEquiv.moduleEndSelf
  signature: : Rᵐᵒᵖ ≃+* Module.End R R
  body: { Module.toModuleEnd R R with
    toFun := DistribSMul.toLinearMap R R
    invFun := fun f => MulOpposite.op (f 1)
    left_inv := mul_one
right_inv := fun _ => LinearMap.ext_ring one_mul _ }

中文:
定义 环等价.moduleEndSelf
  签名: : Rᵐᵒᵖ ≃+* 模.End R R
  定义体: { Module.toModuleEnd R R with
    toFun := DistribSMul.toLinearMap R R
    invFun := fun f => MulOpposite.op (f 1)
    left_inv := mul_one
right_inv := fun _ => LinearMap.ext_ring one_mul _ }

Depends on / 依赖: DistribSMul, DistribSMul.toLinearMap, LinearMap, LinearMap.ext_ring, Module, Module.toModuleEnd, MulOpposite, MulOpposite.op, ext_ring, invFun, left_inv, mul_one, one_mul, right_inv, toLinearMap, toModuleEnd
-/
def RingEquiv.moduleEndSelf : Rᵐᵒᵖ ≃+* Module.End R R :=
  { Module.toModuleEnd R R with
    toFun := DistribSMul.toLinearMap R R
    invFun := fun f => MulOpposite.op (f 1)
    left_inv := mul_one
right_inv := fun _ => LinearMap.ext_ring one_mul _ }

/-- The canonical (semi)ring isomorphism from `R` to `Module.End Rᵐᵒᵖ R` induced by the left
multiplication. -/
@[simps]
/--
Definition of `RingEquiv.moduleEndSelfOp` / `RingEquiv.moduleEndSelfOp` 的定义

English:
definition RingEquiv.moduleEndSelfOp
  signature: : R ≃+* Module.End Rᵐᵒᵖ R
  body: { Module.toModuleEnd _ _ with
    toFun := DistribSMul.toLinearMap _ _
    invFun := fun f => f 1
    left_inv := mul_one
right_inv := fun _ => LinearMap.ext_ring_op mul_one _ }

中文:
定义 环等价.moduleEndSelfOp
  签名: : R ≃+* 模.End Rᵐᵒᵖ R
  定义体: { Module.toModuleEnd _ _ with
    toFun := DistribSMul.toLinearMap _ _
    invFun := fun f => f 1
    left_inv := mul_one
right_inv := fun _ => LinearMap.ext_ring_op mul_one _ }

Depends on / 依赖: DistribSMul, DistribSMul.toLinearMap, LinearMap, LinearMap.ext_ring_op, Module, Module.toModuleEnd, ext_ring_op, invFun, left_inv, mul_one, right_inv, toLinearMap, toModuleEnd
-/
def RingEquiv.moduleEndSelfOp : R ≃+* Module.End Rᵐᵒᵖ R :=
  { Module.toModuleEnd _ _ with
    toFun := DistribSMul.toLinearMap _ _
    invFun := fun f => f 1
    left_inv := mul_one
right_inv := fun _ => LinearMap.ext_ring_op mul_one _ }

/--
theorem `Module.End.natCast_def` / 定理 `Module.End.natCast_def`

English:
theorem Module.End.natCast_def
  given: (n : Nat) [AddCommMonoid N₁] [Module R N₁]
  proof: rfl

中文:
定理 模.End.natCast_def
  条件: (n : 自然数) [加法交换幺半群 N₁] [模 R N₁]
  证明: rfl
-/
theorem Module.End.natCast_def (n : Nat) [AddCommMonoid N₁] [Module R N₁] :
    (↑n : Module.End R N₁) = Module.toModuleEnd R N₁ n :=
  rfl

/--
theorem `Module.End.intCast_def` / 定理 `Module.End.intCast_def`

English:
theorem Module.End.intCast_def
  given: (z : Int) [AddCommGroup N₁] [Module R N₁]
  proof: rfl

中文:
定理 模.End.intCast_def
  条件: (z : 整数) [加法交换群 N₁] [模 R N₁]
  证明: rfl
-/
theorem Module.End.intCast_def (z : Int) [AddCommGroup N₁] [Module R N₁] :
    (z : Module.End R N₁) = Module.toModuleEnd R N₁ z :=
  rfl

end Module

namespace LinearMap

section AddCommMonoid

section SMulRight

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]
variable [Semiring S] [Module R S] [Module S M] [IsScalarTower R S M]

/--
Definition of `smulRight` / `smulRight` 的定义

English:
definition smulRight
  signature: (f : M₁ ->ₗ[R] S) (x : M)
  body: f b • x
  map_add' x y := by rw [f.map_add, add_smul]
  map_smul' b y := by rw [RingHom.id_apply, map_smul, smul_assoc]

@[simp]

中文:
定义 smulRight
  签名: (f : M₁ ->ₗ[R] S) (x : M)
  定义体: f b • x
  map_add' x y := by rw [f.map_add, add_smul]
  map_smul' b y := by rw [RingHom.id_apply, map_smul, smul_assoc]

@[simp]
-/
def smulRight (f : M₁ ->ₗ[R] S) (x : M) : M₁ ->ₗ[R] M where
  toFun b := f b • x
  map_add' x y := by rw [f.map_add, add_smul]
  map_smul' b y := by rw [RingHom.id_apply, map_smul, smul_assoc]

@[simp]
/--
theorem `coe_smulRight` / 定理 `coe_smulRight`

English:
theorem coe_smulRight
  given: (f : M₁ ->ₗ[R] S) (x : M)
  statement: (smulRight f x : M₁ -> M) = fun c => f c • x
  proof: rfl

中文:
定理 coe_smulRight
  条件: (f : M₁ ->ₗ[R] S) (x : M)
  结论: (smulRight f x : M₁ -> M) = fun c => f c • x
  证明: rfl
-/
theorem coe_smulRight (f : M₁ ->ₗ[R] S) (x : M) : (smulRight f x : M₁ -> M) = fun c => f c • x :=
  rfl

/--
theorem `smulRight_apply` / 定理 `smulRight_apply`

English:
theorem smulRight_apply
  given: (f : M₁ ->ₗ[R] S) (x : M) (c : M₁)
  statement: smulRight f x c = f c • x
  proof: rfl

@[simp]

中文:
定理 smulRight_apply
  条件: (f : M₁ ->ₗ[R] S) (x : M) (c : M₁)
  结论: smulRight f x c = f c • x
  证明: rfl

@[simp]
-/
theorem smulRight_apply (f : M₁ ->ₗ[R] S) (x : M) (c : M₁) : smulRight f x c = f c • x :=
  rfl

@[simp]
/--
lemma `smulRight_zero` / 引理 `smulRight_zero`

English:
lemma smulRight_zero
  given: (f : M₁ ->ₗ[R] S)
  statement: f.smulRight (0 : M) = 0
  proof: by ext; simp

@[simp]

中文:
引理 smulRight_zero
  条件: (f : M₁ ->ₗ[R] S)
  结论: f.smulRight (0 : M) = 0
  证明: by ext; simp

@[simp]
-/
lemma smulRight_zero (f : M₁ ->ₗ[R] S) : f.smulRight (0 : M) = 0 := by ext; simp

@[simp]
/--
lemma `zero_smulRight` / 引理 `zero_smulRight`

English:
lemma zero_smulRight
  given: (x : M)
  statement: (0 : M₁ ->ₗ[R] S).smulRight x = 0
  proof: by ext; simp

@[simp]

中文:
引理 zero_smulRight
  条件: (x : M)
  结论: (0 : M₁ ->ₗ[R] S).smulRight x = 0
  证明: by ext; simp

@[simp]
-/
lemma zero_smulRight (x : M) : (0 : M₁ ->ₗ[R] S).smulRight x = 0 := by ext; simp

@[simp]
/--
lemma `smulRight_apply_eq_zero_iff` / 引理 `smulRight_apply_eq_zero_iff`

English:
lemma smulRight_apply_eq_zero_iff
  given: [IsDomain S] {f : M₁ ->ₗ[R] S} {x : M} [Module.IsTorsionFree S M]
  proof: by simp [DFunLike.ext_iff, forall_or_right]

中文:
引理 smulRight_apply_eq_zero_iff
  条件: [是整环 S] {f : M₁ ->ₗ[R] S} {x : M} [模.是无挠 S M]
  证明: by simp [DFunLike.ext_iff, forall_or_right]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, forall_or_right
-/
lemma smulRight_apply_eq_zero_iff [IsDomain S] {f : M₁ ->ₗ[R] S} {x : M} [Module.IsTorsionFree S M] :
    f.smulRight x = 0 ↔ f = 0 ∨ x = 0 := by simp [DFunLike.ext_iff, forall_or_right]

end SMulRight

end AddCommMonoid

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M] [Module R M₁] [Module R M₂] [Module S M₁] [Module S M₂]
variable [SMulCommClass R S M₁] [SMulCommClass R S M₂]
variable (S)

/-- Applying a linear map at `v : M`, seen as `S`-linear map from `M →ₗ[R] M₂` to `M₂`.

See `LinearMap.applyₗ` for a version where `S = R`. -/
@[simps]
/--
Definition of `applyₗ'` / `applyₗ'` 的定义

English:
definition applyₗ'
  signature: : M ->+ (M ->ₗ[R] M₂) ->ₗ[S] M₂ where
  body: { toFun := fun f => f v
      map_add' := fun f g => f.add_apply g v
      map_smul' := fun x f => f.smul_apply x v }
  map_zero' := LinearMap.ext fun f => f.map_zero
  map_add' _ _ := LinearMap.ext fun f => f.map_add _ _

中文:
定义 applyₗ'
  签名: : M ->+ (M ->ₗ[R] M₂) ->ₗ[S] M₂ where
  定义体: { toFun := fun f => f v
      map_add' := fun f g => f.add_apply g v
      map_smul' := fun x f => f.smul_apply x v }
  map_zero' := LinearMap.ext fun f => f.map_zero
  map_add' _ _ := LinearMap.ext fun f => f.map_add _ _

Depends on / 依赖: LinearMap, LinearMap.ext, add_apply, f.add_apply, f.map_add, f.map_zero, f.smul_apply, map_add, map_smul, map_zero, smul_apply
-/
def applyₗ' : M ->+ (M ->ₗ[R] M₂) ->ₗ[S] M₂ where
  toFun v :=
    { toFun := fun f => f v
      map_add' := fun f g => f.add_apply g v
      map_smul' := fun x f => f.smul_apply x v }
  map_zero' := LinearMap.ext fun f => f.map_zero
  map_add' _ _ := LinearMap.ext fun f => f.map_add _ _

variable [CompatibleSMul M₁ M₂ S R]

/--
Definition of `compRight` / `compRight` 的定义

English:
definition compRight
  signature: (f : M₁ ->ₗ[R] M₂)
  body: f.comp g
  map_add' _ _ := LinearMap.ext fun _ => map_add f _ _
  map_smul' _ _ := LinearMap.ext fun _ => map_smul_of_tower ..

@[simp]

中文:
定义 compRight
  签名: (f : M₁ ->ₗ[R] M₂)
  定义体: f.comp g
  map_add' _ _ := LinearMap.ext fun _ => map_add f _ _
  map_smul' _ _ := LinearMap.ext fun _ => map_smul_of_tower ..

@[simp]

Depends on / 依赖: f.comp
-/
def compRight (f : M₁ ->ₗ[R] M₂) : (M ->ₗ[R] M₁) ->ₗ[S] M ->ₗ[R] M₂ where
  toFun g := f.comp g
  map_add' _ _ := LinearMap.ext fun _ => map_add f _ _
  map_smul' _ _ := LinearMap.ext fun _ => map_smul_of_tower ..

@[simp]
/--
theorem `compRight_apply` / 定理 `compRight_apply`

English:
theorem compRight_apply
  given: (f : M₁ ->ₗ[R] M₂) (g : M ->ₗ[R] M₁)
  statement: compRight S f g = f.comp g
  proof: rfl

中文:
定理 compRight_apply
  条件: (f : M₁ ->ₗ[R] M₂) (g : M ->ₗ[R] M₁)
  结论: compRight S f g = f.comp g
  证明: rfl
-/
theorem compRight_apply (f : M₁ ->ₗ[R] M₂) (g : M ->ₗ[R] M₁) : compRight S f g = f.comp g :=
  rfl

end Module

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]
variable (f : M ->ₗ[R] M₂)

/-- Applying a linear map at `v : M`, seen as a linear map from `M →ₗ[R] M₂` to `M₂`.
See also `LinearMap.applyₗ'` for a version that works with two different semirings.

This is the `LinearMap` version of `toAddMonoidHom.eval`. -/
@[simps]
/--
Definition of `applyₗ` / `applyₗ` 的定义

English:
definition applyₗ
  signature: : M ->ₗ[R] (M ->ₗ[R] M₂) ->ₗ[R] M₂
  body: { applyₗ' R with
    toFun := fun v => { applyₗ' R v with toFun := fun f => f v }
    map_smul' := fun _ _ => LinearMap.ext fun f => map_smul f _ _ }

中文:
定义 applyₗ
  签名: : M ->ₗ[R] (M ->ₗ[R] M₂) ->ₗ[R] M₂
  定义体: { applyₗ' R with
    toFun := fun v => { applyₗ' R v with toFun := fun f => f v }
    map_smul' := fun _ _ => LinearMap.ext fun f => map_smul f _ _ }

Depends on / 依赖: LinearMap, LinearMap.ext, map_smul
-/
def applyₗ : M ->ₗ[R] (M ->ₗ[R] M₂) ->ₗ[R] M₂ :=
  { applyₗ' R with
    toFun := fun v => { applyₗ' R v with toFun := fun f => f v }
    map_smul' := fun _ _ => LinearMap.ext fun f => map_smul f _ _ }

/--
Definition of `smulRightₗ` / `smulRightₗ` 的定义

English:
definition smulRightₗ
  signature: : (M₂ ->ₗ[R] R) ->ₗ[R] M ->ₗ[R] M₂ ->ₗ[R] M where
  body: { toFun := LinearMap.smulRight f
      map_add' := fun m m' => by
        ext
        apply smul_add
      map_smul' := fun c m => by
        ext
        apply smul_comm }
  map_add' f f' := by
    ext
    apply add_smul
  map_smul' c f := by
    ext
    apply mul_smul

@[simp]

中文:
定义 smulRightₗ
  签名: : (M₂ ->ₗ[R] R) ->ₗ[R] M ->ₗ[R] M₂ ->ₗ[R] M where
  定义体: { toFun := LinearMap.smulRight f
      map_add' := fun m m' => by
        ext
        apply smul_add
      map_smul' := fun c m => by
        ext
        apply smul_comm }
  map_add' f f' := by
    ext
    apply add_smul
  map_smul' c f := by
    ext
    apply mul_smul

@[simp]

Depends on / 依赖: LinearMap, LinearMap.smulRight, add_smul, map_add, map_smul, mul_smul, smulRight, smul_add, smul_comm
-/
def smulRightₗ : (M₂ ->ₗ[R] R) ->ₗ[R] M ->ₗ[R] M₂ ->ₗ[R] M where
  toFun f :=
    { toFun := LinearMap.smulRight f
      map_add' := fun m m' => by
        ext
        apply smul_add
      map_smul' := fun c m => by
        ext
        apply smul_comm }
  map_add' f f' := by
    ext
    apply add_smul
  map_smul' c f := by
    ext
    apply mul_smul

@[simp]
/--
theorem `smulRightₗ_apply` / 定理 `smulRightₗ_apply`

English:
theorem smulRightₗ_apply
  given: (f : M₂ ->ₗ[R] R) (x : M)
  proof: rfl

中文:
定理 smulRightₗ_apply
  条件: (f : M₂ ->ₗ[R] R) (x : M)
  证明: rfl
-/
theorem smulRightₗ_apply (f : M₂ ->ₗ[R] R) (x : M) :
    (smulRightₗ : (M₂ ->ₗ[R] R) ->ₗ[R] M ->ₗ[R] M₂ ->ₗ[R] M) f x = smulRight f x :=
  rfl

/--
theorem `smulRightₗ_apply_apply` / 定理 `smulRightₗ_apply_apply`

English:
theorem smulRightₗ_apply_apply
  given: (f : M₂ ->ₗ[R] R) (x : M) (y : M₂)
  proof: rfl

中文:
定理 smulRightₗ_apply_apply
  条件: (f : M₂ ->ₗ[R] R) (x : M) (y : M₂)
  证明: rfl
-/
theorem smulRightₗ_apply_apply (f : M₂ ->ₗ[R] R) (x : M) (y : M₂) :
    smulRightₗ f x y = f y • x := rfl

end CommSemiring

end LinearMap

namespace Module.End

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (f : Module.End R M)

/--
lemma `commute_id_left` / 引理 `commute_id_left`

English:
lemma commute_id_left
  statement: Commute LinearMap.id f
  proof: by ext; simp

中文:
引理 commute_id_left
  结论: Commute 线性映射.id f
  证明: by ext; simp
-/
lemma commute_id_left : Commute LinearMap.id f := by ext; simp

/--
lemma `commute_id_right` / 引理 `commute_id_right`

English:
lemma commute_id_right
  statement: Commute f LinearMap.id
  proof: by ext; simp

中文:
引理 commute_id_right
  结论: Commute f 线性映射.id
  证明: by ext; simp
-/
lemma commute_id_right : Commute f LinearMap.id := by ext; simp

end Module.End
