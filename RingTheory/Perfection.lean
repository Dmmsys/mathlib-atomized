/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Pi
public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.Algebra.CharP.Subring
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Valuation.Integers

/-!
# Ring Perfection and Tilt

In this file we define the perfection of a ring of characteristic p, and the tilt of a field
given a valuation to `ℝ≥0`.

## TODO

Define the valuation on the tilt, and define a characteristic predicate for the tilt.

-/

@[expose] public section


universe u₁ u₂ u₃ u₄

open scoped NNReal

/--
Definition of `Perfection` / `Perfection` 的定义

English:
definition Perfection
  signature: (α : Type u₁) [Pow α Nat] (p : Nat)
  body: { f : Nat -> α // forall n, f (n + 1) ^ p = f n }

@[deprecated (since := "2026-03-03")] alias Ring.Perfection := Perfection

中文:
定义 Perfection
  签名: (α : 类型u₁) [幂 α 自然数] (p : 自然数)
  定义体: { f : Nat -> α // forall n, f (n + 1) ^ p = f n }

@[deprecated (since := "2026-03-03")] alias Ring.Perfection := Perfection
-/
def Perfection (α : Type u₁) [Pow α Nat] (p : Nat) : Type u₁ :=
  { f : Nat -> α // forall n, f (n + 1) ^ p = f n }

@[deprecated (since := "2026-03-03")] alias Ring.Perfection := Perfection

namespace Perfection

section CommMonoid

/--
Definition of `submonoid` / `submonoid` 的定义

English:
definition submonoid
  signature: (M : Type*) [CommMonoid M] (p : Nat)
  body: { f | forall n, f (n + 1) ^ p = f n }
  one_mem' _ := one_pow _
  mul_mem' hf hg n := (mul_pow _ _ _).trans congr($(hf n) * $(hg n))

@[deprecated (since := "2026-03-03")]
alias _root_.Monoid.perfection := submonoid

中文:
定义 submonoid
  签名: (M : 类型) [交换幺半群 M] (p : 自然数)
  定义体: { f | forall n, f (n + 1) ^ p = f n }
  one_mem' _ := one_pow _
  mul_mem' hf hg n := (mul_pow _ _ _).trans congr($(hf n) * $(hg n))

@[deprecated (since := "2026-03-03")]
alias _root_.Monoid.perfection := submonoid
-/
def submonoid (M : Type*) [CommMonoid M] (p : Nat) : Submonoid (Nat -> M) where
  carrier := { f | forall n, f (n + 1) ^ p = f n }
  one_mem' _ := one_pow _
  mul_mem' hf hg n := (mul_pow _ _ _).trans congr($(hf n) * $(hg n))

@[deprecated (since := "2026-03-03")]
alias _root_.Monoid.perfection := submonoid

instance (M : Type*) [CommMonoid M] (p : Nat) : CommMonoid (Perfection M p) :=
inferInstanceAs CommMonoid (submonoid M p)

variable (M : Type*) [CommMonoid M] (p : Nat)

/--
Definition of `coeffMonoidHom` / `coeffMonoidHom` 的定义

English:
definition coeffMonoidHom
  signature: (n : Nat)
  body: f.1 n
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 coeffMonoidHom
  签名: (n : 自然数)
  定义体: f.1 n
  map_one' := rfl
  map_mul' _ _ := rfl
-/
def coeffMonoidHom (n : Nat) : Perfection M p ->* M where
  toFun f := f.1 n
  map_one' := rfl
  map_mul' _ _ := rfl

/--
Definition of `pthRootMonoidHom` / `pthRootMonoidHom` 的定义

English:
definition pthRootMonoidHom
  signature: : Perfection M p ->* Perfection M p where
  body: ⟨fun n => coeffMonoidHom M p (n + 1) f, fun _ => f.2 _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 pthRootMonoidHom
  签名: : Perfection M p ->* Perfection M p where
  定义体: ⟨fun n => coeffMonoidHom M p (n + 1) f, fun _ => f.2 _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: coeffMonoidHom
-/
def pthRootMonoidHom : Perfection M p ->* Perfection M p where
  toFun f := ⟨fun n => coeffMonoidHom M p (n + 1) f, fun _ => f.2 _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {M p}

-- To prioritize `Perfection.ext` for the ring case.
@[ext low]
/--
theorem `extMonoid` / 定理 `extMonoid`

English:
theorem extMonoid
  statement: {f g : Perfection M p}
  proof: Subtype.ext funext h

@[simp]

中文:
定理 extMonoid
  结论: {f g : Perfection M p}
  证明: Subtype.ext funext h

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem extMonoid {f g : Perfection M p}
    (h : forall n, coeffMonoidHom M p n f = coeffMonoidHom M p n g) :
    f = g :=
Subtype.ext funext h

@[simp]
/--
theorem `coeffMonoidHom_mk` / 定理 `coeffMonoidHom_mk`

English:
theorem coeffMonoidHom_mk
  given: (f : Nat -> M) (hf) (n : Nat)
  statement: coeffMonoidHom M p n ⟨f, hf⟩ = f n
  proof: rfl

中文:
定理 coeffMonoidHom_mk
  条件: (f : 自然数 -> M) (hf) (n : 自然数)
  结论: coeffMonoidHom M p n ⟨f, hf⟩ = f n
  证明: rfl
-/
theorem coeffMonoidHom_mk (f : Nat -> M) (hf) (n : Nat) : coeffMonoidHom M p n ⟨f, hf⟩ = f n := rfl

/--
theorem `coeffMonoidHom_pthRootMonoidHom` / 定理 `coeffMonoidHom_pthRootMonoidHom`

English:
theorem coeffMonoidHom_pthRootMonoidHom
  given: (f : Perfection M p) (n : Nat)
  proof: rfl

中文:
定理 coeffMonoidHom_pthRootMonoidHom
  条件: (f : Perfection M p) (n : 自然数)
  证明: rfl
-/
theorem coeffMonoidHom_pthRootMonoidHom (f : Perfection M p) (n : Nat) :
    coeffMonoidHom M p n (pthRootMonoidHom M p f) = coeffMonoidHom M p (n + 1) f := rfl
attribute [local simp] coeffMonoidHom_pthRootMonoidHom

/--
theorem `coeffMonoidHom_pow_p` / 定理 `coeffMonoidHom_pow_p`

English:
theorem coeffMonoidHom_pow_p
  given: (f : Perfection M p) (n : Nat)
  proof: by
  rw [map_pow]; exact f.2 n

@[simp]

中文:
定理 coeffMonoidHom_pow_p
  条件: (f : Perfection M p) (n : 自然数)
  证明: by
  rw [map_pow]; exact f.2 n

@[simp]

Depends on / 依赖: map_pow
-/
theorem coeffMonoidHom_pow_p (f : Perfection M p) (n : Nat) :
    coeffMonoidHom M p (n + 1) (f ^ p) = coeffMonoidHom M p n f := by
  rw [map_pow]; exact f.2 n

@[simp]
/--
theorem `coeffMonoidHom_pow_p'` / 定理 `coeffMonoidHom_pow_p'`

English:
theorem coeffMonoidHom_pow_p'
  given: (f : Perfection M p) (n : Nat)
  proof: f.2 n

中文:
定理 coeffMonoidHom_pow_p'
  条件: (f : Perfection M p) (n : 自然数)
  证明: f.2 n
-/
theorem coeffMonoidHom_pow_p' (f : Perfection M p) (n : Nat) :
    coeffMonoidHom M p (n + 1) f ^ p = coeffMonoidHom M p n f :=
  f.2 n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PerfectRing (Perfection M p) p
  body: Function.bijective_iff_has_inverse.mpr
    ⟨pthRootMonoidHom M p, fun x => by ext; simp, fun x => by ext; simp⟩

@[simp]

中文:
实例 :
  签名: 完美环 (Perfection M p) p
  定义体: Function.bijective_iff_has_inverse.mpr
    ⟨pthRootMonoidHom M p, fun x => by ext; simp, fun x => by ext; simp⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse
-/
instance : PerfectRing (Perfection M p) p where
  bijective_frobenius := Function.bijective_iff_has_inverse.mpr
    ⟨pthRootMonoidHom M p, fun x => by ext; simp, fun x => by ext; simp⟩

@[simp]
/--
theorem `pthRootMonoidHom_eq_powMulEquiv_symm` / 定理 `pthRootMonoidHom_eq_powMulEquiv_symm`

English:
theorem pthRootMonoidHom_eq_powMulEquiv_symm
  proof: MonoidHom.ext fun x => (MulEquiv.eq_symm_apply _).mpr by ext; simp

中文:
定理 pthRootMonoidHom_eq_powMulEquiv_symm
  证明: MonoidHom.ext fun x => (MulEquiv.eq_symm_apply _).mpr by ext; simp

Depends on / 依赖: MonoidHom, MonoidHom.ext, MulEquiv, MulEquiv.eq_symm_apply, eq_symm_apply
-/
theorem pthRootMonoidHom_eq_powMulEquiv_symm :
    pthRootMonoidHom M p = (powMulEquiv (Perfection M p) p).symm :=
MonoidHom.ext fun x => (MulEquiv.eq_symm_apply _).mpr by ext; simp

/--
theorem `coe_pthRootMonoidHom_eq_powMulEquiv_symm` / 定理 `coe_pthRootMonoidHom_eq_powMulEquiv_symm`

English:
theorem coe_pthRootMonoidHom_eq_powMulEquiv_symm
  proof: congr($pthRootMonoidHom_eq_powMulEquiv_symm)

中文:
定理 coe_pthRootMonoidHom_eq_powMulEquiv_symm
  证明: congr($pthRootMonoidHom_eq_powMulEquiv_symm)

Depends on / 依赖: pthRootMonoidHom_eq_powMulEquiv_symm
-/
theorem coe_pthRootMonoidHom_eq_powMulEquiv_symm :
    ⇑(pthRootMonoidHom M p) = (powMulEquiv (Perfection M p) p).symm :=
  congr($pthRootMonoidHom_eq_powMulEquiv_symm)

/--
theorem `coeffMonoidHom_symm_powMulEquiv` / 定理 `coeffMonoidHom_symm_powMulEquiv`

English:
theorem coeffMonoidHom_symm_powMulEquiv
  given: (f : Perfection M p) (n : Nat)
  proof: by
  rw [← coe_pthRootMonoidHom_eq_powMulEquiv_symm]; rfl

中文:
定理 coeffMonoidHom_symm_powMulEquiv
  条件: (f : Perfection M p) (n : 自然数)
  证明: by
  rw [← coe_pthRootMonoidHom_eq_powMulEquiv_symm]; rfl
-/
@[simp] theorem coeffMonoidHom_symm_powMulEquiv (f : Perfection M p) (n : Nat) :
    coeffMonoidHom M p n ((powMulEquiv _ p).symm f) = coeffMonoidHom M p (n + 1) f := by
  rw [← coe_pthRootMonoidHom_eq_powMulEquiv_symm]; rfl

/--
theorem `coeffMonoidHom_iterate_symm_powMulEquiv` / 定理 `coeffMonoidHom_iterate_symm_powMulEquiv`

English:
theorem coeffMonoidHom_iterate_symm_powMulEquiv
  given: (f : Perfection M p) (n m : Nat)
  proof: by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']; rw [coeffMonoidHom_symm_powMulEquiv]; rw [ih]
    grind

中文:
定理 coeffMonoidHom_iterate_symm_powMulEquiv
  条件: (f : Perfection M p) (n m : 自然数)
  证明: by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']; rw [coeffMonoidHom_symm_powMulEquiv]; rw [ih]
    grind
-/
@[simp] theorem coeffMonoidHom_iterate_symm_powMulEquiv (f : Perfection M p) (n m : Nat) :
    coeffMonoidHom M p n ((powMulEquiv _ p).symm^[m] f) = coeffMonoidHom M p (n + m) f := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']; rw [coeffMonoidHom_symm_powMulEquiv]; rw [ih]
    grind

/--
theorem `coeffMonoidHom_pow_p_pow` / 定理 `coeffMonoidHom_pow_p_pow`

English:
theorem coeffMonoidHom_pow_p_pow
  given: (f : Perfection M p) (m n : Nat)
  proof: n.recOn (by simp) fun n ih => by rw [pow_succ, pow_mul, Nat.add_succ, coeffMonoidHom_pow_p, ih]

@[simp]

中文:
定理 coeffMonoidHom_pow_p_pow
  条件: (f : Perfection M p) (m n : 自然数)
  证明: n.recOn (by simp) fun n ih => by rw [pow_succ, pow_mul, Nat.add_succ, coeffMonoidHom_pow_p, ih]

@[simp]

Depends on / 依赖: Nat.add_succ, add_succ, coeffMonoidHom_pow_p, n.recOn, pow_mul, pow_succ
-/
theorem coeffMonoidHom_pow_p_pow (f : Perfection M p) (m n : Nat) :
    coeffMonoidHom M p (m + n) (f ^ p ^ n) = coeffMonoidHom M p m f :=
  n.recOn (by simp) fun n ih => by rw [pow_succ, pow_mul, Nat.add_succ, coeffMonoidHom_pow_p, ih]

@[simp]
/--
theorem `coeffMonoidHom_pow_p_pow'` / 定理 `coeffMonoidHom_pow_p_pow'`

English:
theorem coeffMonoidHom_pow_p_pow'
  given: (f : Perfection M p) (m n : Nat)
  proof: by
  rw [← map_pow]; rw [coeffMonoidHom_pow_p_pow]

@[simp]

中文:
定理 coeffMonoidHom_pow_p_pow'
  条件: (f : Perfection M p) (m n : 自然数)
  证明: by
  rw [← map_pow]; rw [coeffMonoidHom_pow_p_pow]

@[simp]

Depends on / 依赖: coeffMonoidHom_pow_p_pow, map_pow
-/
theorem coeffMonoidHom_pow_p_pow' (f : Perfection M p) (m n : Nat) :
    coeffMonoidHom M p (m + n) f ^ p ^ n = coeffMonoidHom M p m f := by
  rw [← map_pow]; rw [coeffMonoidHom_pow_p_pow]

@[simp]
/--
theorem `coeffMonoidHom_pow_p_pow_self` / 定理 `coeffMonoidHom_pow_p_pow_self`

English:
theorem coeffMonoidHom_pow_p_pow_self
  given: (f : Perfection M p) (n : Nat)
  proof: by
  rw [← coeffMonoidHom_pow_p_pow' _ 0 n]; rw [zero_add]

中文:
定理 coeffMonoidHom_pow_p_pow_self
  条件: (f : Perfection M p) (n : 自然数)
  证明: by
  rw [← coeffMonoidHom_pow_p_pow' _ 0 n]; rw [zero_add]

Depends on / 依赖: coeffMonoidHom_pow_p_pow, zero_add
-/
theorem coeffMonoidHom_pow_p_pow_self (f : Perfection M p) (n : Nat) :
    coeffMonoidHom M p n f ^ p ^ n = coeffMonoidHom M p 0 f := by
  rw [← coeffMonoidHom_pow_p_pow' _ 0 n]; rw [zero_add]

/--
theorem `coeffMonoidHom_powMonoidHom` / 定理 `coeffMonoidHom_powMonoidHom`

English:
theorem coeffMonoidHom_powMonoidHom
  given: (f : Perfection M p) (n : Nat)
  proof: coeffMonoidHom_pow_p f n

中文:
定理 coeffMonoidHom_powMonoidHom
  条件: (f : Perfection M p) (n : 自然数)
  证明: coeffMonoidHom_pow_p f n

Depends on / 依赖: coeffMonoidHom_pow_p
-/
theorem coeffMonoidHom_powMonoidHom (f : Perfection M p) (n : Nat) :
    coeffMonoidHom M p (n + 1) (powMonoidHom p f) = coeffMonoidHom M p n f :=
  coeffMonoidHom_pow_p f n

/--
theorem `coeffMonoidHom_iterate_powMonoidHom` / 定理 `coeffMonoidHom_iterate_powMonoidHom`

English:
theorem coeffMonoidHom_iterate_powMonoidHom
  given: (f : Perfection M p) (n m : Nat)
  proof: m.recOn rfl fun m ih => by
    rw [Function.iterate_succ_apply']; rw [Nat.add_succ]; rw [coeffMonoidHom_powMonoidHom]; rw [ih]

中文:
定理 coeffMonoidHom_iterate_powMonoidHom
  条件: (f : Perfection M p) (n m : 自然数)
  证明: m.recOn rfl fun m ih => by
    rw [Function.iterate_succ_apply']; rw [Nat.add_succ]; rw [coeffMonoidHom_powMonoidHom]; rw [ih]

Depends on / 依赖: Function, Function.iterate_succ_apply, Nat.add_succ, add_succ, coeffMonoidHom_powMonoidHom, iterate_succ_apply, m.recOn
-/
theorem coeffMonoidHom_iterate_powMonoidHom (f : Perfection M p) (n m : Nat) :
    coeffMonoidHom M p (n + m) ((powMonoidHom p)^[m] f) = coeffMonoidHom M p n f :=
  m.recOn rfl fun m ih => by
    rw [Function.iterate_succ_apply']; rw [Nat.add_succ]; rw [coeffMonoidHom_powMonoidHom]; rw [ih]

/--
theorem `coeffMonoidHom_iterate_powMonoidHom'` / 定理 `coeffMonoidHom_iterate_powMonoidHom'`

English:
theorem coeffMonoidHom_iterate_powMonoidHom'
  given: (f : Perfection M p) (n m : Nat) (hmn : m <= n)
  proof: by
  rw [← coeffMonoidHom_iterate_powMonoidHom f (n - m) m]; rw [Nat.sub_add_cancel hmn]

中文:
定理 coeffMonoidHom_iterate_powMonoidHom'
  条件: (f : Perfection M p) (n m : 自然数) (hmn : m <= n)
  证明: by
  rw [← coeffMonoidHom_iterate_powMonoidHom f (n - m) m]; rw [Nat.sub_add_cancel hmn]

Depends on / 依赖: Nat.sub_add_cancel, coeffMonoidHom_iterate_powMonoidHom, sub_add_cancel
-/
theorem coeffMonoidHom_iterate_powMonoidHom' (f : Perfection M p) (n m : Nat) (hmn : m <= n) :
    coeffMonoidHom M p n ((powMonoidHom p)^[m] f) = coeffMonoidHom M p (n - m) f := by
  rw [← coeffMonoidHom_iterate_powMonoidHom f (n - m) m]; rw [Nat.sub_add_cancel hmn]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given monoids `M` and `N`, with `M` being perfect,
any homomorphism `M →+* N` can be lifted uniquely to a homomorphism `M →* Perfection N p`. -/
@[simps! symm_apply]
/--
Definition of `liftMonoidHom` / `liftMonoidHom` 的定义

English:
definition liftMonoidHom
  signature: (p : Nat) (M : Type*) [CommMonoid M] [PerfectRing M p]
  body: { toFun r := ⟨fun n => f ((powMulEquiv M (p ^ n)).symm r), fun n => by
        rw [← map_pow]; rw [powMulEquiv_pow]; rw [pow_succ]; rw [MulAut.mul_def]; rw [MulEquiv.symm_trans_apply]; rw [powMulEquiv_symm_pow_p]; rw [← powMulEquiv_pow]⟩
      map_one' := extMonoid fun _ => by simp_rw [coeffMonoidHo

中文:
定义 liftMonoidHom
  签名: (p : 自然数) (M : 类型) [交换幺半群 M] [完美环 M p]
  定义体: { toFun r := ⟨fun n => f ((powMulEquiv M (p ^ n)).symm r), fun n => by
        rw [← map_pow]; rw [powMulEquiv_pow]; rw [pow_succ]; rw [MulAut.mul_def]; rw [MulEquiv.symm_trans_apply]; rw [powMulEquiv_symm_pow_p]; rw [← powMulEquiv_pow]⟩
      map_one' := extMonoid fun _ => by simp_rw [coeffMonoidHo

Depends on / 依赖: MonoidHom, MonoidHom.coe_comp, MulAut, MulAut.mul_def, MulEquiv, MulEquiv.symm_trans_apply, coe_comp, coeffMonoidHom, coeffMonoidHom_mk, extMonoid, invFun, left_inv, map_mul, map_one, map_pow, mul_def, powMulEquiv, powMulEquiv_pow, powMulEquiv_symm_pow_p, pow_succ
-/
noncomputable def liftMonoidHom (p : Nat) (M : Type*) [CommMonoid M] [PerfectRing M p]
    (N : Type*) [CommMonoid N] : (M ->* N) ≃* (M ->* Perfection N p) where
  toFun f :=
    { toFun r := ⟨fun n => f ((powMulEquiv M (p ^ n)).symm r), fun n => by
        rw [← map_pow]; rw [powMulEquiv_pow]; rw [pow_succ]; rw [MulAut.mul_def]; rw [MulEquiv.symm_trans_apply]; rw [powMulEquiv_symm_pow_p]; rw [← powMulEquiv_pow]⟩
      map_one' := extMonoid fun _ => by simp_rw [coeffMonoidHom_mk, map_one]
      map_mul' x y := extMonoid fun _ => by simp_rw [map_mul, coeffMonoidHom_mk] }
  invFun := (coeffMonoidHom N p 0).comp
  left_inv f := by ext; simp
  right_inv f := by
    ext m n
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      coeffMonoidHom_mk]
    rw [← coeffMonoidHom_pow_p_pow _ 0 n]; rw [← map_pow]; rw [powMulEquiv_symm_pow_p]; rw [zero_add]
  map_mul' _ _ := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `coeffMonoidHom_zero_liftMonoidHom` / 引理 `coeffMonoidHom_zero_liftMonoidHom`

English:
lemma coeffMonoidHom_zero_liftMonoidHom
  proof: by simp [liftMonoidHom]

中文:
引理 coeffMonoidHom_zero_liftMonoidHom
  证明: by simp [liftMonoidHom]
-/
@[simp] lemma coeffMonoidHom_zero_liftMonoidHom
    (p : Nat) {M N : Type*} [CommMonoid M] [PerfectRing M p] [CommMonoid N] (e : M ->* N) (x : M) :
    coeffMonoidHom N p 0 (liftMonoidHom p M N e x) = e x := by simp [liftMonoidHom]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mapMonoidHom` / `mapMonoidHom` 的定义

English:
definition mapMonoidHom
  signature: (p : Nat) {M N : Type*} [CommMonoid M] [CommMonoid N] (φ : M ->* N)
  body: ⟨fun n => φ (f.coeffMonoidHom M p n), fun n => by rw [← map_pow, coeffMonoidHom_pow_p']⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]

中文:
定义 mapMonoidHom
  签名: (p : 自然数) {M N : 类型} [交换幺半群 M] [交换幺半群 N] (φ : M ->* N)
  定义体: ⟨fun n => φ (f.coeffMonoidHom M p n), fun n => by rw [← map_pow, coeffMonoidHom_pow_p']⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]

Depends on / 依赖: coeffMonoidHom, coeffMonoidHom_pow_p, f.coeffMonoidHom, map_pow
-/
def mapMonoidHom (p : Nat) {M N : Type*} [CommMonoid M] [CommMonoid N] (φ : M ->* N) :
    Perfection M p ->* Perfection N p where
  toFun f := ⟨fun n => φ (f.coeffMonoidHom M p n), fun n => by rw [← map_pow, coeffMonoidHom_pow_p']⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]
/--
theorem `coeffMonoidHom_mapMonoidHom` / 定理 `coeffMonoidHom_mapMonoidHom`

English:
theorem coeffMonoidHom_mapMonoidHom
  statement: (p : Nat) {M N : Type*} [CommMonoid M] [CommMonoid N]
  proof: rfl

中文:
定理 coeffMonoidHom_mapMonoidHom
  结论: (p : 自然数) {M N : 类型} [交换幺半群 M] [交换幺半群 N]
  证明: rfl
-/
theorem coeffMonoidHom_mapMonoidHom (p : Nat) {M N : Type*} [CommMonoid M] [CommMonoid N]
    (φ : M ->* N) (f : Perfection M p) (n : Nat) :
    coeffMonoidHom N p n (mapMonoidHom p φ f) = φ (coeffMonoidHom M p n f) := rfl

end CommMonoid

section CommSemiring

/--
Definition of `subsemiring` / `subsemiring` 的定义

English:
definition subsemiring
  signature: (R : Type*) [CommSemiring R] (p : Nat) [hp : Fact p.Prime] [CharP R p]
  body: submonoid R p
  zero_mem' _ := zero_pow hp.1.ne_zero
  add_mem' hf hg n := (map_add (frobenius R p) _ _).trans congr($(hf n) + $(hg n))

@[deprecated (since := "2026-03-03")]
alias _root_.Ring.perfectionSubsemiring := subsemiring

中文:
定义 subsemiring
  签名: (R : 类型) [交换半环 R] (p : 自然数) [hp : Fact p.素] [特征p R p]
  定义体: submonoid R p
  zero_mem' _ := zero_pow hp.1.ne_zero
  add_mem' hf hg n := (map_add (frobenius R p) _ _).trans congr($(hf n) + $(hg n))

@[deprecated (since := "2026-03-03")]
alias _root_.Ring.perfectionSubsemiring := subsemiring

Depends on / 依赖: submonoid
-/
def subsemiring (R : Type*) [CommSemiring R] (p : Nat) [hp : Fact p.Prime] [CharP R p] :
    Subsemiring (Nat -> R) where
  __ := submonoid R p
  zero_mem' _ := zero_pow hp.1.ne_zero
  add_mem' hf hg n := (map_add (frobenius R p) _ _).trans congr($(hf n) + $(hg n))

@[deprecated (since := "2026-03-03")]
alias _root_.Ring.perfectionSubsemiring := subsemiring

variable (R : Type*) [CommSemiring R] (p : Nat) [hp : Fact p.Prime] [CharP R p]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring (Perfection R p)
  body: inferInstanceAs CommSemiring (subsemiring R p)

中文:
实例 :
  签名: 交换半环 (Perfection R p)
  定义体: inferInstanceAs CommSemiring (subsemiring R p)

Depends on / 依赖: CommSemiring, subsemiring
-/
instance : CommSemiring (Perfection R p) :=
inferInstanceAs CommSemiring (subsemiring R p)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CharP (Perfection R p) p
  body: CharP.subsemiring _ _ (subsemiring R p)

中文:
实例 :
  签名: 特征p (Perfection R p) p
  定义体: CharP.subsemiring _ _ (subsemiring R p)

Depends on / 依赖: CharP.subsemiring, subsemiring
-/
instance : CharP (Perfection R p) p :=
  CharP.subsemiring _ _ (subsemiring R p)

/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (n : Nat)
  body: coeffMonoidHom R p n
  map_zero' := rfl
  map_add' _ _ := rfl

中文:
定义 coeff
  签名: (n : 自然数)
  定义体: coeffMonoidHom R p n
  map_zero' := rfl
  map_add' _ _ := rfl

Depends on / 依赖: coeffMonoidHom
-/
def coeff (n : Nat) : Perfection R p ->+* R where
  __ := coeffMonoidHom R p n
  map_zero' := rfl
  map_add' _ _ := rfl

/--
Definition of `pthRoot` / `pthRoot` 的定义

English:
definition pthRoot
  signature: : Perfection R p ->+* Perfection R p where
  body: pthRootMonoidHom R p
  map_zero' := rfl
  map_add' _ _ := rfl

中文:
定义 pthRoot
  签名: : Perfection R p ->+* Perfection R p where
  定义体: pthRootMonoidHom R p
  map_zero' := rfl
  map_add' _ _ := rfl

Depends on / 依赖: pthRootMonoidHom
-/
def pthRoot : Perfection R p ->+* Perfection R p where
  __ := pthRootMonoidHom R p
  map_zero' := rfl
  map_add' _ _ := rfl

variable {R p}

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : Perfection R p} (h : forall n, coeff R p n f = coeff R p n g)
  statement: f = g
  proof: extMonoid h

中文:
定理 ext
  条件: {f g : Perfection R p} (h : 对任意 n, coeff R p n f = coeff R p n g)
  结论: f = g
  证明: extMonoid h

Depends on / 依赖: extMonoid
-/
theorem ext {f g : Perfection R p} (h : forall n, coeff R p n f = coeff R p n g) : f = g :=
  extMonoid h

/--
lemma `pthRoot_eq_symm_frobeniusEquiv` / 引理 `pthRoot_eq_symm_frobeniusEquiv`

English:
lemma pthRoot_eq_symm_frobeniusEquiv
  proof: by
  ext : 1
simpa [RingEquiv.eq_symm_apply] using ext coeffMonoidHom_pow_p' _

中文:
引理 pthRoot_eq_symm_frobeniusEquiv
  证明: by
  ext : 1
simpa [RingEquiv.eq_symm_apply] using ext coeffMonoidHom_pow_p' _
-/
@[simp] lemma pthRoot_eq_symm_frobeniusEquiv :
    pthRoot R p = RingHomClass.toRingHom (frobeniusEquiv _ p).symm := by
  ext : 1
simpa [RingEquiv.eq_symm_apply] using ext coeffMonoidHom_pow_p' _

/--
lemma `coe_pthRoot_eq_symm_frobeniusEquiv` / 引理 `coe_pthRoot_eq_symm_frobeniusEquiv`

English:
lemma coe_pthRoot_eq_symm_frobeniusEquiv
  statement: ⇑(pthRoot R p) = (frobeniusEquiv _ p).symm
  proof: congr($pthRoot_eq_symm_frobeniusEquiv)

中文:
引理 coe_pthRoot_eq_symm_frobeniusEquiv
  结论: ⇑(pthRoot R p) = (frobeniusEquiv _ p).symm
  证明: congr($pthRoot_eq_symm_frobeniusEquiv)

Depends on / 依赖: pthRoot_eq_symm_frobeniusEquiv
-/
lemma coe_pthRoot_eq_symm_frobeniusEquiv : ⇑(pthRoot R p) = (frobeniusEquiv _ p).symm :=
  congr($pthRoot_eq_symm_frobeniusEquiv)

/--
lemma `coeffMonoidHom_eq_coeff` / 引理 `coeffMonoidHom_eq_coeff`

English:
lemma coeffMonoidHom_eq_coeff
  given: (n : Nat)
  statement: ⇑(coeffMonoidHom R p n) = coeff R p n
  proof: rfl

中文:
引理 coeffMonoidHom_eq_coeff
  条件: (n : 自然数)
  结论: ⇑(coeffMonoidHom R p n) = coeff R p n
  证明: rfl
-/
@[simp] lemma coeffMonoidHom_eq_coeff (n : Nat) : ⇑(coeffMonoidHom R p n) = coeff R p n := rfl

/--
lemma `pthRootMonoidHom_eq_pthRoot` / 引理 `pthRootMonoidHom_eq_pthRoot`

English:
lemma pthRootMonoidHom_eq_pthRoot
  statement: ⇑(pthRootMonoidHom R p) = pthRoot R p
  proof: rfl

中文:
引理 pthRootMonoidHom_eq_pthRoot
  结论: ⇑(pthRootMonoidHom R p) = pthRoot R p
  证明: rfl
-/
lemma pthRootMonoidHom_eq_pthRoot : ⇑(pthRootMonoidHom R p) = pthRoot R p := rfl

/--
lemma `pthRootMonoidHom_eq_symm_frobeniusEquiv` / 引理 `pthRootMonoidHom_eq_symm_frobeniusEquiv`

English:
lemma pthRootMonoidHom_eq_symm_frobeniusEquiv
  proof: by
  simp

中文:
引理 pthRootMonoidHom_eq_symm_frobeniusEquiv
  证明: by
  simp
-/
lemma pthRootMonoidHom_eq_symm_frobeniusEquiv :
    ⇑(pthRootMonoidHom R p) = RingHomClass.toRingHom (frobeniusEquiv _ p).symm := by
  simp

/--
lemma `coeff_toMonoidHom` / 引理 `coeff_toMonoidHom`

English:
lemma coeff_toMonoidHom
  given: (n : Nat)
  statement: (coeff R p n).toMonoidHom = coeffMonoidHom R p n
  proof: rfl

@[simp]

中文:
引理 coeff_toMonoidHom
  条件: (n : 自然数)
  结论: (coeff R p n).toMonoidHom = coeffMonoidHom R p n
  证明: rfl

@[simp]
-/
lemma coeff_toMonoidHom (n : Nat) : (coeff R p n).toMonoidHom = coeffMonoidHom R p n := rfl

@[simp]
/--
theorem `coeff_mk` / 定理 `coeff_mk`

English:
theorem coeff_mk
  given: (f : Nat -> R) (hf) (n : Nat)
  statement: coeff R p n ⟨f, hf⟩ = f n
  proof: rfl

@[simp]

中文:
定理 coeff_mk
  条件: (f : 自然数 -> R) (hf) (n : 自然数)
  结论: coeff R p n ⟨f, hf⟩ = f n
  证明: rfl

@[simp]
-/
theorem coeff_mk (f : Nat -> R) (hf) (n : Nat) : coeff R p n ⟨f, hf⟩ = f n := rfl

@[simp]
/--
theorem `coeff_symm_frobeniusEquiv` / 定理 `coeff_symm_frobeniusEquiv`

English:
theorem coeff_symm_frobeniusEquiv
  given: (f : Perfection R p) (n : Nat)
  proof: coeffMonoidHom_symm_powMulEquiv ..

@[simp]

中文:
定理 coeff_symm_frobeniusEquiv
  条件: (f : Perfection R p) (n : 自然数)
  证明: coeffMonoidHom_symm_powMulEquiv ..

@[simp]

Depends on / 依赖: coeffMonoidHom_symm_powMulEquiv
-/
theorem coeff_symm_frobeniusEquiv (f : Perfection R p) (n : Nat) :
    coeff R p n ((frobeniusEquiv _ p).symm f) = coeff R p (n + 1) f :=
  coeffMonoidHom_symm_powMulEquiv ..

@[simp]
/--
theorem `coeff_iterate_symm_frobeniusEquiv` / 定理 `coeff_iterate_symm_frobeniusEquiv`

English:
theorem coeff_iterate_symm_frobeniusEquiv
  given: (f : Perfection R p) (n m : Nat)
  proof: coeffMonoidHom_iterate_symm_powMulEquiv ..

中文:
定理 coeff_iterate_symm_frobeniusEquiv
  条件: (f : Perfection R p) (n m : 自然数)
  证明: coeffMonoidHom_iterate_symm_powMulEquiv ..

Depends on / 依赖: coeffMonoidHom_iterate_symm_powMulEquiv
-/
theorem coeff_iterate_symm_frobeniusEquiv (f : Perfection R p) (n m : Nat) :
    coeff R p n ((frobeniusEquiv _ p).symm^[m] f) = coeff R p (n + m) f :=
  coeffMonoidHom_iterate_symm_powMulEquiv ..

/--
theorem `coeff_pow_p` / 定理 `coeff_pow_p`

English:
theorem coeff_pow_p
  given: (f : Perfection R p) (n : Nat)
  proof: coeffMonoidHom_pow_p f n

@[simp]

中文:
定理 coeff_pow_p
  条件: (f : Perfection R p) (n : 自然数)
  证明: coeffMonoidHom_pow_p f n

@[simp]

Depends on / 依赖: coeffMonoidHom_pow_p
-/
theorem coeff_pow_p (f : Perfection R p) (n : Nat) :
    coeff R p (n + 1) (f ^ p) = coeff R p n f := coeffMonoidHom_pow_p f n

@[simp]
/--
theorem `coeff_pow_p'` / 定理 `coeff_pow_p'`

English:
theorem coeff_pow_p'
  given: (f : Perfection R p) (n : Nat)
  statement: coeff R p (n + 1) f ^ p = coeff R p n f
  proof: f.2 n

@[simp]

中文:
定理 coeff_pow_p'
  条件: (f : Perfection R p) (n : 自然数)
  结论: coeff R p (n + 1) f ^ p = coeff R p n f
  证明: f.2 n

@[simp]
-/
theorem coeff_pow_p' (f : Perfection R p) (n : Nat) : coeff R p (n + 1) f ^ p = coeff R p n f :=
  f.2 n

@[simp]
/--
theorem `coeff_frobenius` / 定理 `coeff_frobenius`

English:
theorem coeff_frobenius
  given: (f : Perfection R p) (n : Nat)
  proof: coeffMonoidHom_powMonoidHom f n

@[simp]

中文:
定理 coeff_frobenius
  条件: (f : Perfection R p) (n : 自然数)
  证明: coeffMonoidHom_powMonoidHom f n

@[simp]

Depends on / 依赖: coeffMonoidHom_powMonoidHom
-/
theorem coeff_frobenius (f : Perfection R p) (n : Nat) :
    coeff R p (n + 1) (frobenius _ p f) = coeff R p n f := coeffMonoidHom_powMonoidHom f n

@[simp]
/--
theorem `coeff_iterate_frobenius` / 定理 `coeff_iterate_frobenius`

English:
theorem coeff_iterate_frobenius
  given: (f : Perfection R p) (n m : Nat)
  proof: coeffMonoidHom_iterate_powMonoidHom ..

中文:
定理 coeff_iterate_frobenius
  条件: (f : Perfection R p) (n m : 自然数)
  证明: coeffMonoidHom_iterate_powMonoidHom ..

Depends on / 依赖: coeffMonoidHom_iterate_powMonoidHom
-/
theorem coeff_iterate_frobenius (f : Perfection R p) (n m : Nat) :
    coeff R p (n + m) ((frobenius _ p)^[m] f) = coeff R p n f :=
  coeffMonoidHom_iterate_powMonoidHom ..

/--
theorem `coeff_iterate_frobenius'` / 定理 `coeff_iterate_frobenius'`

English:
theorem coeff_iterate_frobenius'
  given: (f : Perfection R p) (n m : Nat) (hmn : m <= n)
  proof: coeffMonoidHom_iterate_powMonoidHom' _ _ _ hmn

中文:
定理 coeff_iterate_frobenius'
  条件: (f : Perfection R p) (n m : 自然数) (hmn : m <= n)
  证明: coeffMonoidHom_iterate_powMonoidHom' _ _ _ hmn

Depends on / 依赖: coeffMonoidHom_iterate_powMonoidHom
-/
theorem coeff_iterate_frobenius' (f : Perfection R p) (n m : Nat) (hmn : m <= n) :
    coeff R p n ((frobenius _ p)^[m] f) = coeff R p (n - m) f :=
  coeffMonoidHom_iterate_powMonoidHom' _ _ _ hmn

/--
theorem `pthRoot_frobenius` / 定理 `pthRoot_frobenius`

English:
theorem pthRoot_frobenius
  statement: (pthRoot R p).comp (frobenius _ p) = RingHom.id _
  proof: by
  ext; simp

中文:
定理 pthRoot_frobenius
  结论: (pthRoot R p).comp (frobenius _ p) = 环态射.id _
  证明: by
  ext; simp
-/
theorem pthRoot_frobenius : (pthRoot R p).comp (frobenius _ p) = RingHom.id _ := by
  ext; simp

/--
theorem `frobenius_pthRoot` / 定理 `frobenius_pthRoot`

English:
theorem frobenius_pthRoot
  statement: (frobenius _ p).comp (pthRoot R p) = RingHom.id _
  proof: pthRoot_frobenius

中文:
定理 frobenius_pthRoot
  结论: (frobenius _ p).comp (pthRoot R p) = 环态射.id _
  证明: pthRoot_frobenius

Depends on / 依赖: pthRoot_frobenius
-/
theorem frobenius_pthRoot : (frobenius _ p).comp (pthRoot R p) = RingHom.id _ := pthRoot_frobenius

/--
theorem `coeff_add_ne_zero` / 定理 `coeff_add_ne_zero`

English:
theorem coeff_add_ne_zero
  given: {f : Perfection R p} {n : Nat} (hfn : coeff R p n f != 0) (k : Nat)
  proof: Nat.recOn k hfn fun k ih h => ih by
    rw [Nat.add_succ] at h
    rw [← coeff_pow_p]; rw [map_pow]; rw [h]; rw [zero_pow hp.1.ne_zero]

中文:
定理 coeff_add_ne_zero
  条件: {f : Perfection R p} {n : 自然数} (hfn : coeff R p n f != 0) (k : 自然数)
  证明: Nat.recOn k hfn fun k ih h => ih by
    rw [Nat.add_succ] at h
    rw [← coeff_pow_p]; rw [map_pow]; rw [h]; rw [zero_pow hp.1.ne_zero]

Depends on / 依赖: Nat.add_succ, Nat.recOn, add_succ, coeff_pow_p, map_pow, ne_zero, zero_pow
-/
theorem coeff_add_ne_zero {f : Perfection R p} {n : Nat} (hfn : coeff R p n f != 0) (k : Nat) :
    coeff R p (n + k) f != 0 :=
Nat.recOn k hfn fun k ih h => ih by
    rw [Nat.add_succ] at h
    rw [← coeff_pow_p]; rw [map_pow]; rw [h]; rw [zero_pow hp.1.ne_zero]

/--
theorem `coeff_ne_zero_of_le` / 定理 `coeff_ne_zero_of_le`

English:
theorem coeff_ne_zero_of_le
  statement: {f : Perfection R p} {m n : Nat} (hfm : coeff R p m f != 0)
  proof: let ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
  hk.symm ▸ coeff_add_ne_zero hfm k

中文:
定理 coeff_ne_zero_of_le
  结论: {f : Perfection R p} {m n : 自然数} (hfm : coeff R p m f != 0)
  证明: let ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
  hk.symm ▸ coeff_add_ne_zero hfm k

Depends on / 依赖: Nat.exists_eq_add_of_le, coeff_add_ne_zero, exists_eq_add_of_le, hk.symm
-/
theorem coeff_ne_zero_of_le {f : Perfection R p} {m n : Nat} (hfm : coeff R p m f != 0)
    (hmn : m <= n) : coeff R p n f != 0 :=
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
  hk.symm ▸ coeff_add_ne_zero hfm k

/--
theorem `coeff_surjective` / 定理 `coeff_surjective`

English:
theorem coeff_surjective
  given: (h : Function.Surjective (frobenius R p)) (n : Nat)
  proof: by
  intro x
  refine ⟨⟨fun m => if h : n <= m then ?_ else x ^ p ^ (n - m), ?_⟩, ?_⟩
  · induction h using Nat.leRec with
    | refl =>
      exact x
    | le_succ_of_le hle xk =>
      choose x hx using h xk
      use x
  · intro m
    obtain (h1 | h1 | h1) : n <= m ∨ n = m + 1 ∨ ¬ n <= m + 1 := b

中文:
定理 coeff_surjective
  条件: (h : 函数.满射 (frobenius R p)) (n : 自然数)
  证明: by
  intro x
  refine ⟨⟨fun m => if h : n <= m then ?_ else x ^ p ^ (n - m), ?_⟩, ?_⟩
  · induction h using Nat.leRec with
    | refl =>
      exact x
    | le_succ_of_le hle xk =>
      choose x hx using h xk
      use x
  · intro m
    obtain (h1 | h1 | h1) : n <= m ∨ n = m + 1 ∨ ¬ n <= m + 1 := b

Depends on / 依赖: Classical, Classical.choose_spec, Nat.leRec, Nat.leRec_succ, choose_spec, frobenius_def, leRec_succ, le_succ_of_le, reduceDIte
-/
theorem coeff_surjective (h : Function.Surjective (frobenius R p)) (n : Nat) :
    Function.Surjective (Perfection.coeff R p n) := by
  intro x
  refine ⟨⟨fun m => if h : n <= m then ?_ else x ^ p ^ (n - m), ?_⟩, ?_⟩
  · induction h using Nat.leRec with
    | refl =>
      exact x
    | le_succ_of_le hle xk =>
      choose x hx using h xk
      use x
  · intro m
    obtain (h1 | h1 | h1) : n <= m ∨ n = m + 1 ∨ ¬ n <= m + 1 := by lia
    · have h1' : n <= m + 1 := by lia
      simp only [h1', ↓reduceDIte, h1, Nat.leRec_succ, ← frobenius_def]
      exact Classical.choose_spec (h _)
    · subst h1
      simp [← frobenius_def]
    · have h1' : ¬ n <= m := by lia
      have : n - m = (n - (m + 1)) + 1 := by lia
      simp [h1, h1', this, pow_succ, pow_mul]
  · simp

variable (R p)

/-- Given rings `R` and `S` of characteristic `p`, with `R` being perfect,
any homomorphism `R →+* S` can be lifted to a homomorphism `R →+* Perfection S p`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (R : Type u₁) [CommSemiring R] [CharP R p] [PerfectRing R p]
  body: { toFun := fun r => ⟨fun n => f (((frobeniusEquiv R p).symm : R ->+* R)^[n] r),
        fun n => by rw [← f.map_pow, Function.iterate_succ_apply', RingHom.coe_coe,
          frobeniusEquiv_symm_pow_p]⟩
      map_one' := ext fun _ => (congr_arg f <| iterate_map_one _ _).trans f.map_one
      map_mul'

中文:
定义 lift
  签名: (R : 类型u₁) [交换半环 R] [特征p R p] [完美环 R p]
  定义体: { toFun := fun r => ⟨fun n => f (((frobeniusEquiv R p).symm : R ->+* R)^[n] r),
        fun n => by rw [← f.map_pow, Function.iterate_succ_apply', RingHom.coe_coe,
          frobeniusEquiv_symm_pow_p]⟩
      map_one' := ext fun _ => (congr_arg f <| iterate_map_one _ _).trans f.map_one
      map_mul'

Depends on / 依赖: Function, Function.iterate_succ_apply, RingHom, RingHom.coe_coe, coe_coe, congr_arg, f.map_mul, f.map_one, f.map_pow, f.map_zero, frobeniusEquiv, frobeniusEquiv_symm_pow_p, iterate_, iterate_map_mul, iterate_map_one, iterate_map_zero, iterate_succ_apply, map_add, map_mul, map_one
-/
noncomputable def lift (R : Type u₁) [CommSemiring R] [CharP R p] [PerfectRing R p]
    (S : Type u₂) [CommSemiring S] [CharP S p] : (R ->+* S) ≃ (R ->+* Perfection S p) where
  toFun f :=
    { toFun := fun r => ⟨fun n => f (((frobeniusEquiv R p).symm : R ->+* R)^[n] r),
        fun n => by rw [← f.map_pow, Function.iterate_succ_apply', RingHom.coe_coe,
          frobeniusEquiv_symm_pow_p]⟩
      map_one' := ext fun _ => (congr_arg f <| iterate_map_one _ _).trans f.map_one
      map_mul' := fun _ _ =>
ext fun _ => (congr_arg f <| iterate_map_mul _ _ _ _).trans f.map_mul _ _
      map_zero' := ext fun _ => (congr_arg f <| iterate_map_zero _ _).trans f.map_zero
      map_add' := fun _ _ =>
ext fun _ => (congr_arg f <| iterate_map_add _ _ _ _).trans f.map_add _ _ }
invFun := RingHom.comp coeff S p 0
  right_inv f := RingHom.ext fun r => ext fun n =>
    show coeff S p 0 (f (((frobeniusEquiv R p).symm)^[n] r)) = coeff S p n (f r) by
      rw [← coeff_iterate_frobenius _ 0 n]; rw [zero_add]; rw [← RingHom.map_iterate_frobenius]; rw [Function.RightInverse.iterate (frobenius_apply_frobeniusEquiv_symm R p) n]

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {R : Type u₁} [CommSemiring R] [CharP R p] [PerfectRing R p] {S : Type u₂}
  proof: (lift p R S).symm.injective RingHom.ext hfg

中文:
定理 hom_ext
  结论: {R : 类型u₁} [交换半环 R] [特征p R p] [完美环 R p] {S : 类型u₂}
  证明: (lift p R S).symm.injective RingHom.ext hfg

Depends on / 依赖: RingHom, RingHom.ext, injective, symm.injective
-/
theorem hom_ext {R : Type u₁} [CommSemiring R] [CharP R p] [PerfectRing R p] {S : Type u₂}
    [CommSemiring S] [CharP S p] {f g : R ->+* Perfection S p}
    (hfg : forall x, coeff S p 0 (f x) = coeff S p 0 (g x)) : f = g :=
(lift p R S).symm.injective RingHom.ext hfg

variable {R} {S : Type u₂} [CommSemiring S] [CharP S p]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (φ : R ->+* S)
  body: mapMonoidHom p (φ : R ->* S)
map_zero' := Subtype.ext funext fun _ => φ.map_zero
map_add' _ _ := Subtype.ext funext fun _ => φ.map_add _ _

中文:
定义 map
  签名: (φ : R ->+* S)
  定义体: mapMonoidHom p (φ : R ->* S)
map_zero' := Subtype.ext funext fun _ => φ.map_zero
map_add' _ _ := Subtype.ext funext fun _ => φ.map_add _ _

Depends on / 依赖: mapMonoidHom
-/
def map (φ : R ->+* S) : Perfection R p ->+* Perfection S p where
  __ := mapMonoidHom p (φ : R ->* S)
map_zero' := Subtype.ext funext fun _ => φ.map_zero
map_add' _ _ := Subtype.ext funext fun _ => φ.map_add _ _

/--
theorem `coeff_map` / 定理 `coeff_map`

English:
theorem coeff_map
  given: (φ : R ->+* S) (f : Perfection R p) (n : Nat)
  proof: rfl

中文:
定理 coeff_map
  条件: (φ : R ->+* S) (f : Perfection R p) (n : 自然数)
  证明: rfl
-/
@[simp] theorem coeff_map (φ : R ->+* S) (f : Perfection R p) (n : Nat) :
    coeff S p n (map p φ f) = φ (coeff R p n f) := rfl

end CommSemiring

section CommRing

/--
Definition of `subring` / `subring` 的定义

English:
definition subring
  signature: (R : Type*) [CommRing R] (p : Nat) [hp : Fact p.Prime] [CharP R p]
  body: subsemiring R p
  neg_mem' hf n := (map_neg (frobenius R p) _).trans congr(-$(hf n))

@[deprecated (since := "2026-03-03")]
alias _root_.Ring.perfectionSubring := subring

中文:
定义 subring
  签名: (R : 类型) [交换环 R] (p : 自然数) [hp : Fact p.素] [特征p R p]
  定义体: subsemiring R p
  neg_mem' hf n := (map_neg (frobenius R p) _).trans congr(-$(hf n))

@[deprecated (since := "2026-03-03")]
alias _root_.Ring.perfectionSubring := subring

Depends on / 依赖: subsemiring
-/
def subring (R : Type*) [CommRing R] (p : Nat) [hp : Fact p.Prime] [CharP R p] :
    Subring (Nat -> R) where
  __ := subsemiring R p
  neg_mem' hf n := (map_neg (frobenius R p) _).trans congr(-$(hf n))

@[deprecated (since := "2026-03-03")]
alias _root_.Ring.perfectionSubring := subring

variable (R : Type*) [CommRing R] (p : Nat) [hp : Fact p.Prime] [CharP R p]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring (Perfection R p)
  body: inferInstanceAs Ring (subring R p)

中文:
实例 :
  签名: 环 (Perfection R p)
  定义体: inferInstanceAs Ring (subring R p)

Depends on / 依赖: subring
-/
instance : Ring (Perfection R p) :=
inferInstanceAs Ring (subring R p)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (Perfection R p)
  body: inferInstanceAs CommRing (subring R p)

中文:
实例 :
  签名: 交换环 (Perfection R p)
  定义体: inferInstanceAs CommRing (subring R p)

Depends on / 依赖: CommRing, subring
-/
instance : CommRing (Perfection R p) :=
inferInstanceAs CommRing (subring R p)

end CommRing

section CommMonoid_CommRing

/--
theorem `coeff_mapMonoidHom` / 定理 `coeff_mapMonoidHom`

English:
theorem coeff_mapMonoidHom
  statement: {p : Nat} [Fact p.Prime] {M N : Type*} [CommMonoid M] [CommRing N]
  proof: rfl

中文:
定理 coeff_mapMonoidHom
  结论: {p : 自然数} [Fact p.素] {M N : 类型} [交换幺半群 M] [交换环 N]
  证明: rfl
-/
@[simp] theorem coeff_mapMonoidHom {p : Nat} [Fact p.Prime] {M N : Type*} [CommMonoid M] [CommRing N]
    [CharP N p] (e : M ->* N) (n : Nat) (x : Perfection M p) :
    coeff N p n (mapMonoidHom p e x) = e (coeffMonoidHom M p n x) := rfl

end CommMonoid_CommRing

end Perfection

/--
Definition of `PerfectionMap` / `PerfectionMap` 的定义

English:
structure PerfectionMap
  parameters: (p : Nat) [Fact p.Prime] {R : Type u₁} [CommSemiring R] [CharP R p]
  axioms and operations (2):
    - injective : forall ⦃x y : P⦄, (forall n, π (((frobeniusEquiv P p).symm)^[n] x) = π (((frobeniusEquiv P p).symm)^[n] y)) -> x = y
    - surjective : forall f : Nat -> R, (forall n, f (n + 1) ^ p = f n) -> exists x : P, forall n, π (((frobeniusEquiv P p).symm)^[n] x) = f n

中文:
结构 Perfection映射
  参数: (p : 自然数) [Fact p.素] {R : 类型u₁} [交换半环 R] [特征p R p]
  公理与运算 (2 个):
    - injective : 对任意 ⦃x y : P⦄, (对任意 n, π (((frobeniusEquiv P p).symm)^[n] x) = π (((frobeniusEquiv P p).symm)^[n] y)) -> x = y
    - surjective : 对任意 f : 自然数 -> R, (对任意 n, f (n + 1) ^ p = f n) -> 存在 x : P, 对任意 n, π (((frobeniusEquiv P p).symm)^[n] x) = f n
-/
structure PerfectionMap (p : Nat) [Fact p.Prime] {R : Type u₁} [CommSemiring R] [CharP R p]
    {P : Type u₂} [CommSemiring P] [CharP P p] [PerfectRing P p] (π : P ->+* R) : Prop where
  injective : forall ⦃x y : P⦄,
    (forall n, π (((frobeniusEquiv P p).symm)^[n] x) = π (((frobeniusEquiv P p).symm)^[n] y)) -> x = y
  surjective : forall f : Nat -> R, (forall n, f (n + 1) ^ p = f n) -> exists x : P, forall n,
    π (((frobeniusEquiv P p).symm)^[n] x) = f n

namespace PerfectionMap

variable {p : Nat} [Fact p.Prime]
variable {R : Type u₁} [CommSemiring R] [CharP R p]
variable {P : Type u₃} [CommSemiring P] [CharP P p] [PerfectRing P p]

/--
theorem `mk'` / 定理 `mk'`

English:
theorem mk'
  given: {f : P ->+* R} (g : P ≃+* Perfection R p) (hfg : Perfection.lift p P R f = g)
  proof: { injective := fun x y hxy =>
g.injective
(RingHom.ext_iff.1 hfg x).symm.trans
Eq.symm (RingHom.ext_iff.1 hfg y).symm.trans Perfection.ext fun n => (hxy n).symm
    surjective := fun y hy =>
      let ⟨x, hx⟩ := g.surjective ⟨y, hy⟩
      ⟨x, fun n =>
        show Perfection.coeff R p n (Perfection.

中文:
定理 mk'
  条件: {f : P ->+* R} (g : P ≃+* Perfection R p) (hfg : Perfection.lift p P R f = g)
  证明: { injective := fun x y hxy =>
g.injective
(RingHom.ext_iff.1 hfg x).symm.trans
Eq.symm (RingHom.ext_iff.1 hfg y).symm.trans Perfection.ext fun n => (hxy n).symm
    surjective := fun y hy =>
      let ⟨x, hx⟩ := g.surjective ⟨y, hy⟩
      ⟨x, fun n =>
        show Perfection.coeff R p n (Perfection.

Depends on / 依赖: Eq.symm, Perfection, Perfection.coeff, Perfection.ext, Perfection.lift, RingHom, RingHom.ext_iff, ext_iff, g.injective, g.surjective, injective, surjective, symm.trans
-/
theorem mk' {f : P ->+* R} (g : P ≃+* Perfection R p) (hfg : Perfection.lift p P R f = g) :
    PerfectionMap p f :=
  { injective := fun x y hxy =>
g.injective
(RingHom.ext_iff.1 hfg x).symm.trans
Eq.symm (RingHom.ext_iff.1 hfg y).symm.trans Perfection.ext fun n => (hxy n).symm
    surjective := fun y hy =>
      let ⟨x, hx⟩ := g.surjective ⟨y, hy⟩
      ⟨x, fun n =>
        show Perfection.coeff R p n (Perfection.lift p P R f x) = Perfection.coeff R p n ⟨y, hy⟩ by
          simp [hfg, hx]⟩ }

variable (p R P)

/--
theorem `of` / 定理 `of`

English:
theorem of
  statement: PerfectionMap p (Perfection.coeff R p 0)
  proof: mk' (RingEquiv.refl _) (Equiv.eq_symm_apply _).1 rfl

中文:
定理 of
  结论: Perfection映射 p (Perfection.coeff R p 0)
  证明: mk' (RingEquiv.refl _) (Equiv.eq_symm_apply _).1 rfl

Depends on / 依赖: Equiv.eq_symm_apply, RingEquiv, RingEquiv.refl, eq_symm_apply
-/
theorem of : PerfectionMap p (Perfection.coeff R p 0) :=
mk' (RingEquiv.refl _) (Equiv.eq_symm_apply _).1 rfl

/--
theorem `id` / 定理 `id`

English:
theorem id
  given: [PerfectRing R p]
  statement: PerfectionMap p (RingHom.id R)
  proof: { injective := fun _ _ hxy => hxy 0
    surjective := fun f hf =>
      ⟨f 0, fun n =>
        show ((frobeniusEquiv R p).symm)^[n] (f 0) = f n from
Nat.recOn n rfl fun n ih => injective_pow_p R p by
            rw [Function.iterate_succ_apply']; rw [frobeniusEquiv_symm_pow_p]; rw [ih]; rw [hf]⟩ }

中文:
定理 id
  条件: [完美环 R p]
  结论: Perfection映射 p (环态射.id R)
  证明: { injective := fun _ _ hxy => hxy 0
    surjective := fun f hf =>
      ⟨f 0, fun n =>
        show ((frobeniusEquiv R p).symm)^[n] (f 0) = f n from
Nat.recOn n rfl fun n ih => injective_pow_p R p by
            rw [Function.iterate_succ_apply']; rw [frobeniusEquiv_symm_pow_p]; rw [ih]; rw [hf]⟩ }

Depends on / 依赖: Function, Function.iterate_succ_apply, Nat.recOn, frobeniusEquiv, frobeniusEquiv_symm_pow_p, injective, injective_pow_p, iterate_succ_apply, surjective
-/
theorem id [PerfectRing R p] : PerfectionMap p (RingHom.id R) :=
  { injective := fun _ _ hxy => hxy 0
    surjective := fun f hf =>
      ⟨f 0, fun n =>
        show ((frobeniusEquiv R p).symm)^[n] (f 0) = f n from
Nat.recOn n rfl fun n ih => injective_pow_p R p by
            rw [Function.iterate_succ_apply']; rw [frobeniusEquiv_symm_pow_p]; rw [ih]; rw [hf]⟩ }

variable {p R P}

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: {π : P ->+* R} (m : PerfectionMap p π)
  body: RingEquiv.ofBijective (Perfection.lift p P R π)
    ⟨fun _ _ hxy => m.injective fun n => (congr_arg (Perfection.coeff R p n) hxy :), fun f =>
      let ⟨x, hx⟩ := m.surjective f.1 f.2
⟨x, Perfection.ext hx⟩⟩

中文:
定义 equiv
  签名: {π : P ->+* R} (m : Perfection映射 p π)
  定义体: RingEquiv.ofBijective (Perfection.lift p P R π)
    ⟨fun _ _ hxy => m.injective fun n => (congr_arg (Perfection.coeff R p n) hxy :), fun f =>
      let ⟨x, hx⟩ := m.surjective f.1 f.2
⟨x, Perfection.ext hx⟩⟩

Depends on / 依赖: Perfection, Perfection.coeff, Perfection.ext, Perfection.lift, RingEquiv, RingEquiv.ofBijective, congr_arg, injective, m.injective, m.surjective, ofBijective, surjective
-/
noncomputable def equiv {π : P ->+* R} (m : PerfectionMap p π) : P ≃+* Perfection R p :=
  RingEquiv.ofBijective (Perfection.lift p P R π)
    ⟨fun _ _ hxy => m.injective fun n => (congr_arg (Perfection.coeff R p n) hxy :), fun f =>
      let ⟨x, hx⟩ := m.surjective f.1 f.2
⟨x, Perfection.ext hx⟩⟩

/--
theorem `equiv_apply` / 定理 `equiv_apply`

English:
theorem equiv_apply
  given: {π : P ->+* R} (m : PerfectionMap p π) (x : P)
  proof: rfl

中文:
定理 equiv_apply
  条件: {π : P ->+* R} (m : Perfection映射 p π) (x : P)
  证明: rfl
-/
theorem equiv_apply {π : P ->+* R} (m : PerfectionMap p π) (x : P) :
    m.equiv x = Perfection.lift p P R π x := rfl

/--
theorem `comp_equiv` / 定理 `comp_equiv`

English:
theorem comp_equiv
  given: {π : P ->+* R} (m : PerfectionMap p π) (x : P)
  proof: rfl

中文:
定理 comp_equiv
  条件: {π : P ->+* R} (m : Perfection映射 p π) (x : P)
  证明: rfl
-/
theorem comp_equiv {π : P ->+* R} (m : PerfectionMap p π) (x : P) :
    Perfection.coeff R p 0 (m.equiv x) = π x := rfl

/--
theorem `comp_equiv'` / 定理 `comp_equiv'`

English:
theorem comp_equiv'
  given: {π : P ->+* R} (m : PerfectionMap p π)
  proof: RingHom.ext fun _ => rfl

中文:
定理 comp_equiv'
  条件: {π : P ->+* R} (m : Perfection映射 p π)
  证明: RingHom.ext fun _ => rfl

Depends on / 依赖: RingHom, RingHom.ext
-/
theorem comp_equiv' {π : P ->+* R} (m : PerfectionMap p π) :
    (Perfection.coeff R p 0).comp ↑m.equiv = π :=
  RingHom.ext fun _ => rfl

/--
theorem `comp_symm_equiv` / 定理 `comp_symm_equiv`

English:
theorem comp_symm_equiv
  given: {π : P ->+* R} (m : PerfectionMap p π) (f : Perfection R p)
  proof: (m.comp_equiv _).symm.trans congr_arg _ m.equiv.apply_symm_apply f

中文:
定理 comp_symm_equiv
  条件: {π : P ->+* R} (m : Perfection映射 p π) (f : Perfection R p)
  证明: (m.comp_equiv _).symm.trans congr_arg _ m.equiv.apply_symm_apply f

Depends on / 依赖: apply_symm_apply, comp_equiv, congr_arg, m.comp_equiv, m.equiv.apply_symm_apply, symm.trans
-/
theorem comp_symm_equiv {π : P ->+* R} (m : PerfectionMap p π) (f : Perfection R p) :
    π (m.equiv.symm f) = Perfection.coeff R p 0 f :=
(m.comp_equiv _).symm.trans congr_arg _ m.equiv.apply_symm_apply f

/--
theorem `comp_symm_equiv'` / 定理 `comp_symm_equiv'`

English:
theorem comp_symm_equiv'
  given: {π : P ->+* R} (m : PerfectionMap p π)
  proof: RingHom.ext m.comp_symm_equiv

中文:
定理 comp_symm_equiv'
  条件: {π : P ->+* R} (m : Perfection映射 p π)
  证明: RingHom.ext m.comp_symm_equiv

Depends on / 依赖: RingHom, RingHom.ext, comp_symm_equiv, m.comp_symm_equiv
-/
theorem comp_symm_equiv' {π : P ->+* R} (m : PerfectionMap p π) :
    π.comp ↑m.equiv.symm = Perfection.coeff R p 0 :=
  RingHom.ext m.comp_symm_equiv

variable (p R P)

/-- Given rings `R` and `S` of characteristic `p`, with `R` being perfect,
any homomorphism `R →+* S` can be lifted to a homomorphism `R →+* P`,
where `P` is any perfection of `S`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: [PerfectRing R p] (S : Type u₂) [CommSemiring S] [CharP S p] (P : Type u₃)
  body: RingHom.comp ↑m.equiv.symm Perfection.lift p R S f
  invFun f := π.comp f
  left_inv f := by
    simp_rw [← RingHom.comp_assoc, comp_symm_equiv']
    exact (Perfection.lift p R S).symm_apply_apply f
  right_inv f := by
exact RingHom.ext fun x => m.equiv.injective (m.equiv.apply_symm_apply _).trans
 

中文:
定义 lift
  签名: [完美环 R p] (S : 类型u₂) [交换半环 S] [特征p S p] (P : 类型u₃)
  定义体: RingHom.comp ↑m.equiv.symm Perfection.lift p R S f
  invFun f := π.comp f
  left_inv f := by
    simp_rw [← RingHom.comp_assoc, comp_symm_equiv']
    exact (Perfection.lift p R S).symm_apply_apply f
  right_inv f := by
exact RingHom.ext fun x => m.equiv.injective (m.equiv.apply_symm_apply _).trans
 

Depends on / 依赖: Perfection, Perfection.lift, RingHom, RingHom.comp, m.equiv.symm
-/
noncomputable def lift [PerfectRing R p] (S : Type u₂) [CommSemiring S] [CharP S p] (P : Type u₃)
    [CommSemiring P] [CharP P p] [PerfectRing P p] (π : P ->+* S) (m : PerfectionMap p π) :
    (R ->+* S) ≃ (R ->+* P) where
toFun f := RingHom.comp ↑m.equiv.symm Perfection.lift p R S f
  invFun f := π.comp f
  left_inv f := by
    simp_rw [← RingHom.comp_assoc, comp_symm_equiv']
    exact (Perfection.lift p R S).symm_apply_apply f
  right_inv f := by
exact RingHom.ext fun x => m.equiv.injective (m.equiv.apply_symm_apply _).trans
 show Perfection.lift p R S (π.comp f) x = RingHom.comp (↑m.equiv) f x from
        RingHom.ext_iff.1 (by rw [← Equiv.eq_symm_apply]; rfl) _

variable {R p}

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: [PerfectRing R p] {S : Type u₂} [CommSemiring S] [CharP S p] {P : Type u₃}
  proof: (lift p R S P π m).symm.injective RingHom.ext hfg

中文:
定理 hom_ext
  结论: [完美环 R p] {S : 类型u₂} [交换半环 S] [特征p S p] {P : 类型u₃}
  证明: (lift p R S P π m).symm.injective RingHom.ext hfg

Depends on / 依赖: RingHom, RingHom.ext, injective, symm.injective
-/
theorem hom_ext [PerfectRing R p] {S : Type u₂} [CommSemiring S] [CharP S p] {P : Type u₃}
    [CommSemiring P] [CharP P p] [PerfectRing P p] (π : P ->+* S) (m : PerfectionMap p π)
    {f g : R ->+* P} (hfg : forall x, π (f x) = π (g x)) : f = g :=
(lift p R S P π m).symm.injective RingHom.ext hfg

variable {P} (p)
variable {S : Type u₂} [CommSemiring S] [CharP S p]
variable {Q : Type u₄} [CommSemiring Q] [CharP Q p] [PerfectRing Q p]

/-- A ring homomorphism `R →+* S` induces `P →+* Q`, a map of the respective perfections. -/
@[nolint unusedArguments]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {π : P ->+* R} (_ : PerfectionMap p π) {σ : Q ->+* S} (n : PerfectionMap p σ)
  body: lift p P S Q σ n φ.comp π

中文:
定义 map
  签名: {π : P ->+* R} (_ : Perfection映射 p π) {σ : Q ->+* S} (n : Perfection映射 p σ)
  定义体: lift p P S Q σ n φ.comp π
-/
noncomputable def map {π : P ->+* R} (_ : PerfectionMap p π) {σ : Q ->+* S} (n : PerfectionMap p σ)
    (φ : R ->+* S) : P ->+* Q :=
lift p P S Q σ n φ.comp π

/--
theorem `comp_map` / 定理 `comp_map`

English:
theorem comp_map
  statement: {π : P ->+* R} (m : PerfectionMap p π) {σ : Q ->+* S} (n : PerfectionMap p σ)
  proof: (lift p P S Q σ n).symm_apply_apply _

中文:
定理 comp_map
  结论: {π : P ->+* R} (m : Perfection映射 p π) {σ : Q ->+* S} (n : Perfection映射 p σ)
  证明: (lift p P S Q σ n).symm_apply_apply _

Depends on / 依赖: symm_apply_apply
-/
theorem comp_map {π : P ->+* R} (m : PerfectionMap p π) {σ : Q ->+* S} (n : PerfectionMap p σ)
    (φ : R ->+* S) : σ.comp (map p m n φ) = φ.comp π :=
  (lift p P S Q σ n).symm_apply_apply _

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: {π : P ->+* R} (m : PerfectionMap p π) {σ : Q ->+* S} (n : PerfectionMap p σ)
  proof: RingHom.ext_iff.1 (comp_map p m n φ) x

中文:
定理 map_map
  结论: {π : P ->+* R} (m : Perfection映射 p π) {σ : Q ->+* S} (n : Perfection映射 p σ)
  证明: RingHom.ext_iff.1 (comp_map p m n φ) x

Depends on / 依赖: RingHom, RingHom.ext_iff, comp_map, ext_iff
-/
theorem map_map {π : P ->+* R} (m : PerfectionMap p π) {σ : Q ->+* S} (n : PerfectionMap p σ)
    (φ : R ->+* S) (x : P) : σ (map p m n φ x) = φ (π x) :=
  RingHom.ext_iff.1 (comp_map p m n φ) x

/--
theorem `map_eq_map` / 定理 `map_eq_map`

English:
theorem map_eq_map
  given: (φ : R ->+* S)
  statement: map p (of p R) (of p S) φ = Perfection.map p φ
  proof: hom_ext _ (of p S) fun f => by rw [map_map, Perfection.coeff_map]

中文:
定理 map_eq_map
  条件: (φ : R ->+* S)
  结论: map p (of p R) (of p S) φ = Perfection.map p φ
  证明: hom_ext _ (of p S) fun f => by rw [map_map, Perfection.coeff_map]

Depends on / 依赖: Perfection, Perfection.coeff_map, coeff_map, hom_ext, map_map
-/
theorem map_eq_map (φ : R ->+* S) : map p (of p R) (of p S) φ = Perfection.map p φ :=
  hom_ext _ (of p S) fun f => by rw [map_map, Perfection.coeff_map]

end PerfectionMap

section ModP

variable (O : Type u₂) [CommRing O] (p : Nat)

/--
Definition of `ModP` / `ModP` 的定义

English:
abbreviation ModP
  body: O ⧸ (Ideal.span {(p : O)} : Ideal O)

中文:
缩写 ModP
  定义体: O ⧸ (Ideal.span {(p : O)} : Ideal O)

Depends on / 依赖: Ideal.span
-/
abbrev ModP :=
  O ⧸ (Ideal.span {(p : O)} : Ideal O)

namespace ModP

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fact
  signature: p.Prime] [hvp
  body: CharP.quotient O p hvp.1

中文:
实例 [Fact
  签名: p.素] [hvp
  定义体: CharP.quotient O p hvp.1

Depends on / 依赖: CharP.quotient, quotient
-/
instance [Fact p.Prime] [hvp : Fact (¬ IsUnit (p : O))] : CharP (ModP O p) p :=
CharP.quotient O p hvp.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hp
  signature: : Fact p.Prime] [Fact (¬ IsUnit (p : O))] : Nontrivial (ModP O p)
  body: CharP.nontrivial_of_char_ne_one hp.1.ne_one

中文:
实例 [hp
  签名: : Fact p.素] [Fact (¬ 是单位 (p : O))] : 非平凡 (ModP O p)
  定义体: CharP.nontrivial_of_char_ne_one hp.1.ne_one

Depends on / 依赖: CharP.nontrivial_of_char_ne_one, ne_one, nontrivial_of_char_ne_one
-/
instance [hp : Fact p.Prime] [Fact (¬ IsUnit (p : O))] : Nontrivial (ModP O p) :=
  CharP.nontrivial_of_char_ne_one hp.1.ne_one

end ModP

end ModP

section Perfectoid

variable (K : Type u₁) [Field K] (v : Valuation K Real>=0)
variable (O : Type u₂) [CommRing O] [Algebra O K] (hv : v.Integers O)
variable (p : Nat)

namespace ModP

section Classical

attribute [local instance] Classical.dec

/--
Definition of `preVal` / `preVal` 的定义

English:
definition preVal
  signature: (x : ModP O p)
  body: if x = 0 then 0 else v (algebraMap O K x.out)

中文:
定义 preVal
  签名: (x : ModP O p)
  定义体: if x = 0 then 0 else v (algebraMap O K x.out)

Depends on / 依赖: algebraMap, x.out
-/
noncomputable def preVal (x : ModP O p) : Real>=0 :=
  if x = 0 then 0 else v (algebraMap O K x.out)

variable {K v O p}

@[simp]
/--
theorem `preVal_zero` / 定理 `preVal_zero`

English:
theorem preVal_zero
  statement: preVal K v O p 0 = 0
  proof: if_pos rfl

include hv

中文:
定理 preVal_zero
  结论: preVal K v O p 0 = 0
  证明: if_pos rfl

include hv

Depends on / 依赖: if_pos
-/
theorem preVal_zero : preVal K v O p 0 = 0 :=
  if_pos rfl

include hv

/--
theorem `preVal_mk` / 定理 `preVal_mk`

English:
theorem preVal_mk
  given: {x : O} (hx : (Ideal.Quotient.mk _ x : ModP O p) != 0)
  proof: by
  obtain ⟨r, hr⟩ : exists (a : O), a * (p : O) = (Ideal.Quotient.mk _ x).out - x :=
Ideal.mem_span_singleton'.1 Ideal.Quotient.eq.1 Quotient.sound' Quotient.mk_out' _
  refine (if_neg hx).trans (v.map_eq_of_sub_lt <| lt_of_not_ge ?_)
  rw [← map_sub]; rw [← hr]; rw [hv.le_iff_dvd]
  exact fun hpr

中文:
定理 preVal_mk
  条件: {x : O} (hx : (理想.商.mk _ x : ModP O p) != 0)
  证明: by
  obtain ⟨r, hr⟩ : exists (a : O), a * (p : O) = (Ideal.Quotient.mk _ x).out - x :=
Ideal.mem_span_singleton'.1 Ideal.Quotient.eq.1 Quotient.sound' Quotient.mk_out' _
  refine (if_neg hx).trans (v.map_eq_of_sub_lt <| lt_of_not_ge ?_)
  rw [← map_sub]; rw [← hr]; rw [hv.le_iff_dvd]
  exact fun hpr

Depends on / 依赖: Ideal.Quotient.eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk, Ideal.mem_span_singleton, Quotient, Quotient.mk_out, Quotient.sound, dvd_of_mul_left_dvd, eq_zero_iff_mem, hv.le_iff_dvd, if_neg, le_iff_dvd, lt_of_not_ge, map_eq_of_sub_lt, map_sub, mem_span_singleton, mk_out, v.map_eq_of_sub_lt
-/
theorem preVal_mk {x : O} (hx : (Ideal.Quotient.mk _ x : ModP O p) != 0) :
    preVal K v O p (Ideal.Quotient.mk _ x) = v (algebraMap O K x) := by
  obtain ⟨r, hr⟩ : exists (a : O), a * (p : O) = (Ideal.Quotient.mk _ x).out - x :=
Ideal.mem_span_singleton'.1 Ideal.Quotient.eq.1 Quotient.sound' Quotient.mk_out' _
  refine (if_neg hx).trans (v.map_eq_of_sub_lt <| lt_of_not_ge ?_)
  rw [← map_sub]; rw [← hr]; rw [hv.le_iff_dvd]
  exact fun hprx =>
    hx (Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.mem_span_singleton.2 <| dvd_of_mul_left_dvd hprx)

/--
theorem `preVal_mul` / 定理 `preVal_mul`

English:
theorem preVal_mul
  given: {x y : ModP O p} (hxy0 : x * y != 0)
  proof: by
  have hx0 : x != 0 := mt (by rintro rfl; rw [zero_mul]) hxy0
  have hy0 : y != 0 := mt (by rintro rfl; rw [mul_zero]) hxy0
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul (Ideal.Quotient.mk (Ideal.span {↑p})) r s] at hxy0 ⊢


中文:
定理 preVal_mul
  条件: {x y : ModP O p} (hxy0 : x * y != 0)
  证明: by
  have hx0 : x != 0 := mt (by rintro rfl; rw [zero_mul]) hxy0
  have hy0 : y != 0 := mt (by rintro rfl; rw [mul_zero]) hxy0
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul (Ideal.Quotient.mk (Ideal.span {↑p})) r s] at hxy0 ⊢


Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.span, Quotient, map_mul, mk_surjective, mul_zero, preVal_mk, v.map_mul, zero_mul
-/
theorem preVal_mul {x y : ModP O p} (hxy0 : x * y != 0) :
    preVal K v O p (x * y) = preVal K v O p x * preVal K v O p y := by
  have hx0 : x != 0 := mt (by rintro rfl; rw [zero_mul]) hxy0
  have hy0 : y != 0 := mt (by rintro rfl; rw [mul_zero]) hxy0
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul (Ideal.Quotient.mk (Ideal.span {↑p})) r s] at hxy0 ⊢
  rw [preVal_mk hv hx0]; rw [preVal_mk hv hy0]; rw [preVal_mk hv hxy0]; rw [map_mul]; rw [v.map_mul]

/--
theorem `preVal_add` / 定理 `preVal_add`

English:
theorem preVal_add
  given: (x y : ModP O p)
  proof: by
  obtain rfl | hx0 := eq_or_ne x 0
  · simp
  obtain rfl | hy0 := eq_or_ne y 0
  · simp
  by_cases hxy0 : x + y = 0
  · simp [hxy0]
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_add (Ideal.Quotient.mk (Ideal.span {↑p})) r s] at

中文:
定理 preVal_add
  条件: (x y : ModP O p)
  证明: by
  obtain rfl | hx0 := eq_or_ne x 0
  · simp
  obtain rfl | hy0 := eq_or_ne y 0
  · simp
  by_cases hxy0 : x + y = 0
  · simp [hxy0]
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_add (Ideal.Quotient.mk (Ideal.span {↑p})) r s] at

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.span, Quotient, eq_or_ne, map_add, mk_surjective, preVal_mk, v.map_add
-/
theorem preVal_add (x y : ModP O p) :
    preVal K v O p (x + y) <= max (preVal K v O p x) (preVal K v O p y) := by
  obtain rfl | hx0 := eq_or_ne x 0
  · simp
  obtain rfl | hy0 := eq_or_ne y 0
  · simp
  by_cases hxy0 : x + y = 0
  · simp [hxy0]
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_add (Ideal.Quotient.mk (Ideal.span {↑p})) r s] at hxy0 ⊢
  rw [preVal_mk hv hx0]; rw [preVal_mk hv hy0]; rw [preVal_mk hv hxy0]; rw [map_add]; exact v.map_add _ _

/--
theorem `v_p_lt_preVal` / 定理 `v_p_lt_preVal`

English:
theorem v_p_lt_preVal
  given: {x : ModP O p}
  statement: v p < preVal K v O p x ↔ x != 0
  proof: by
  refine ⟨by aesop, fun h => lt_of_not_ge fun hp => h ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [preVal_mk hv h]; rw [← map_natCast (algebraMap O K) p]; rw [hv.le_iff_dvd] at hp
  · rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; exact hp

中文:
定理 v_p_lt_preVal
  条件: {x : ModP O p}
  结论: v p < preVal K v O p x ↔ x != 0
  证明: by
  refine ⟨by aesop, fun h => lt_of_not_ge fun hp => h ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [preVal_mk hv h]; rw [← map_natCast (algebraMap O K) p]; rw [hv.le_iff_dvd] at hp
  · rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; exact hp

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_surjective, Ideal.mem_span_singleton, Quotient, algebraMap, eq_zero_iff_mem, hv.le_iff_dvd, le_iff_dvd, lt_of_not_ge, map_natCast, mem_span_singleton, mk_surjective, preVal_mk
-/
theorem v_p_lt_preVal {x : ModP O p} : v p < preVal K v O p x ↔ x != 0 := by
  refine ⟨by aesop, fun h => lt_of_not_ge fun hp => h ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [preVal_mk hv h]; rw [← map_natCast (algebraMap O K) p]; rw [hv.le_iff_dvd] at hp
  · rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; exact hp

/--
theorem `preVal_eq_zero` / 定理 `preVal_eq_zero`

English:
theorem preVal_eq_zero
  given: {x : ModP O p}
  statement: preVal K v O p x = 0 ↔ x = 0 where
  proof: by
    contrapose! h
    exact ((v_p_lt_preVal hv).2 h).ne_zero
  mpr hx := by simp [hx]

中文:
定理 preVal_eq_zero
  条件: {x : ModP O p}
  结论: preVal K v O p x = 0 ↔ x = 0 where
  证明: by
    contrapose! h
    exact ((v_p_lt_preVal hv).2 h).ne_zero
  mpr hx := by simp [hx]

Depends on / 依赖: contrapose, ne_zero, v_p_lt_preVal
-/
theorem preVal_eq_zero {x : ModP O p} : preVal K v O p x = 0 ↔ x = 0 where
  mp h := by
    contrapose! h
    exact ((v_p_lt_preVal hv).2 h).ne_zero
  mpr hx := by simp [hx]

/--
theorem `v_p_lt_val` / 定理 `v_p_lt_val`

English:
theorem v_p_lt_val
  given: {x : O}
  proof: by
  rw [lt_iff_not_ge]; rw [not_iff_not]; rw [← map_natCast (algebraMap O K) p]; rw [hv.le_iff_dvd]; rw [Ideal.Quotient.eq_zero_iff_mem]; rw [Ideal.mem_span_singleton]

中文:
定理 v_p_lt_val
  条件: {x : O}
  证明: by
  rw [lt_iff_not_ge]; rw [not_iff_not]; rw [← map_natCast (algebraMap O K) p]; rw [hv.le_iff_dvd]; rw [Ideal.Quotient.eq_zero_iff_mem]; rw [Ideal.mem_span_singleton]

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Quotient, algebraMap, eq_zero_iff_mem, hv.le_iff_dvd, le_iff_dvd, lt_iff_not_ge, map_natCast, mem_span_singleton, not_iff_not
-/
theorem v_p_lt_val {x : O} :
    v p < v (algebraMap O K x) ↔ (Ideal.Quotient.mk _ x : ModP O p) != 0 := by
  rw [lt_iff_not_ge]; rw [not_iff_not]; rw [← map_natCast (algebraMap O K) p]; rw [hv.le_iff_dvd]; rw [Ideal.Quotient.eq_zero_iff_mem]; rw [Ideal.mem_span_singleton]

open NNReal

variable [hp : Fact p.Prime]

/--
theorem `mul_ne_zero_of_pow_p_ne_zero` / 定理 `mul_ne_zero_of_pow_p_ne_zero`

English:
theorem mul_ne_zero_of_pow_p_ne_zero
  given: {x y : ModP O p} (hx : x ^ p != 0) (hy : y ^ p != 0)
  proof: by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1p : (0 : Real) < 1 / p := one_div_pos.2 (Nat.cast_pos.2 hp.1.pos)
  rw [← (Ideal.Quotient.mk (Ideal.span {(p : O)})).map_mul]
  rw [← (Ideal.Quotient.mk (Ideal.span {(p : O)})).map_pow

中文:
定理 mul_ne_zero_of_pow_p_ne_zero
  条件: {x y : ModP O p} (hx : x ^ p != 0) (hy : y ^ p != 0)
  证明: by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1p : (0 : Real) < 1 / p := one_div_pos.2 (Nat.cast_pos.2 hp.1.pos)
  rw [← (Ideal.Quotient.mk (Ideal.span {(p : O)})).map_mul]
  rw [← (Ideal.Quotient.mk (Ideal.span {(p : O)})).map_pow

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.span, Nat.cast_ne_zero, Nat.cast_pos, Quotient, cast_ne_zero, cast_pos, map_mul, map_pow, mk_surjective, mul_one_div_cancel, ne_zero, one_div_pos, rpow_lt_rpow_iff, rpow_mul, rpow_natCast, v.map_pow, v_p_lt_val
-/
theorem mul_ne_zero_of_pow_p_ne_zero {x y : ModP O p} (hx : x ^ p != 0) (hy : y ^ p != 0) :
    x * y != 0 := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1p : (0 : Real) < 1 / p := one_div_pos.2 (Nat.cast_pos.2 hp.1.pos)
  rw [← (Ideal.Quotient.mk (Ideal.span {(p : O)})).map_mul]
  rw [← (Ideal.Quotient.mk (Ideal.span {(p : O)})).map_pow] at hx hy
  rw [← v_p_lt_val hv] at hx hy ⊢
  rw [map_pow]; rw [v.map_pow]; rw [← rpow_lt_rpow_iff h1p]; rw [← rpow_natCast]; rw [← rpow_mul]; rw [mul_one_div_cancel (Nat.cast_ne_zero.2 hp.1.ne_zero : (p : Real) != 0)]; rw [rpow_one] at hx hy
  rw [map_mul]; rw [v.map_mul]; refine lt_of_le_of_lt ?_ (mul_lt_mul'' hx hy zero_le zero_le)
  by_cases hvp : v p = 0
  · rw [hvp]; exact zero_le
  replace hvp := zero_lt_iff.2 hvp
  conv_lhs => rw [← rpow_one (v p)]
  rw [← rpow_add (ne_of_gt hvp)]
  refine rpow_le_rpow_of_exponent_ge hvp (map_natCast (algebraMap O K) p ▸ hv.2 _) ?_
  rw [← add_div]; rw [div_le_one (Nat.cast_pos.2 hp.1.pos : 0 < (p : Real))]; exact mod_cast hp.1.two_le

end Classical

end ModP

/--
Definition of `PreTilt` / `PreTilt` 的定义

English:
definition PreTilt
  body: Perfection (ModP O p) p

中文:
定义 PreTilt
  定义体: Perfection (ModP O p) p

Depends on / 依赖: Perfection
-/
def PreTilt :=
  Perfection (ModP O p) p

namespace PreTilt

variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (PreTilt O p)
  body: inferInstanceAs CommRing Perfection _ _

中文:
实例 :
  签名: 交换环 (PreTilt O p)
  定义体: inferInstanceAs CommRing Perfection _ _

Depends on / 依赖: CommRing, Perfection
-/
instance : CommRing (PreTilt O p) :=
inferInstanceAs CommRing Perfection _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CharP (PreTilt O p) p
  body: inferInstanceAs CharP (Perfection _ _) _

中文:
实例 :
  签名: 特征p (PreTilt O p) p
  定义体: inferInstanceAs CharP (Perfection _ _) _

Depends on / 依赖: Perfection
-/
instance : CharP (PreTilt O p) p :=
inferInstanceAs CharP (Perfection _ _) _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PerfectRing (PreTilt O p) p
  body: inferInstanceAs PerfectRing (Perfection _ _) p

中文:
实例 :
  签名: 完美环 (PreTilt O p) p
  定义体: inferInstanceAs PerfectRing (Perfection _ _) p

Depends on / 依赖: PerfectRing, Perfection
-/
instance : PerfectRing (PreTilt O p) p :=
inferInstanceAs PerfectRing (Perfection _ _) p

section coeff

variable {O p}

/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (n : Nat)
  body: Perfection.coeff (ModP O p) p n

中文:
定义 coeff
  签名: (n : 自然数)
  定义体: Perfection.coeff (ModP O p) p n

Depends on / 依赖: Perfection, Perfection.coeff
-/
def coeff (n : Nat) : PreTilt O p ->+* ModP O p := Perfection.coeff (ModP O p) p n

/--
theorem `coeff_def` / 定理 `coeff_def`

English:
theorem coeff_def
  given: (n : Nat) (x : PreTilt O p)
  statement: coeff n x = Perfection.coeff _ _ n x
  proof: rfl

中文:
定理 coeff_def
  条件: (n : 自然数) (x : PreTilt O p)
  结论: coeff n x = Perfection.coeff _ _ n x
  证明: rfl
-/
theorem coeff_def (n : Nat) (x : PreTilt O p) : coeff n x = Perfection.coeff _ _ n x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `coeff_frobenius` / 定理 `coeff_frobenius`

English:
theorem coeff_frobenius
  given: (n : Nat) (x : PreTilt O p)
  proof: by
  simp [PreTilt, coeff]

中文:
定理 coeff_frobenius
  条件: (n : 自然数) (x : PreTilt O p)
  证明: by
  simp [PreTilt, coeff]

Depends on / 依赖: PreTilt
-/
theorem coeff_frobenius (n : Nat) (x : PreTilt O p) :
    (coeff (n + 1) (frobenius _ p x)) = coeff n x := by
  simp [PreTilt, coeff]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `coeff_iterate_frobenius` / 定理 `coeff_iterate_frobenius`

English:
theorem coeff_iterate_frobenius
  given: (m n : Nat) (x : PreTilt O p)
  proof: by
  simp [PreTilt, coeff]

中文:
定理 coeff_iterate_frobenius
  条件: (m n : 自然数) (x : PreTilt O p)
  证明: by
  simp [PreTilt, coeff]

Depends on / 依赖: PreTilt
-/
theorem coeff_iterate_frobenius (m n : Nat) (x : PreTilt O p) :
    (coeff (m + n) ((frobenius _ p)^[n] x)) = coeff m x := by
  simp [PreTilt, coeff]

/--
theorem `coeff_iterate_frobenius'` / 定理 `coeff_iterate_frobenius'`

English:
theorem coeff_iterate_frobenius'
  given: (x : PreTilt O p) {m n : Nat} (hmn : m <= n)
  proof: Perfection.coeff_iterate_frobenius' _ _ _ hmn

@[simp]

中文:
定理 coeff_iterate_frobenius'
  条件: (x : PreTilt O p) {m n : 自然数} (hmn : m <= n)
  证明: Perfection.coeff_iterate_frobenius' _ _ _ hmn

@[simp]

Depends on / 依赖: Perfection, Perfection.coeff_iterate_frobenius, coeff_iterate_frobenius
-/
theorem coeff_iterate_frobenius' (x : PreTilt O p) {m n : Nat} (hmn : m <= n) :
    coeff n ((frobenius _ p)^[m] x) = coeff (n - m) x :=
  Perfection.coeff_iterate_frobenius' _ _ _ hmn

@[simp]
/--
theorem `coeff_pow_p` / 定理 `coeff_pow_p`

English:
theorem coeff_pow_p
  given: (x : PreTilt O p) (n : Nat)
  statement: coeff (n + 1) x ^ p = coeff n x
  proof: Perfection.coeff_pow_p x n

中文:
定理 coeff_pow_p
  条件: (x : PreTilt O p) (n : 自然数)
  结论: coeff (n + 1) x ^ p = coeff n x
  证明: Perfection.coeff_pow_p x n

Depends on / 依赖: Perfection, Perfection.coeff_pow_p, coeff_pow_p
-/
theorem coeff_pow_p (x : PreTilt O p) (n : Nat) : coeff (n + 1) x ^ p = coeff n x :=
  Perfection.coeff_pow_p x n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `coeff_frobeniusEquiv_symm` / 定理 `coeff_frobeniusEquiv_symm`

English:
theorem coeff_frobeniusEquiv_symm
  given: (n : Nat) (x : PreTilt O p)
  proof: by
  simp [PreTilt, coeff]

中文:
定理 coeff_frobeniusEquiv_symm
  条件: (n : 自然数) (x : PreTilt O p)
  证明: by
  simp [PreTilt, coeff]

Depends on / 依赖: PreTilt
-/
theorem coeff_frobeniusEquiv_symm (n : Nat) (x : PreTilt O p) :
    (coeff n (((frobeniusEquiv _ p).symm) x)) = coeff (n + 1) x := by
  simp [PreTilt, coeff]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `coeff_iterate_frobeniusEquiv_symm` / 定理 `coeff_iterate_frobeniusEquiv_symm`

English:
theorem coeff_iterate_frobeniusEquiv_symm
  given: (m n : Nat) (x : PreTilt O p)
  proof: by
  simp [PreTilt, coeff]

中文:
定理 coeff_iterate_frobeniusEquiv_symm
  条件: (m n : 自然数) (x : PreTilt O p)
  证明: by
  simp [PreTilt, coeff]

Depends on / 依赖: PreTilt
-/
theorem coeff_iterate_frobeniusEquiv_symm (m n : Nat) (x : PreTilt O p) :
    (coeff m (((frobeniusEquiv _ p).symm^[n]) x)) = coeff (m + n) x := by
  simp [PreTilt, coeff]

end coeff

section Classical

open Perfection

open scoped Classical in
/--
Definition of `valAux` / `valAux` 的定义

English:
definition valAux
  signature: (f : PreTilt O p)
  body: if h : exists n, coeff n f != 0 then
    ModP.preVal K v O p (coeff (Nat.find h) f) ^ p ^ Nat.find h
  else 0

中文:
定义 valAux
  签名: (f : PreTilt O p)
  定义体: if h : exists n, coeff n f != 0 then
    ModP.preVal K v O p (coeff (Nat.find h) f) ^ p ^ Nat.find h
  else 0

Depends on / 依赖: ModP.preVal, Nat.find, preVal
-/
noncomputable def valAux (f : PreTilt O p) : Real>=0 :=
  if h : exists n, coeff n f != 0 then
    ModP.preVal K v O p (coeff (Nat.find h) f) ^ p ^ Nat.find h
  else 0

variable {K v O p}

open scoped Classical in
/--
theorem `coeff_nat_find_add_ne_zero` / 定理 `coeff_nat_find_add_ne_zero`

English:
theorem coeff_nat_find_add_ne_zero
  given: {f : PreTilt O p} {h : exists n, coeff n f != 0} (k : Nat)
  proof: coeff_add_ne_zero (Nat.find_spec h) k

@[simp]

中文:
定理 coeff_nat_find_add_ne_zero
  条件: {f : PreTilt O p} {h : 存在 n, coeff n f != 0} (k : 自然数)
  证明: coeff_add_ne_zero (Nat.find_spec h) k

@[simp]

Depends on / 依赖: Nat.find_spec, coeff_add_ne_zero, find_spec
-/
theorem coeff_nat_find_add_ne_zero {f : PreTilt O p} {h : exists n, coeff n f != 0} (k : Nat) :
    coeff (Nat.find h + k) f != 0 :=
  coeff_add_ne_zero (Nat.find_spec h) k

@[simp]
/--
theorem `valAux_zero` / 定理 `valAux_zero`

English:
theorem valAux_zero
  statement: valAux K v O p 0 = 0
  proof: dif_neg fun ⟨_, hn⟩ => hn rfl

include hv

中文:
定理 valAux_zero
  结论: valAux K v O p 0 = 0
  证明: dif_neg fun ⟨_, hn⟩ => hn rfl

include hv

Depends on / 依赖: dif_neg
-/
theorem valAux_zero : valAux K v O p 0 = 0 :=
  dif_neg fun ⟨_, hn⟩ => hn rfl

include hv

/--
theorem `valAux_eq` / 定理 `valAux_eq`

English:
theorem valAux_eq
  given: {f : PreTilt O p} {n : Nat} (hfn : coeff n f != 0)
  proof: by
  have h : exists n, coeff n f != 0 := ⟨n, hfn⟩
  rw [valAux]; rw [dif_pos h]
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.find_min' h hfn)
  induction k with
  | zero => rfl
  | succ k ih => ?_
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (coeff (Nat.find h + k + 1) f)
  hav

中文:
定理 valAux_eq
  条件: {f : PreTilt O p} {n : 自然数} (hfn : coeff n f != 0)
  证明: by
  have h : exists n, coeff n f != 0 := ⟨n, hfn⟩
  rw [valAux]; rw [dif_pos h]
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.find_min' h hfn)
  induction k with
  | zero => rfl
  | succ k ih => ?_
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (coeff (Nat.find h + k + 1) f)
  hav

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Nat.exists_eq_add_of_le, Nat.find, Nat.find_min, Quotient, classical, coeff_nat, coeff_nat_find_add_ne_zero, coeff_pow_p, dif_pos, exists_eq_add_of_le, find_min, hx.symm, map_pow, mk_surjective, valAux
-/
theorem valAux_eq {f : PreTilt O p} {n : Nat} (hfn : coeff n f != 0) :
    valAux K v O p f = ModP.preVal K v O p (coeff n f) ^ p ^ n := by
  have h : exists n, coeff n f != 0 := ⟨n, hfn⟩
  rw [valAux]; rw [dif_pos h]
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.find_min' h hfn)
  induction k with
  | zero => rfl
  | succ k ih => ?_
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (coeff (Nat.find h + k + 1) f)
  have h1 : (Ideal.Quotient.mk _ x : ModP O p) != 0 := hx.symm ▸ hfn
  have h2 : (Ideal.Quotient.mk _ (x ^ p) : ModP O p) != 0 := by
    rw [map_pow]; rw [hx]; rw [coeff_pow_p]
    exact coeff_nat_find_add_ne_zero k
  rw [ih (coeff_nat_find_add_ne_zero k)]; rw [← add_assoc]; rw [← hx]; rw [← coeff_pow_p]; rw [← hx]; rw [← map_pow]; rw [ModP.preVal_mk hv h1]; rw [ModP.preVal_mk hv h2]; rw [map_pow]; rw [v.map_pow]; rw [← pow_mul]; rw [pow_succ']

/--
theorem `valAux_one` / 定理 `valAux_one`

English:
theorem valAux_one
  statement: valAux K v O p 1 = 1
  proof: (valAux_eq (hv := hv) <| show coeff 0 1 != 0 from one_ne_zero).trans by
    rw [pow_zero]; rw [pow_one]; rw [map_one]; rw [← (Ideal.Quotient.mk _).map_one]; rw [ModP.preVal_mk hv]; rw [map_one]; rw [v.map_one]
    change (1 : ModP O p) != 0
    exact one_ne_zero

中文:
定理 valAux_one
  结论: valAux K v O p 1 = 1
  证明: (valAux_eq (hv := hv) <| show coeff 0 1 != 0 from one_ne_zero).trans by
    rw [pow_zero]; rw [pow_one]; rw [map_one]; rw [← (Ideal.Quotient.mk _).map_one]; rw [ModP.preVal_mk hv]; rw [map_one]; rw [v.map_one]
    change (1 : ModP O p) != 0
    exact one_ne_zero

Depends on / 依赖: Ideal.Quotient.mk, ModP.preVal_mk, Quotient, map_one, one_ne_zero, pow_one, pow_zero, preVal_mk, v.map_one, valAux_eq
-/
theorem valAux_one : valAux K v O p 1 = 1 :=
(valAux_eq (hv := hv) <| show coeff 0 1 != 0 from one_ne_zero).trans by
    rw [pow_zero]; rw [pow_one]; rw [map_one]; rw [← (Ideal.Quotient.mk _).map_one]; rw [ModP.preVal_mk hv]; rw [map_one]; rw [v.map_one]
    change (1 : ModP O p) != 0
    exact one_ne_zero

/--
theorem `valAux_mul` / 定理 `valAux_mul`

English:
theorem valAux_mul
  given: (f g : PreTilt O p)
  proof: by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  obtain rfl | hg := eq_or_ne g 0
  · simp
obtain ⟨m, hm⟩ : exists n, coeff n f != 0 := not_forall.1 fun h => hf Perfection.ext h
obtain ⟨n, hn⟩ : exists n, coeff n g != 0 := not_forall.1 fun h => hg Perfection.ext h
  replace hm := coeff_ne_zero_of_le h

中文:
定理 valAux_mul
  条件: (f g : PreTilt O p)
  证明: by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  obtain rfl | hg := eq_or_ne g 0
  · simp
obtain ⟨m, hm⟩ : exists n, coeff n f != 0 := not_forall.1 fun h => hf Perfection.ext h
obtain ⟨n, hn⟩ : exists n, coeff n g != 0 := not_forall.1 fun h => hg Perfection.ext h
  replace hm := coeff_ne_zero_of_le h

Depends on / 依赖: ModP.mul_ne_zero_of_pow_p_ne_zero, Perfection, Perfection.ext, coeff_ne_zero_of_le, coeff_p, eq_or_ne, le_max_left, le_max_right, map_mul, mul_ne_zero_of_pow_p_ne_zero, not_forall, replace
-/
theorem valAux_mul (f g : PreTilt O p) :
    valAux K v O p (f * g) = valAux K v O p f * valAux K v O p g := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  obtain rfl | hg := eq_or_ne g 0
  · simp
obtain ⟨m, hm⟩ : exists n, coeff n f != 0 := not_forall.1 fun h => hf Perfection.ext h
obtain ⟨n, hn⟩ : exists n, coeff n g != 0 := not_forall.1 fun h => hg Perfection.ext h
  replace hm := coeff_ne_zero_of_le hm (le_max_left m n)
  replace hn := coeff_ne_zero_of_le hn (le_max_right m n)
  have hfg : coeff (max m n + 1) (f * g) != 0 := by
    rw [map_mul]
    refine ModP.mul_ne_zero_of_pow_p_ne_zero (hv := hv) ?_ ?_
    · rw [coeff_pow_p f]; assumption
    · rw [coeff_pow_p g]; assumption
  rw [valAux_eq hv (coeff_add_ne_zero hm 1)]; rw [valAux_eq hv (coeff_add_ne_zero hn 1)]; rw [valAux_eq hv hfg]
  rw [map_mul] at hfg ⊢; rw [ModP.preVal_mul hv hfg, mul_pow]

/--
theorem `valAux_add` / 定理 `valAux_add`

English:
theorem valAux_add
  given: (f g : PreTilt O p)
  proof: by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  obtain rfl | hg := eq_or_ne g 0
  · simp
  by_cases hfg : f + g = 0
  · simp [hfg]
replace hf : exists n, coeff n f != 0 := not_forall.1 fun h => hf Perfection.ext h
replace hg : exists n, coeff n g != 0 := not_forall.1 fun h => hg Perfection.ext h
rep

中文:
定理 valAux_add
  条件: (f g : PreTilt O p)
  证明: by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  obtain rfl | hg := eq_or_ne g 0
  · simp
  by_cases hfg : f + g = 0
  · simp [hfg]
replace hf : exists n, coeff n f != 0 := not_forall.1 fun h => hf Perfection.ext h
replace hg : exists n, coeff n g != 0 := not_forall.1 fun h => hg Perfection.ext h
rep

Depends on / 依赖: Perfection, Perfection.ext, coeff_ne_zero_of_le, eq_or_ne, le_max_lef, le_trans, not_forall, replace
-/
theorem valAux_add (f g : PreTilt O p) :
    valAux K v O p (f + g) <= max (valAux K v O p f) (valAux K v O p g) := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  obtain rfl | hg := eq_or_ne g 0
  · simp
  by_cases hfg : f + g = 0
  · simp [hfg]
replace hf : exists n, coeff n f != 0 := not_forall.1 fun h => hf Perfection.ext h
replace hg : exists n, coeff n g != 0 := not_forall.1 fun h => hg Perfection.ext h
replace hfg : exists n, coeff n (f + g) != 0 := not_forall.1 fun h => hfg Perfection.ext h
  obtain ⟨m, hm⟩ := hf; obtain ⟨n, hn⟩ := hg; obtain ⟨k, hk⟩ := hfg
  replace hm := coeff_ne_zero_of_le hm (le_trans (le_max_left m n) (le_max_left _ k))
  replace hn := coeff_ne_zero_of_le hn (le_trans (le_max_right m n) (le_max_left _ k))
  replace hk := coeff_ne_zero_of_le hk (le_max_right (max m n) k)
  rw [valAux_eq hv hm]; rw [valAux_eq hv hn]; rw [valAux_eq hv hk]; rw [map_add]
  rcases le_max_iff.1
      (ModP.preVal_add hv (coeff (max (max m n) k) f)
      (coeff (max (max m n) k) g)) with h | h
  · exact le_max_of_le_left (pow_le_pow_left' h _)
  · exact le_max_of_le_right (pow_le_pow_left' h _)

variable (K v O p)

/--
Definition of `val` / `val` 的定义

English:
definition val
  signature: : Valuation (PreTilt O p) Real>=0 where
  body: valAux K v O p
  map_one' := valAux_one hv
  map_mul' := valAux_mul hv
  map_zero' := valAux_zero
  map_add_le_max' := valAux_add hv

中文:
定义 val
  签名: : 赋值 (PreTilt O p) 实数>=0 where
  定义体: valAux K v O p
  map_one' := valAux_one hv
  map_mul' := valAux_mul hv
  map_zero' := valAux_zero
  map_add_le_max' := valAux_add hv

Depends on / 依赖: valAux
-/
noncomputable def val : Valuation (PreTilt O p) Real>=0 where
  toFun := valAux K v O p
  map_one' := valAux_one hv
  map_mul' := valAux_mul hv
  map_zero' := valAux_zero
  map_add_le_max' := valAux_add hv

variable {K v O p}

/--
theorem `map_eq_zero` / 定理 `map_eq_zero`

English:
theorem map_eq_zero
  given: {f : PreTilt O p}
  statement: val K v O hv p f = 0 ↔ f = 0
  proof: by
  by_cases hf0 : f = 0
  · rw [hf0]; exact iff_of_true (Valuation.map_zero _) rfl
obtain ⟨n, hn⟩ : exists n, coeff n f != 0 := not_forall.1 fun h => hf0 Perfection.ext h
  change valAux K v O p f = 0 ↔ f = 0; refine iff_of_false (fun hvf => hn ?_) hf0
  rw [valAux_eq hv hn] at hvf
  replace hvf :

中文:
定理 map_eq_zero
  条件: {f : PreTilt O p}
  结论: val K v O hv p f = 0 ↔ f = 0
  证明: by
  by_cases hf0 : f = 0
  · rw [hf0]; exact iff_of_true (Valuation.map_zero _) rfl
obtain ⟨n, hn⟩ : exists n, coeff n f != 0 := not_forall.1 fun h => hf0 Perfection.ext h
  change valAux K v O p f = 0 ↔ f = 0; refine iff_of_false (fun hvf => hn ?_) hf0
  rw [valAux_eq hv hn] at hvf
  replace hvf :

Depends on / 依赖: ModP.preVal_eq_zero, Perfection, Perfection.ext, Valuation, Valuation.map_zero, eq_zero_of_pow_eq_zero, iff_of_false, iff_of_true, map_zero, not_forall, preVal_eq_zero, replace, valAux, valAux_eq
-/
theorem map_eq_zero {f : PreTilt O p} : val K v O hv p f = 0 ↔ f = 0 := by
  by_cases hf0 : f = 0
  · rw [hf0]; exact iff_of_true (Valuation.map_zero _) rfl
obtain ⟨n, hn⟩ : exists n, coeff n f != 0 := not_forall.1 fun h => hf0 Perfection.ext h
  change valAux K v O p f = 0 ↔ f = 0; refine iff_of_false (fun hvf => hn ?_) hf0
  rw [valAux_eq hv hn] at hvf
  replace hvf := eq_zero_of_pow_eq_zero hvf
  rwa [ModP.preVal_eq_zero hv] at hvf

end Classical

include hv

/--
theorem `isDomain` / 定理 `isDomain`

English:
theorem isDomain
  statement: IsDomain (PreTilt O p)
  proof: by
  have hp : Nat.Prime p := Fact.out
  have : Nontrivial (PreTilt O p) := ⟨(CharP.nontrivial_of_char_ne_one hp.ne_one).1⟩
  have : NoZeroDivisors (PreTilt O p) :=
    ⟨fun hfg => by
      simp_rw [← map_eq_zero hv] at hfg ⊢; contrapose! hfg; rw [Valuation.map_mul]
      exact mul_ne_zero hfg.1 hfg

中文:
定理 isDomain
  结论: 是整环 (PreTilt O p)
  证明: by
  have hp : Nat.Prime p := Fact.out
  have : Nontrivial (PreTilt O p) := ⟨(CharP.nontrivial_of_char_ne_one hp.ne_one).1⟩
  have : NoZeroDivisors (PreTilt O p) :=
    ⟨fun hfg => by
      simp_rw [← map_eq_zero hv] at hfg ⊢; contrapose! hfg; rw [Valuation.map_mul]
      exact mul_ne_zero hfg.1 hfg

Depends on / 依赖: CharP.nontrivial_of_char_ne_one, Fact.out, Nat.Prime, NoZeroDivisors, NoZeroDivisors.to_isDomain, Nontrivial, PreTilt, Valuation, Valuation.map_mul, contrapose, hp.ne_one, map_eq_zero, map_mul, mul_ne_zero, ne_one, nontrivial_of_char_ne_one, simp_rw, to_isDomain
-/
theorem isDomain : IsDomain (PreTilt O p) := by
  have hp : Nat.Prime p := Fact.out
  have : Nontrivial (PreTilt O p) := ⟨(CharP.nontrivial_of_char_ne_one hp.ne_one).1⟩
  have : NoZeroDivisors (PreTilt O p) :=
    ⟨fun hfg => by
      simp_rw [← map_eq_zero hv] at hfg ⊢; contrapose! hfg; rw [Valuation.map_mul]
      exact mul_ne_zero hfg.1 hfg.2⟩
  exact NoZeroDivisors.to_isDomain _

end PreTilt

/--
Definition of `Tilt` / `Tilt` 的定义

English:
definition Tilt
  signature: [Fact p.Prime] [hvp : Fact (v p != 1)]
  body: have _ := Fact.mk mt hv.one_of_isUnit (map_natCast (algebraMap O K) p).symm ▸ hvp.1
  FractionRing (PreTilt O p)

中文:
定义 Tilt
  签名: [Fact p.素] [hvp : Fact (v p != 1)]
  定义体: have _ := Fact.mk mt hv.one_of_isUnit (map_natCast (algebraMap O K) p).symm ▸ hvp.1
  FractionRing (PreTilt O p)

Depends on / 依赖: Fact.mk, FractionRing, PreTilt, algebraMap, hv.one_of_isUnit, map_natCast, one_of_isUnit
-/
def Tilt [Fact p.Prime] [hvp : Fact (v p != 1)] :=
have _ := Fact.mk mt hv.one_of_isUnit (map_natCast (algebraMap O K) p).symm ▸ hvp.1
  FractionRing (PreTilt O p)

namespace Tilt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fact
  signature: p.Prime] [hvp
  body: #adaptation_note /-- This type ascription was not needed prior to nightly-2026-05-17. -/
  haveI : Fact ¬IsUnit (p : O) :=
Fact.mk mt hv.one_of_isUnit (map_natCast (algebraMap O K) p).symm ▸ hvp.1
  haveI := PreTilt.isDomain K v O hv p
inferInstanceAs Field (FractionRing (PreTilt O p))

中文:
实例 [Fact
  签名: p.素] [hvp
  定义体: #adaptation_note /-- This type ascription was not needed prior to nightly-2026-05-17. -/
  haveI : Fact ¬IsUnit (p : O) :=
Fact.mk mt hv.one_of_isUnit (map_natCast (algebraMap O K) p).symm ▸ hvp.1
  haveI := PreTilt.isDomain K v O hv p
inferInstanceAs Field (FractionRing (PreTilt O p))

Depends on / 依赖: Fact.mk, FractionRing, IsUnit, PreTilt, PreTilt.isDomain, adaptation_note, algebraMap, ascription, hv.one_of_isUnit, isDomain, map_natCast, needed, nightly, one_of_isUnit
-/
noncomputable instance [Fact p.Prime] [hvp : Fact (v p != 1)] : Field (Tilt K v O hv p) :=
  #adaptation_note /-- This type ascription was not needed prior to nightly-2026-05-17. -/
  haveI : Fact ¬IsUnit (p : O) :=
Fact.mk mt hv.one_of_isUnit (map_natCast (algebraMap O K) p).symm ▸ hvp.1
  haveI := PreTilt.isDomain K v O hv p
inferInstanceAs Field (FractionRing (PreTilt O p))

end Tilt

end Perfectoid
