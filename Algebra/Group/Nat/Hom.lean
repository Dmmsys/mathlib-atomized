/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Tactic.Spread

/-!
# Extensionality of monoid homs from `ℕ`
-/

@[expose] public section

assert_not_exists IsOrderedMonoid MonoidWithZero

open Additive Multiplicative

variable {M : Type*}

section AddMonoidHomClass

variable {A B F : Type*} [FunLike F Nat A]

/--
lemma `ext_nat'` / 引理 `ext_nat'`

English:
lemma ext_nat'
  given: [AddZeroClass A] [AddMonoidHomClass F Nat A] (f g : F) (h : f 1 = g 1)
  statement: f = g
  proof: DFunLike.ext f g by
    intro n
    induction n with
    | zero => simp_rw [map_zero f, map_zero g]
    | succ n ihn =>
      simp [h, ihn]

@[ext]

中文:
引理 ext_nat'
  条件: [加法零类 A] [加法幺半群态射类 F 自然数 A] (f g : F) (h : f 1 = g 1)
  结论: f = g
  证明: DFunLike.ext f g by
    intro n
    induction n with
    | zero => simp_rw [map_zero f, map_zero g]
    | succ n ihn =>
      simp [h, ihn]

@[ext]

Depends on / 依赖: DFunLike, DFunLike.ext, map_zero, simp_rw
-/
lemma ext_nat' [AddZeroClass A] [AddMonoidHomClass F Nat A] (f g : F) (h : f 1 = g 1) : f = g :=
DFunLike.ext f g by
    intro n
    induction n with
    | zero => simp_rw [map_zero f, map_zero g]
    | succ n ihn =>
      simp [h, ihn]

@[ext]
/--
lemma `AddMonoidHom.ext_nat` / 引理 `AddMonoidHom.ext_nat`

English:
lemma AddMonoidHom.ext_nat
  given: [AddZeroClass A] {f g : Nat ->+ A}
  statement: f 1 = g 1 -> f = g
  proof: ext_nat' f g

中文:
引理 加法幺半群态射.ext_nat
  条件: [加法零类 A] {f g : 自然数 ->+ A}
  结论: f 1 = g 1 -> f = g
  证明: ext_nat' f g

Depends on / 依赖: ext_nat
-/
lemma AddMonoidHom.ext_nat [AddZeroClass A] {f g : Nat ->+ A} : f 1 = g 1 -> f = g :=
  ext_nat' f g

end AddMonoidHomClass

section AddMonoid
variable [AddMonoid M]

variable (M) in
/--
Definition of `multiplesHom` / `multiplesHom` 的定义

English:
definition multiplesHom
  signature: : M ≃ (Nat ->+ M) where
  body: { toFun := fun n => n • x
    map_zero' := zero_nsmul x
    map_add' := fun _ _ => add_nsmul _ _ _ }
  invFun f := f 1
  left_inv := one_nsmul
right_inv f := AddMonoidHom.ext_nat one_nsmul (f 1)

中文:
定义 multiplesHom
  签名: : M ≃ (自然数 ->+ M) where
  定义体: { toFun := fun n => n • x
    map_zero' := zero_nsmul x
    map_add' := fun _ _ => add_nsmul _ _ _ }
  invFun f := f 1
  left_inv := one_nsmul
right_inv f := AddMonoidHom.ext_nat one_nsmul (f 1)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext_nat, add_nsmul, ext_nat, invFun, left_inv, map_add, map_zero, one_nsmul, right_inv, zero_nsmul
-/
def multiplesHom : M ≃ (Nat ->+ M) where
  toFun x :=
  { toFun := fun n => n • x
    map_zero' := zero_nsmul x
    map_add' := fun _ _ => add_nsmul _ _ _ }
  invFun f := f 1
  left_inv := one_nsmul
right_inv f := AddMonoidHom.ext_nat one_nsmul (f 1)

/--
lemma `multiplesHom_apply` / 引理 `multiplesHom_apply`

English:
lemma multiplesHom_apply
  given: (x : M) (n : Nat)
  statement: multiplesHom M x n = n • x
  proof: rfl

中文:
引理 multiplesHom_apply
  条件: (x : M) (n : 自然数)
  结论: multiplesHom M x n = n • x
  证明: rfl
-/
@[simp] lemma multiplesHom_apply (x : M) (n : Nat) : multiplesHom M x n = n • x := rfl

/--
lemma `multiplesHom_symm_apply` / 引理 `multiplesHom_symm_apply`

English:
lemma multiplesHom_symm_apply
  given: (f : Nat ->+ M)
  statement: (multiplesHom M).symm f = f 1
  proof: rfl

中文:
引理 multiplesHom_symm_apply
  条件: (f : 自然数 ->+ M)
  结论: (multiplesHom M).symm f = f 1
  证明: rfl
-/
@[simp] lemma multiplesHom_symm_apply (f : Nat ->+ M) : (multiplesHom M).symm f = f 1 := rfl

/--
lemma `AddMonoidHom.apply_nat` / 引理 `AddMonoidHom.apply_nat`

English:
lemma AddMonoidHom.apply_nat
  given: (f : Nat ->+ M) (n : Nat)
  statement: f n = n • f 1
  proof: by
  rw [← multiplesHom_symm_apply]; rw [← multiplesHom_apply]; rw [Equiv.apply_symm_apply]

中文:
引理 加法幺半群态射.apply_nat
  条件: (f : 自然数 ->+ M) (n : 自然数)
  结论: f n = n • f 1
  证明: by
  rw [← multiplesHom_symm_apply]; rw [← multiplesHom_apply]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, multiplesHom_apply, multiplesHom_symm_apply
-/
lemma AddMonoidHom.apply_nat (f : Nat ->+ M) (n : Nat) : f n = n • f 1 := by
  rw [← multiplesHom_symm_apply]; rw [← multiplesHom_apply]; rw [Equiv.apply_symm_apply]

end AddMonoid

section Monoid
variable [Monoid M]

variable (M) in
/--
Definition of `powersHom` / `powersHom` 的定义

English:
definition powersHom
  signature: : M ≃ (Multiplicative Nat ->* M)
  body: Additive.ofMul.trans (multiplesHom _).trans AddMonoidHom.toMultiplicativeLeft

中文:
定义 powersHom
  签名: : M ≃ (Multiplicative 自然数 ->* M)
  定义体: Additive.ofMul.trans (multiplesHom _).trans AddMonoidHom.toMultiplicativeLeft

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toMultiplicativeLeft, Additive, Additive.ofMul.trans, multiplesHom, toMultiplicativeLeft
-/
def powersHom : M ≃ (Multiplicative Nat ->* M) :=
Additive.ofMul.trans (multiplesHom _).trans AddMonoidHom.toMultiplicativeLeft

/--
lemma `powersHom_apply` / 引理 `powersHom_apply`

English:
lemma powersHom_apply
  given: (x : M) (n : Multiplicative Nat)
  proof: rfl

中文:
引理 powersHom_apply
  条件: (x : M) (n : Multiplicative 自然数)
  证明: rfl
-/
@[simp] lemma powersHom_apply (x : M) (n : Multiplicative Nat) :
    powersHom M x n = x ^ n.toAdd := rfl

/--
lemma `powersHom_symm_apply` / 引理 `powersHom_symm_apply`

English:
lemma powersHom_symm_apply
  given: (f : Multiplicative Nat ->* M)
  proof: rfl

中文:
引理 powersHom_symm_apply
  条件: (f : Multiplicative 自然数 ->* M)
  证明: rfl
-/
@[simp] lemma powersHom_symm_apply (f : Multiplicative Nat ->* M) :
    (powersHom M).symm f = f (Multiplicative.ofAdd 1) := rfl

/--
lemma `MonoidHom.apply_mnat` / 引理 `MonoidHom.apply_mnat`

English:
lemma MonoidHom.apply_mnat
  given: (f : Multiplicative Nat ->* M) (n : Multiplicative Nat)
  proof: by
  rw [← powersHom_symm_apply]; rw [← powersHom_apply]; rw [Equiv.apply_symm_apply]

@[ext]

中文:
引理 幺半群态射.apply_mnat
  条件: (f : Multiplicative 自然数 ->* M) (n : Multiplicative 自然数)
  证明: by
  rw [← powersHom_symm_apply]; rw [← powersHom_apply]; rw [Equiv.apply_symm_apply]

@[ext]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, powersHom_apply, powersHom_symm_apply
-/
lemma MonoidHom.apply_mnat (f : Multiplicative Nat ->* M) (n : Multiplicative Nat) :
    f n = f (Multiplicative.ofAdd 1) ^ n.toAdd := by
  rw [← powersHom_symm_apply]; rw [← powersHom_apply]; rw [Equiv.apply_symm_apply]

@[ext]
/--
lemma `MonoidHom.ext_mnat` / 引理 `MonoidHom.ext_mnat`

English:
lemma MonoidHom.ext_mnat
  given: ⦃f g
  statement: Multiplicative Nat ->* M⦄
  proof: MonoidHom.ext fun n => by rw [f.apply_mnat, g.apply_mnat, h]

中文:
引理 幺半群态射.ext_mnat
  条件: ⦃f g
  结论: Multiplicative 自然数 ->* M⦄
  证明: MonoidHom.ext fun n => by rw [f.apply_mnat, g.apply_mnat, h]

Depends on / 依赖: MonoidHom, MonoidHom.ext, apply_mnat, f.apply_mnat, g.apply_mnat
-/
lemma MonoidHom.ext_mnat ⦃f g : Multiplicative Nat ->* M⦄
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g :=
  MonoidHom.ext fun n => by rw [f.apply_mnat, g.apply_mnat, h]

end Monoid

section AddCommMonoid
variable [AddCommMonoid M]

variable (M) in
/--
Definition of `multiplesAddHom` / `multiplesAddHom` 的定义

English:
definition multiplesAddHom
  signature: : M ≃+ (Nat ->+ M) where
  body: multiplesHom M
  map_add' a b := AddMonoidHom.ext fun n => by simp [nsmul_add]

中文:
定义 multiplesAddHom
  签名: : M ≃+ (自然数 ->+ M) where
  定义体: multiplesHom M
  map_add' a b := AddMonoidHom.ext fun n => by simp [nsmul_add]

Depends on / 依赖: multiplesHom
-/
def multiplesAddHom : M ≃+ (Nat ->+ M) where
  __ := multiplesHom M
  map_add' a b := AddMonoidHom.ext fun n => by simp [nsmul_add]

/--
lemma `multiplesAddHom_apply` / 引理 `multiplesAddHom_apply`

English:
lemma multiplesAddHom_apply
  given: (x : M) (n : Nat)
  statement: multiplesAddHom M x n = n • x
  proof: rfl

中文:
引理 multiplesAddHom_apply
  条件: (x : M) (n : 自然数)
  结论: multiplesAddHom M x n = n • x
  证明: rfl
-/
@[simp] lemma multiplesAddHom_apply (x : M) (n : Nat) : multiplesAddHom M x n = n • x := rfl

/--
lemma `multiplesAddHom_symm_apply` / 引理 `multiplesAddHom_symm_apply`

English:
lemma multiplesAddHom_symm_apply
  given: (f : Nat ->+ M)
  statement: (multiplesAddHom M).symm f = f 1
  proof: rfl

中文:
引理 multiplesAddHom_symm_apply
  条件: (f : 自然数 ->+ M)
  结论: (multiplesAddHom M).symm f = f 1
  证明: rfl
-/
@[simp] lemma multiplesAddHom_symm_apply (f : Nat ->+ M) : (multiplesAddHom M).symm f = f 1 := rfl

end AddCommMonoid

section CommMonoid
variable [CommMonoid M]

variable (M) in
/--
Definition of `powersMulHom` / `powersMulHom` 的定义

English:
definition powersMulHom
  signature: : M ≃* (Multiplicative Nat ->* M) where
  body: powersHom M
  map_mul' a b := MonoidHom.ext fun n => by simp [mul_pow]

@[simp]

中文:
定义 powersMulHom
  签名: : M ≃* (Multiplicative 自然数 ->* M) where
  定义体: powersHom M
  map_mul' a b := MonoidHom.ext fun n => by simp [mul_pow]

@[simp]

Depends on / 依赖: powersHom
-/
def powersMulHom : M ≃* (Multiplicative Nat ->* M) where
  __ := powersHom M
  map_mul' a b := MonoidHom.ext fun n => by simp [mul_pow]

@[simp]
/--
lemma `powersMulHom_apply` / 引理 `powersMulHom_apply`

English:
lemma powersMulHom_apply
  given: (x : M) (n : Multiplicative Nat)
  statement: powersMulHom M x n = x ^ n.toAdd
  proof: rfl

@[simp]

中文:
引理 powersMulHom_apply
  条件: (x : M) (n : Multiplicative 自然数)
  结论: powersMulHom M x n = x ^ n.toAdd
  证明: rfl

@[simp]
-/
lemma powersMulHom_apply (x : M) (n : Multiplicative Nat) : powersMulHom M x n = x ^ n.toAdd := rfl

@[simp]
/--
lemma `powersMulHom_symm_apply` / 引理 `powersMulHom_symm_apply`

English:
lemma powersMulHom_symm_apply
  given: (f : Multiplicative Nat ->* M)
  statement: (powersMulHom M).symm f = f (ofAdd 1)
  proof: rfl

中文:
引理 powersMulHom_symm_apply
  条件: (f : Multiplicative 自然数 ->* M)
  结论: (powersMulHom M).symm f = f (ofAdd 1)
  证明: rfl
-/
lemma powersMulHom_symm_apply (f : Multiplicative Nat ->* M) : (powersMulHom M).symm f = f (ofAdd 1) :=
  rfl

end CommMonoid
