/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Logic.Equiv.Defs
/-!
# Theorems about invertible elements

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

universe u

variable {α : Type u}

/-- An `Invertible` element is a unit. -/
@[simps]
/--
Definition of `unitOfInvertible` / `unitOfInvertible` 的定义

English:
definition unitOfInvertible
  signature: [Monoid α] (a : α) [Invertible a]
  body: a
  inv := ⅟a
  val_inv := by simp
  inv_val := by simp

中文:
定义 unitOfInvertible
  签名: [幺半群 α] (a : α) [可逆 a]
  定义体: a
  inv := ⅟a
  val_inv := by simp
  inv_val := by simp
-/
def unitOfInvertible [Monoid α] (a : α) [Invertible a] : αˣ where
  val := a
  inv := ⅟a
  val_inv := by simp
  inv_val := by simp

/--
theorem `isUnit_of_invertible` / 定理 `isUnit_of_invertible`

English:
theorem isUnit_of_invertible
  given: [Monoid α] (a : α) [Invertible a]
  statement: IsUnit a
  proof: ⟨unitOfInvertible a, rfl⟩

中文:
定理 isUnit_of_invertible
  条件: [幺半群 α] (a : α) [可逆 a]
  结论: 是单位 a
  证明: ⟨unitOfInvertible a, rfl⟩

Depends on / 依赖: unitOfInvertible
-/
theorem isUnit_of_invertible [Monoid α] (a : α) [Invertible a] : IsUnit a :=
  ⟨unitOfInvertible a, rfl⟩

/--
Instance `Units.invertible` / 实例 `Units.invertible`

English:
instance Units.invertible
  signature: [Monoid α] (u : αˣ)
  body: ↑u⁻¹
  invOf_mul_self := u.inv_mul
  mul_invOf_self := u.mul_inv

@[simp]

中文:
实例 单位群.invertible
  签名: [幺半群 α] (u : αˣ)
  定义体: ↑u⁻¹
  invOf_mul_self := u.inv_mul
  mul_invOf_self := u.mul_inv

@[simp]
-/
instance Units.invertible [Monoid α] (u : αˣ) :
    Invertible (u : α) where
  invOf := ↑u⁻¹
  invOf_mul_self := u.inv_mul
  mul_invOf_self := u.mul_inv

@[simp]
/--
theorem `invOf_units` / 定理 `invOf_units`

English:
theorem invOf_units
  given: [Monoid α] (u : αˣ) [Invertible (u : α)]
  statement: ⅟(u : α) = ↑u⁻¹
  proof: invOf_eq_right_inv u.mul_inv

中文:
定理 invOf_units
  条件: [幺半群 α] (u : αˣ) [可逆 (u : α)]
  结论: ⅟(u : α) = ↑u⁻¹
  证明: invOf_eq_right_inv u.mul_inv

Depends on / 依赖: invOf_eq_right_inv, mul_inv, u.mul_inv
-/
theorem invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟(u : α) = ↑u⁻¹ :=
  invOf_eq_right_inv u.mul_inv

/--
theorem `IsUnit.nonempty_invertible` / 定理 `IsUnit.nonempty_invertible`

English:
theorem IsUnit.nonempty_invertible
  given: [Monoid α] {a : α} (h : IsUnit a)
  statement: Nonempty (Invertible a)
  proof: let ⟨x, hx⟩ := h
  ⟨x.invertible.copy _ hx.symm⟩

中文:
定理 是单位.nonempty_invertible
  条件: [幺半群 α] {a : α} (h : 是单位 a)
  结论: 非空 (可逆 a)
  证明: let ⟨x, hx⟩ := h
  ⟨x.invertible.copy _ hx.symm⟩

Depends on / 依赖: hx.symm, invertible, x.invertible.copy
-/
theorem IsUnit.nonempty_invertible [Monoid α] {a : α} (h : IsUnit a) : Nonempty (Invertible a) :=
  let ⟨x, hx⟩ := h
  ⟨x.invertible.copy _ hx.symm⟩

/-- Convert `IsUnit` to `Invertible` using `Classical.choice`.

Prefer `casesI h.nonempty_invertible` over `letI := h.invertible` if you want to avoid choice. -/
@[instance_reducible]
/--
Definition of `IsUnit.invertible` / `IsUnit.invertible` 的定义

English:
definition IsUnit.invertible
  signature: [Monoid α] {a : α} (h : IsUnit a)
  body: Classical.choice h.nonempty_invertible

@[simp]

中文:
定义 是单位.invertible
  签名: [幺半群 α] {a : α} (h : 是单位 a)
  定义体: Classical.choice h.nonempty_invertible

@[simp]

Depends on / 依赖: Classical, Classical.choice, choice, h.nonempty_invertible, nonempty_invertible
-/
noncomputable def IsUnit.invertible [Monoid α] {a : α} (h : IsUnit a) : Invertible a :=
  Classical.choice h.nonempty_invertible

@[simp]
/--
theorem `nonempty_invertible_iff_isUnit` / 定理 `nonempty_invertible_iff_isUnit`

English:
theorem nonempty_invertible_iff_isUnit
  given: [Monoid α] (a : α)
  statement: Nonempty (Invertible a) ↔ IsUnit a
  proof: ⟨Nonempty.rec @isUnit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩

中文:
定理 nonempty_invertible_iff_isUnit
  条件: [幺半群 α] (a : α)
  结论: 非空 (可逆 a) ↔ 是单位 a
  证明: ⟨Nonempty.rec @isUnit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩

Depends on / 依赖: IsUnit, IsUnit.nonempty_invertible, Nonempty, Nonempty.rec, isUnit_of_invertible, nonempty_invertible
-/
theorem nonempty_invertible_iff_isUnit [Monoid α] (a : α) : Nonempty (Invertible a) ↔ IsUnit a :=
⟨Nonempty.rec @isUnit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩

/--
theorem `Commute.invOf_right` / 定理 `Commute.invOf_right`

English:
theorem Commute.invOf_right
  given: [Monoid α] {a b : α} [Invertible b] (h : Commute a b)
  proof: calc
    a * ⅟b = ⅟b * (b * a * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (a * b * ⅟b) := by rw [h.eq]
    _ = ⅟b * a := by simp [mul_assoc]

中文:
定理 Commute.invOf_right
  条件: [幺半群 α] {a b : α} [可逆 b] (h : Commute a b)
  证明: calc
    a * ⅟b = ⅟b * (b * a * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (a * b * ⅟b) := by rw [h.eq]
    _ = ⅟b * a := by simp [mul_assoc]

Depends on / 依赖: h.eq, mul_assoc
-/
theorem Commute.invOf_right [Monoid α] {a b : α} [Invertible b] (h : Commute a b) :
    Commute a (⅟b) :=
  calc
    a * ⅟b = ⅟b * (b * a * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (a * b * ⅟b) := by rw [h.eq]
    _ = ⅟b * a := by simp [mul_assoc]

/--
theorem `Commute.invOf_left` / 定理 `Commute.invOf_left`

English:
theorem Commute.invOf_left
  given: [Monoid α] {a b : α} [Invertible b] (h : Commute b a)
  proof: calc
    ⅟b * a = ⅟b * (a * b * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (b * a * ⅟b) := by rw [h.eq]
    _ = a * ⅟b := by simp [mul_assoc]

中文:
定理 Commute.invOf_left
  条件: [幺半群 α] {a b : α} [可逆 b] (h : Commute b a)
  证明: calc
    ⅟b * a = ⅟b * (a * b * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (b * a * ⅟b) := by rw [h.eq]
    _ = a * ⅟b := by simp [mul_assoc]

Depends on / 依赖: h.eq, mul_assoc
-/
theorem Commute.invOf_left [Monoid α] {a b : α} [Invertible b] (h : Commute b a) :
    Commute (⅟b) a :=
  calc
    ⅟b * a = ⅟b * (a * b * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (b * a * ⅟b) := by rw [h.eq]
    _ = a * ⅟b := by simp [mul_assoc]

/--
theorem `commute_invOf` / 定理 `commute_invOf`

English:
theorem commute_invOf
  given: {M : Type*} [One M] [Mul M] (m : M) [Invertible m]
  statement: Commute m (⅟m)
  proof: calc
    m * ⅟m = 1 := mul_invOf_self m
    _ = ⅟m * m := (invOf_mul_self m).symm

中文:
定理 commute_invOf
  条件: {M : 类型} [幺 M] [乘法 M] (m : M) [可逆 m]
  结论: Commute m (⅟m)
  证明: calc
    m * ⅟m = 1 := mul_invOf_self m
    _ = ⅟m * m := (invOf_mul_self m).symm

Depends on / 依赖: invOf_mul_self, mul_invOf_self
-/
theorem commute_invOf {M : Type*} [One M] [Mul M] (m : M) [Invertible m] : Commute m (⅟m) :=
  calc
    m * ⅟m = 1 := mul_invOf_self m
    _ = ⅟m * m := (invOf_mul_self m).symm

section Monoid

variable [Monoid α]

/--
Definition of `invertibleOfInvertibleMul` / `invertibleOfInvertibleMul` 的定义

English:
abbreviation invertibleOfInvertibleMul
  signature: (a b : α) [Invertible a] [Invertible (a * b)]
  body: ⅟(a * b) * a
  invOf_mul_self := by rw [mul_assoc, invOf_mul_self]
  mul_invOf_self := by
    rw [← (isUnit_of_invertible a).mul_right_inj]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_invOf_self]; rw [mul_one]; rw [one_mul]

中文:
缩写 invertibleOfInvertibleMul
  签名: (a b : α) [可逆 a] [可逆 (a * b)]
  定义体: ⅟(a * b) * a
  invOf_mul_self := by rw [mul_assoc, invOf_mul_self]
  mul_invOf_self := by
    rw [← (isUnit_of_invertible a).mul_right_inj]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_invOf_self]; rw [mul_one]; rw [one_mul]
-/
abbrev invertibleOfInvertibleMul (a b : α) [Invertible a] [Invertible (a * b)] : Invertible b where
  invOf := ⅟(a * b) * a
  invOf_mul_self := by rw [mul_assoc, invOf_mul_self]
  mul_invOf_self := by
    rw [← (isUnit_of_invertible a).mul_right_inj]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_invOf_self]; rw [mul_one]; rw [one_mul]

/--
Definition of `invertibleOfMulInvertible` / `invertibleOfMulInvertible` 的定义

English:
abbreviation invertibleOfMulInvertible
  signature: (a b : α) [Invertible (a * b)] [Invertible b]
  body: b * ⅟(a * b)
  invOf_mul_self := by
    rw [← (isUnit_of_invertible b).mul_left_inj]; rw [mul_assoc]; rw [mul_assoc]; rw [invOf_mul_self]; rw [mul_one]; rw [one_mul]
  mul_invOf_self := by rw [← mul_assoc, mul_invOf_self]

中文:
缩写 invertibleOfMulInvertible
  签名: (a b : α) [可逆 (a * b)] [可逆 b]
  定义体: b * ⅟(a * b)
  invOf_mul_self := by
    rw [← (isUnit_of_invertible b).mul_left_inj]; rw [mul_assoc]; rw [mul_assoc]; rw [invOf_mul_self]; rw [mul_one]; rw [one_mul]
  mul_invOf_self := by rw [← mul_assoc, mul_invOf_self]
-/
abbrev invertibleOfMulInvertible (a b : α) [Invertible (a * b)] [Invertible b] : Invertible a where
  invOf := b * ⅟(a * b)
  invOf_mul_self := by
    rw [← (isUnit_of_invertible b).mul_left_inj]; rw [mul_assoc]; rw [mul_assoc]; rw [invOf_mul_self]; rw [mul_one]; rw [one_mul]
  mul_invOf_self := by rw [← mul_assoc, mul_invOf_self]

/-- `invertibleOfInvertibleMul` and `invertibleMul` as an equivalence. -/
@[simps apply symm_apply]
/--
Definition of `Invertible.mulLeft` / `Invertible.mulLeft` 的定义

English:
definition Invertible.mulLeft
  signature: {a : α} (_ : Invertible a) (b : α)
  body: invertibleMul a b
  invFun _ := invertibleOfInvertibleMul a _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 可逆.mulLeft
  签名: {a : α} (_ : 可逆 a) (b : α)
  定义体: invertibleMul a b
  invFun _ := invertibleOfInvertibleMul a _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: invertibleMul
-/
def Invertible.mulLeft {a : α} (_ : Invertible a) (b : α) : Invertible b ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfInvertibleMul a _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- `invertibleOfMulInvertible` and `invertibleMul` as an equivalence. -/
@[simps apply symm_apply]
/--
Definition of `Invertible.mulRight` / `Invertible.mulRight` 的定义

English:
definition Invertible.mulRight
  signature: (a : α) {b : α} (_ : Invertible b)
  body: invertibleMul a b
  invFun _ := invertibleOfMulInvertible _ b
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 可逆.mulRight
  签名: (a : α) {b : α} (_ : 可逆 b)
  定义体: invertibleMul a b
  invFun _ := invertibleOfMulInvertible _ b
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: invertibleMul
-/
def Invertible.mulRight (a : α) {b : α} (_ : Invertible b) : Invertible a ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfMulInvertible _ b
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/--
Instance `invertiblePow` / 实例 `invertiblePow`

English:
instance invertiblePow
  signature: (m : α) [Invertible m] (n : Nat)
  body: ⅟m ^ n
  invOf_mul_self := by rw [← (commute_invOf m).symm.mul_pow, invOf_mul_self, one_pow]
  mul_invOf_self := by rw [← (commute_invOf m).mul_pow, mul_invOf_self, one_pow]

中文:
实例 invertiblePow
  签名: (m : α) [可逆 m] (n : 自然数)
  定义体: ⅟m ^ n
  invOf_mul_self := by rw [← (commute_invOf m).symm.mul_pow, invOf_mul_self, one_pow]
  mul_invOf_self := by rw [← (commute_invOf m).mul_pow, mul_invOf_self, one_pow]
-/
instance invertiblePow (m : α) [Invertible m] (n : Nat) : Invertible (m ^ n) where
  invOf := ⅟m ^ n
  invOf_mul_self := by rw [← (commute_invOf m).symm.mul_pow, invOf_mul_self, one_pow]
  mul_invOf_self := by rw [← (commute_invOf m).mul_pow, mul_invOf_self, one_pow]

/--
lemma `invOf_pow` / 引理 `invOf_pow`

English:
lemma invOf_pow
  given: (m : α) [Invertible m] (n : Nat) [Invertible (m ^ n)]
  statement: ⅟(m ^ n) = ⅟m ^ n
  proof: @invertible_unique _ _ _ _ _ (invertiblePow m n) rfl

中文:
引理 invOf_pow
  条件: (m : α) [可逆 m] (n : 自然数) [可逆 (m ^ n)]
  结论: ⅟(m ^ n) = ⅟m ^ n
  证明: @invertible_unique _ _ _ _ _ (invertiblePow m n) rfl

Depends on / 依赖: invertiblePow, invertible_unique
-/
lemma invOf_pow (m : α) [Invertible m] (n : Nat) [Invertible (m ^ n)] : ⅟(m ^ n) = ⅟m ^ n :=
  @invertible_unique _ _ _ _ _ (invertiblePow m n) rfl

/-- If `x ^ n = 1` then `x` has an inverse, `x^(n - 1)`. -/
@[instance_reducible]
/--
Definition of `invertibleOfPowEqOne` / `invertibleOfPowEqOne` 的定义

English:
definition invertibleOfPowEqOne
  signature: (x : α) (n : Nat) (hx : x ^ n = 1) (hn : n != 0)
  body: inferInstanceAs Invertible (Units.ofPowEqOne x n hx hn : α)

中文:
定义 invertibleOfPowEqOne
  签名: (x : α) (n : 自然数) (hx : x ^ n = 1) (hn : n != 0)
  定义体: inferInstanceAs Invertible (Units.ofPowEqOne x n hx hn : α)

Depends on / 依赖: Invertible, Units.ofPowEqOne, ofPowEqOne
-/
def invertibleOfPowEqOne (x : α) (n : Nat) (hx : x ^ n = 1) (hn : n != 0) : Invertible x :=
inferInstanceAs Invertible (Units.ofPowEqOne x n hx hn : α)

end Monoid


/-- Monoid homs preserve invertibility. -/
@[instance_reducible]
/--
Definition of `Invertible.map` / `Invertible.map` 的定义

English:
definition Invertible.map
  signature: {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [MulOneClass S]
  body: f (⅟r)
  invOf_mul_self := by rw [← map_mul, invOf_mul_self, map_one]
  mul_invOf_self := by rw [← map_mul, mul_invOf_self, map_one]

中文:
定义 可逆.map
  签名: {R : 类型} {S : 类型} {F : 类型} [MulOne类 R] [MulOne类 S]
  定义体: f (⅟r)
  invOf_mul_self := by rw [← map_mul, invOf_mul_self, map_one]
  mul_invOf_self := by rw [← map_mul, mul_invOf_self, map_one]
-/
def Invertible.map {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [MulOneClass S]
    [FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] :
    Invertible (f r) where
  invOf := f (⅟r)
  invOf_mul_self := by rw [← map_mul, invOf_mul_self, map_one]
  mul_invOf_self := by rw [← map_mul, mul_invOf_self, map_one]

/--
theorem `map_invOf` / 定理 `map_invOf`

English:
theorem map_invOf
  statement: {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [Monoid S]
  proof: by
  obtain rfl : ifr = Invertible.map f r := Subsingleton.elim _ _; rfl

中文:
定理 map_invOf
  结论: {R : 类型} {S : 类型} {F : 类型} [MulOne类 R] [幺半群 S]
  证明: by
  obtain rfl : ifr = Invertible.map f r := Subsingleton.elim _ _; rfl

Depends on / 依赖: Invertible, Invertible.map, Subsingleton, Subsingleton.elim
-/
theorem map_invOf {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [Monoid S]
    [FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R)
    [Invertible r] [ifr : Invertible (f r)] :
    f (⅟r) = ⅟(f r) := by
  obtain rfl : ifr = Invertible.map f r := Subsingleton.elim _ _; rfl

/-- If a function `f : R → S` has a left-inverse that is a monoid hom,
  then `r : R` is invertible if `f r` is.

The inverse is computed as `g (⅟(f r))` -/
@[simps! -isSimp, instance_reducible]
/--
Definition of `Invertible.ofLeftInverse` / `Invertible.ofLeftInverse` 的定义

English:
definition Invertible.ofLeftInverse
  signature: {R : Type*} {S : Type*} {G : Type*} [MulOneClass R] [MulOneClass S]
  body: (Invertible.map g (f r)).copy _ (h r).symm

中文:
定义 可逆.ofLeftInverse
  签名: {R : 类型} {S : 类型} {G : 类型} [MulOne类 R] [MulOne类 S]
  定义体: (Invertible.map g (f r)).copy _ (h r).symm

Depends on / 依赖: Invertible, Invertible.map
-/
def Invertible.ofLeftInverse {R : Type*} {S : Type*} {G : Type*} [MulOneClass R] [MulOneClass S]
    [FunLike G S R] [MonoidHomClass G S R] (f : R -> S) (g : G) (r : R)
    (h : Function.LeftInverse g f) [Invertible (f r)] : Invertible r :=
  (Invertible.map g (f r)).copy _ (h r).symm

/-- Invertibility on either side of a monoid hom with a left-inverse is equivalent. -/
@[simps]
/--
Definition of `invertibleEquivOfLeftInverse` / `invertibleEquivOfLeftInverse` 的定义

English:
definition invertibleEquivOfLeftInverse
  signature: {R : Type*} {S : Type*} {F G : Type*} [Monoid R] [Monoid S]
  body: Invertible.ofLeftInverse f _ _ h
  invFun _ := Invertible.map f _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 invertibleEquivOfLeftInverse
  签名: {R : 类型} {S : 类型} {F G : 类型} [幺半群 R] [幺半群 S]
  定义体: Invertible.ofLeftInverse f _ _ h
  invFun _ := Invertible.map f _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: Invertible, Invertible.ofLeftInverse, ofLeftInverse
-/
def invertibleEquivOfLeftInverse {R : Type*} {S : Type*} {F G : Type*} [Monoid R] [Monoid S]
    [FunLike F R S] [MonoidHomClass F R S] [FunLike G S R] [MonoidHomClass G S R]
    (f : F) (g : G) (r : R) (h : Function.LeftInverse g f) : Invertible (f r) ≃ Invertible r where
  toFun _ := Invertible.ofLeftInverse f _ _ h
  invFun _ := Invertible.map f _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
