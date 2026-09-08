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
/-
**unitOfInvertible** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：unitOfInvertible [Monoid α] (a : α) [Invertible a] : αˣ where val
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `Invertible` element is a unit.
-/
def unitOfInvertible [Monoid α] (a : α) [Invertible a] : αˣ where
  val := a
  inv := ⅟a
  val_inv := by simp
  inv_val := by simp
/-
**isUnit_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_of_invertible [Monoid α] (a : α) [Invertible a] : IsUnit a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isUnit_of_invertible [Monoid α] (a : α) [Invertible a] : IsUnit a :=
  ⟨unitOfInvertible a, rfl⟩

/-- Units are invertible in their associated monoid. -/
/-
**Units.invertible** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Units.invertible [Monoid α] (u : αˣ) : Invertible (u : α) where invOf
参数：u : αˣ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1

--- 原说明 ---
Units are invertible in their associated monoid.
-/
instance Units.invertible [Monoid α] (u : αˣ) :
    Invertible (u : α) where
  invOf := ↑u⁻¹
  invOf_mul_self := u.inv_mul
  mul_invOf_self := u.mul_inv

@[simp]
/-
**invOf_units** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟(u : α) = ↑u⁻¹
参数：u : αˣ；u : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_eq_right_inv`：invOf_eq_right_inv [Invertible a] (hac : a * b = 1) 
: ⅟a = b
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
theorem invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟(u : α) = ↑u⁻¹ :=
  invOf_eq_right_inv u.mul_inv
/-
**IsUnit.nonempty_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.nonempty_invertible [Monoid α] {a : α} (h : IsUnit a) : Nonempty (I
nvertible a)
参数：h : IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsUnit.nonempty_invertible [Monoid α] {a : α} (h : IsUnit a) : Nonempty (Invertible a) :=
  let ⟨x, hx⟩ := h
  ⟨x.invertible.copy _ hx.symm⟩

/-- Convert `IsUnit` to `Invertible` using `Classical.choice`.

Prefer `casesI h.nonempty_invertible` over `letI := h.invertible` if you want to avoid choice. -/
@[instance_reducible]
/-
**IsUnit.invertible** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsUnit.invertible [Monoid α] {a : α} (h : IsUnit a) : Invertible a
参数：h : IsUnit a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)

--- 原说明 ---
Convert `IsUnit` to `Invertible` using `Classical.choice`.

Prefer `casesI h.nonempty_invertible` over `letI := h.invertible` if you want to
 avoid choice.
-/
noncomputable def IsUnit.invertible [Monoid α] {a : α} (h : IsUnit a) : Invertible a :=
  Classical.choice h.nonempty_invertible

@[simp]
/-
**nonempty_invertible_iff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_invertible_iff_isUnit [Monoid α] (a : α) : Nonempty (Invertible a
) ↔ IsUnit a
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
-/
theorem nonempty_invertible_iff_isUnit [Monoid α] (a : α) : Nonempty (Invertible a) ↔ IsUnit a :=
  ⟨Nonempty.rec <| @isUnit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩
/-
**Commute.invOf_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.invOf_right [Monoid α] {a b : α} [Invertible b] (h : Commute a b) 
: Commute a (⅟b)
参数：h : Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `invOf_mul_cancel_left'`：invOf_mul_cancel_left' {_ : Invertible a} : ⅟a *
 (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Commute.invOf_right [Monoid α] {a b : α} [Invertible b] (h : Commute a b) :
    Commute a (⅟b) :=
  calc
    a * ⅟b = ⅟b * (b * a * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (a * b * ⅟b) := by rw [h.eq]
    _ = ⅟b * a := by simp [mul_assoc]
/-
**Commute.invOf_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.invOf_left [Monoid α] {a b : α} [Invertible b] (h : Commute b a) :
 Commute (⅟b) a
参数：h : Commute b a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `invOf_mul_cancel_left'`：invOf_mul_cancel_left' {_ : Invertible a} : ⅟a *
 (a * b) = b
-/
theorem Commute.invOf_left [Monoid α] {a b : α} [Invertible b] (h : Commute b a) :
    Commute (⅟b) a :=
  calc
    ⅟b * a = ⅟b * (a * b * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (b * a * ⅟b) := by rw [h.eq]
    _ = a * ⅟b := by simp [mul_assoc]
/-
**commute_invOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_invOf {M : Type*} [One M] [Mul M] (m : M) [Invertible m] : Commute
 m (⅟m)
参数：m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
-/
theorem commute_invOf {M : Type*} [One M] [Mul M] (m : M) [Invertible m] : Commute m (⅟m) :=
  calc
    m * ⅟m = 1 := mul_invOf_self m
    _ = ⅟m * m := (invOf_mul_self m).symm

section Monoid

variable [Monoid α]

/-- This is the `Invertible` version of `Units.isUnit_units_mul` -/
/-
**invertibleOfInvertibleMul** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：invertibleOfInvertibleMul (a b : α) [Invertible a] [Invertible (a * b)] : 
Invertible b where invOf
参数：a b : α；a * b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `Invertible` version of `Units.isUnit_units_mul`
-/
abbrev invertibleOfInvertibleMul (a b : α) [Invertible a] [Invertible (a * b)] : Invertible b where
  invOf := ⅟(a * b) * a
  invOf_mul_self := by rw [mul_assoc, invOf_mul_self]
  mul_invOf_self := by
    rw [← (isUnit_of_invertible a).mul_right_inj, ← mul_assoc, ← mul_assoc, mul_invOf_self, mul_one,
      one_mul]

/-- This is the `Invertible` version of `Units.isUnit_mul_units` -/
/-
**invertibleOfMulInvertible** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：invertibleOfMulInvertible (a b : α) [Invertible (a * b)] [Invertible b] : 
Invertible a where invOf
参数：a b : α；a * b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `Invertible` version of `Units.isUnit_mul_units`
-/
abbrev invertibleOfMulInvertible (a b : α) [Invertible (a * b)] [Invertible b] : Invertible a where
  invOf := b * ⅟(a * b)
  invOf_mul_self := by
    rw [← (isUnit_of_invertible b).mul_left_inj, mul_assoc, mul_assoc, invOf_mul_self, mul_one,
      one_mul]
  mul_invOf_self := by rw [← mul_assoc, mul_invOf_self]

/-- `invertibleOfInvertibleMul` and `invertibleMul` as an equivalence. -/
@[simps apply symm_apply]
/-
**Invertible.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Invertible.mulLeft {a : α} (_ : Invertible a) (b : α) : Invertible b ≃ Inv
ertible (a * b) where toFun _
参数：_ : Invertible a；b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`invertibleOfInvertibleMul` and `invertibleMul` as an equivalence.
-/
def Invertible.mulLeft {a : α} (_ : Invertible a) (b : α) : Invertible b ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfInvertibleMul a _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- `invertibleOfMulInvertible` and `invertibleMul` as an equivalence. -/
@[simps apply symm_apply]
/-
**Invertible.mulRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Invertible.mulRight (a : α) {b : α} (_ : Invertible b) : Invertible a ≃ In
vertible (a * b) where toFun _
参数：a : α；_ : Invertible b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`invertibleOfMulInvertible` and `invertibleMul` as an equivalence.
-/
def Invertible.mulRight (a : α) {b : α} (_ : Invertible b) : Invertible a ≃ Invertible (a * b) where
  toFun _ := invertibleMul a b
  invFun _ := invertibleOfMulInvertible _ b
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
/-
**invertiblePow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：invertiblePow (m : α) [Invertible m] (n : Nat) : Invertible (m ^ n) where 
invOf
参数：m : α；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance invertiblePow (m : α) [Invertible m] (n : ℕ) : Invertible (m ^ n) where
  invOf := ⅟m ^ n
  invOf_mul_self := by rw [← (commute_invOf m).symm.mul_pow, invOf_mul_self, one_pow]
  mul_invOf_self := by rw [← (commute_invOf m).mul_pow, mul_invOf_self, one_pow]
/-
**invOf_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：invOf_pow (m : α) [Invertible m] (n : Nat) [Invertible (m ^ n)] : ⅟(m ^ n)
 = ⅟m ^ n
参数：m : α；n : Nat；m ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invertible_unique`：invertible_unique [Invertible a] [Invertible b] (h : 
a = b) : ⅟a = ⅟b
-/
lemma invOf_pow (m : α) [Invertible m] (n : ℕ) [Invertible (m ^ n)] : ⅟(m ^ n) = ⅟m ^ n :=
  @invertible_unique _ _ _ _ _ (invertiblePow m n) rfl

/-- If `x ^ n = 1` then `x` has an inverse, `x^(n - 1)`. -/
@[instance_reducible]
/-
**invertibleOfPowEqOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleOfPowEqOne (x : α) (n : Nat) (hx : x ^ n = 1) (hn : n != 0) : In
vertible x
参数：x : α；n : Nat；hx : x ^ n = 1；hn : n != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x ^ n = 1` then `x` has an inverse, `x^(n - 1)`.
-/
def invertibleOfPowEqOne (x : α) (n : ℕ) (hx : x ^ n = 1) (hn : n ≠ 0) : Invertible x :=
  inferInstanceAs <| Invertible (Units.ofPowEqOne x n hx hn : α)

end Monoid


/-- Monoid homs preserve invertibility. -/
@[instance_reducible]
/-
**Invertible.map** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Invertible.map {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [MulOne
Class S] [FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] :
 Invertible (f r) where invOf
参数：f : F；r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monoid homs preserve invertibility.
-/
def Invertible.map {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [MulOneClass S]
    [FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] :
    Invertible (f r) where
  invOf := f (⅟r)
  invOf_mul_self := by rw [← map_mul, invOf_mul_self, map_one]
  mul_invOf_self := by rw [← map_mul, mul_invOf_self, map_one]

/-- Note that the `Invertible (f r)` argument can be satisfied by using `letI := Invertible.map f r`
before applying this lemma. -/
/-
**map_invOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_invOf {R : Type*} {S : Type*} {F : Type*} [MulOneClass R] [Monoid S] [
FunLike F R S] [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] [ifr : Inve
rtible (f r)] : f (⅟r) = ⅟(f r)
参数：f : F；r : R；f r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
Note that the `Invertible (f r)` argument can be satisfied by using `letI := Inv
ertible.map f r`
before applying this lemma.
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
/-
**Invertible.ofLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Invertible.ofLeftInverse {R : Type*} {S : Type*} {G : Type*} [MulOneClass 
R] [MulOneClass S] [FunLike G S R] [MonoidHomClass G S R] (f : R -> S) (g : G) (
r : R) (h : Function.LeftInverse g f) [Invertible (f r)] : Invertible r
参数：f : R -> S；g : G；r : R；h : Function.LeftInverse g f；f r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `f : R → S` has a left-inverse that is a monoid hom,
  then `r : R` is invertible if `f r` is.

The inverse is computed as `g (⅟(f r))`
-/
def Invertible.ofLeftInverse {R : Type*} {S : Type*} {G : Type*} [MulOneClass R] [MulOneClass S]
    [FunLike G S R] [MonoidHomClass G S R] (f : R → S) (g : G) (r : R)
    (h : Function.LeftInverse g f) [Invertible (f r)] : Invertible r :=
  (Invertible.map g (f r)).copy _ (h r).symm

/-- Invertibility on either side of a monoid hom with a left-inverse is equivalent. -/
@[simps]
/-
**invertibleEquivOfLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleEquivOfLeftInverse {R : Type*} {S : Type*} {F G : Type*} [Monoid
 R] [Monoid S] [FunLike F R S] [MonoidHomClass F R S] [FunLike G S R] [MonoidHom
Class G S R] (f : F) (g : G) (r : R) (h : Function.LeftInverse g f) : Invertible
 (f r) ≃ Invertible r where toFun _
参数：f : F；g : G；r : R；h : Function.LeftInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Invertibility on either side of a monoid hom with a left-inverse is equivalent.
-/
def invertibleEquivOfLeftInverse {R : Type*} {S : Type*} {F G : Type*} [Monoid R] [Monoid S]
    [FunLike F R S] [MonoidHomClass F R S] [FunLike G S R] [MonoidHomClass G S R]
    (f : F) (g : G) (r : R) (h : Function.LeftInverse g f) : Invertible (f r) ≃ Invertible r where
  toFun _ := Invertible.ofLeftInverse f _ _ h
  invFun _ := Invertible.map f _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
