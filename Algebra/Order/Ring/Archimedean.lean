/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Algebra.Order.Group.DenselyOrdered
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Archimedean classes of a linearly ordered ring

The archimedean classes of a linearly ordered ring can be given the structure of an `AddCommMonoid`,
by defining

* `0 = mk 1`
* `mk x + mk y = mk (x * y)`

For a linearly ordered field, we can define a negative as

* `-mk x = mk x⁻¹`

which turns them into a `LinearOrderedAddCommGroupWithTop`.

## Implementation notes

We give Archimedean class an additive structure, rather than a multiplicative one, for the following
reasons:

* In the ring version of Hahn embedding theorem, the subtype `FiniteArchimedeanClass R` of non-top
  elements in `ArchimedeanClass R` naturally becomes the additive abelian group for the ring
  `ℝ⟦FiniteArchimedeanClass R⟧`.
* The order we defined on `ArchimedeanClass R` matches the order on `AddValuation`, rather than the
  one on `Valuation`.
-/

@[expose] public section

variable {R S : Type*} [LinearOrder R] [LinearOrder S]

namespace ArchimedeanClass
section Ring
variable [CommRing R]

section IsOrderedRing
variable [IsStrictOrderedRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (ArchimedeanClass R)
  body: mk 1

中文:
实例 :
  签名: 零 (ArchimedeanClass R)
  定义体: mk 1
-/
instance : Zero (ArchimedeanClass R) where
  zero := mk 1

/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  statement: mk (1 : R) = 0
  proof: rfl

中文:
定理 mk_one
  结论: mk (1 : R) = 0
  证明: rfl
-/
@[simp] theorem mk_one : mk (1 : R) = 0 := rfl

/--
lemma `top_ne_zero` / 引理 `top_ne_zero`

English:
lemma top_ne_zero
  statement: (⊤ : ArchimedeanClass R) != 0
  proof: by simp [← mk_one]

中文:
引理 top_ne_zero
  结论: (⊤ : ArchimedeanClass R) != 0
  证明: by simp [← mk_one]
-/
@[simp] lemma top_ne_zero : (⊤ : ArchimedeanClass R) != 0 := by simp [← mk_one]
/--
lemma `zero_ne_top` / 引理 `zero_ne_top`

English:
lemma zero_ne_top
  statement: 0 != (⊤ : ArchimedeanClass R)
  proof: top_ne_zero.symm

中文:
引理 zero_ne_top
  结论: 0 != (⊤ : ArchimedeanClass R)
  证明: top_ne_zero.symm
-/
@[simp] lemma zero_ne_top : 0 != (⊤ : ArchimedeanClass R) := top_ne_zero.symm

/--
theorem `mk_mul_le_of_le` / 定理 `mk_mul_le_of_le`

English:
theorem mk_mul_le_of_le
  given: {x₁ y₁ x₂ y₂ : R} (hx : mk x₁ <= mk x₂) (hy : mk y₁ <= mk y₂)
  proof: by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  use m * n
  convert mul_le_mul hm hn (abs_nonneg _) (nsmul_nonneg (abs_nonneg _) _) <;>
    simp_rw [ArchimedeanOrder.val_of, abs_mul]
  ring

中文:
定理 mk_mul_le_of_le
  条件: {x₁ y₁ x₂ y₂ : R} (hx : mk x₁ <= mk x₂) (hy : mk y₁ <= mk y₂)
  证明: by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  use m * n
  convert mul_le_mul hm hn (abs_nonneg _) (nsmul_nonneg (abs_nonneg _) _) <;>
    simp_rw [ArchimedeanOrder.val_of, abs_mul]
  ring
-/
private theorem mk_mul_le_of_le {x₁ y₁ x₂ y₂ : R} (hx : mk x₁ <= mk x₂) (hy : mk y₁ <= mk y₂) :
    mk (x₁ * y₁) <= mk (x₂ * y₂) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  use m * n
  convert mul_le_mul hm hn (abs_nonneg _) (nsmul_nonneg (abs_nonneg _) _) <;>
    simp_rw [ArchimedeanOrder.val_of, abs_mul]
  ring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (ArchimedeanClass R)
  body: lift₂ (fun x y => .mk <| x * y) fun _ _ _ _ hx hy => by
    exact (mk_mul_le_of_le hx.le hy.le).antisymm (mk_mul_le_of_le hx.ge hy.ge)

中文:
实例 :
  签名: 加法 (ArchimedeanClass R)
  定义体: lift₂ (fun x y => .mk <| x * y) fun _ _ _ _ hx hy => by
    exact (mk_mul_le_of_le hx.le hy.le).antisymm (mk_mul_le_of_le hx.ge hy.ge)

Depends on / 依赖: antisymm, hx.ge, hx.le, hy.ge, hy.le, mk_mul_le_of_le
-/
instance : Add (ArchimedeanClass R) where
  add := lift₂ (fun x y => .mk <| x * y) fun _ _ _ _ hx hy => by
    exact (mk_mul_le_of_le hx.le hy.le).antisymm (mk_mul_le_of_le hx.ge hy.ge)

/--
theorem `mk_mul` / 定理 `mk_mul`

English:
theorem mk_mul
  given: (x y : R)
  statement: mk (x * y) = mk x + mk y
  proof: rfl

中文:
定理 mk_mul
  条件: (x y : R)
  结论: mk (x * y) = mk x + mk y
  证明: rfl
-/
@[simp] theorem mk_mul (x y : R) : mk (x * y) = mk x + mk y := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (ArchimedeanClass R)
  body: lift (fun x => mk (x ^ n)) fun x y h => by
    induction n with
    | zero => simp
    | succ n IH => simp_rw [pow_succ, mk_mul, IH, h]

中文:
实例 :
  签名: 标量乘法 自然数 (ArchimedeanClass R)
  定义体: lift (fun x => mk (x ^ n)) fun x y h => by
    induction n with
    | zero => simp
    | succ n IH => simp_rw [pow_succ, mk_mul, IH, h]

Depends on / 依赖: mk_mul, pow_succ, simp_rw
-/
instance : SMul Nat (ArchimedeanClass R) where
  smul n := lift (fun x => mk (x ^ n)) fun x y h => by
    induction n with
    | zero => simp
    | succ n IH => simp_rw [pow_succ, mk_mul, IH, h]

/--
theorem `mk_pow` / 定理 `mk_pow`

English:
theorem mk_pow
  given: (n : Nat) (x : R)
  statement: mk (x ^ n) = n • mk x
  proof: rfl

中文:
定理 mk_pow
  条件: (n : 自然数) (x : R)
  结论: mk (x ^ n) = n • mk x
  证明: rfl
-/
@[simp] theorem mk_pow (n : Nat) (x : R) : mk (x ^ n) = n • mk x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMagma (ArchimedeanClass R)
  body: by
    induction x with | mk x
    induction y with | mk y
    rw [← mk_mul]; rw [mul_comm]; rw [mk_mul]

中文:
实例 :
  签名: 加法交换原群 (ArchimedeanClass R)
  定义体: by
    induction x with | mk x
    induction y with | mk y
    rw [← mk_mul]; rw [mul_comm]; rw [mk_mul]

Depends on / 依赖: mk_mul, mul_comm
-/
instance : AddCommMagma (ArchimedeanClass R) where
  add_comm x y := by
    induction x with | mk x
    induction y with | mk y
    rw [← mk_mul]; rw [mul_comm]; rw [mk_mul]

/--
theorem `zero_add'` / 定理 `zero_add'`

English:
theorem zero_add'
  given: (x : ArchimedeanClass R)
  statement: 0 + x = x
  proof: by
  induction x with | mk x
  rw [← mk_one]; rw [← mk_mul]; rw [one_mul]

中文:
定理 zero_add'
  条件: (x : ArchimedeanClass R)
  结论: 0 + x = x
  证明: by
  induction x with | mk x
  rw [← mk_one]; rw [← mk_mul]; rw [one_mul]
-/
private theorem zero_add' (x : ArchimedeanClass R) : 0 + x = x := by
  induction x with | mk x
  rw [← mk_one]; rw [← mk_mul]; rw [one_mul]

/--
theorem `add_assoc'` / 定理 `add_assoc'`

English:
theorem add_assoc'
  given: (x y z : ArchimedeanClass R)
  statement: x + y + z = x + (y + z)
  proof: by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  simp_rw [← mk_mul, mul_assoc]

中文:
定理 add_assoc'
  条件: (x y z : ArchimedeanClass R)
  结论: x + y + z = x + (y + z)
  证明: by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  simp_rw [← mk_mul, mul_assoc]
-/
private theorem add_assoc' (x y z : ArchimedeanClass R) : x + y + z = x + (y + z) := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  simp_rw [← mk_mul, mul_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (ArchimedeanClass R)
  body: private add_assoc'
  zero_add := private zero_add'
  add_zero x := private add_comm x _ ▸ zero_add' x
  nsmul_zero x := by induction x with | mk x => rw [← mk_pow, pow_zero, mk_one]
  nsmul_succ n x := by induction x with | mk x => rw [← mk_pow, pow_succ, mk_mul, mk_pow]

中文:
实例 :
  签名: 加法交换幺半群 (ArchimedeanClass R)
  定义体: private add_assoc'
  zero_add := private zero_add'
  add_zero x := private add_comm x _ ▸ zero_add' x
  nsmul_zero x := by induction x with | mk x => rw [← mk_pow, pow_zero, mk_one]
  nsmul_succ n x := by induction x with | mk x => rw [← mk_pow, pow_succ, mk_mul, mk_pow]

Depends on / 依赖: add_assoc, private
-/
instance : AddCommMonoid (ArchimedeanClass R) where
  add_assoc := private add_assoc'
  zero_add := private zero_add'
  add_zero x := private add_comm x _ ▸ zero_add' x
  nsmul_zero x := by induction x with | mk x => rw [← mk_pow, pow_zero, mk_one]
  nsmul_succ n x := by induction x with | mk x => rw [← mk_pow, pow_succ, mk_mul, mk_pow]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedAddMonoid (ArchimedeanClass R)
  body: by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    rw [← mk_mul]; rw [← mk_mul]
    exact mk_mul_le_of_le h le_rfl

中文:
实例 :
  签名: 是OrderedAdd幺半群 (ArchimedeanClass R)
  定义体: by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    rw [← mk_mul]; rw [← mk_mul]
    exact mk_mul_le_of_le h le_rfl

Depends on / 依赖: le_rfl, mk_mul, mk_mul_le_of_le
-/
instance : IsOrderedAddMonoid (ArchimedeanClass R) where
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    rw [← mk_mul]; rw [← mk_mul]
    exact mk_mul_le_of_le h le_rfl

/--
lemma `isAddRegular_mk` / 引理 `isAddRegular_mk`

English:
lemma isAddRegular_mk
  given: {x : R} (hx : x != 0)
  statement: IsAddRegular (mk x)
  proof: by
  rw [← isAddLeftRegular_iff_isAddRegular]
  rintro y z hyz
  induction y with | mk y =>
  induction z with | mk z =>
  simpa [← mk_mul, mk_eq_mk, mul_left_comm _ (|x|), abs_pos.2 hx] using hyz

中文:
引理 isAddRegular_mk
  条件: {x : R} (hx : x != 0)
  结论: 是加法正则 (mk x)
  证明: by
  rw [← isAddLeftRegular_iff_isAddRegular]
  rintro y z hyz
  induction y with | mk y =>
  induction z with | mk z =>
  simpa [← mk_mul, mk_eq_mk, mul_left_comm _ (|x|), abs_pos.2 hx] using hyz

Depends on / 依赖: abs_pos, isAddLeftRegular_iff_isAddRegular, mk_eq_mk, mk_mul, mul_left_comm
-/
lemma isAddRegular_mk {x : R} (hx : x != 0) : IsAddRegular (mk x) := by
  rw [← isAddLeftRegular_iff_isAddRegular]
  rintro y z hyz
  induction y with | mk y =>
  induction z with | mk z =>
  simpa [← mk_mul, mk_eq_mk, mul_left_comm _ (|x|), abs_pos.2 hx] using hyz

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedAddCommMonoidWithTop (ArchimedeanClass R)
  body: by induction x with | mk x => rw [← mk_zero, ← mk_mul, zero_mul]
  isAddLeftRegular_of_ne_top x := by induction x with | mk x => simp +contextual [isAddRegular_mk]

中文:
实例 :
  签名: LinearOrderedAddComm幺半群带顶 (ArchimedeanClass R)
  定义体: by induction x with | mk x => rw [← mk_zero, ← mk_mul, zero_mul]
  isAddLeftRegular_of_ne_top x := by induction x with | mk x => simp +contextual [isAddRegular_mk]

Depends on / 依赖: contextual, isAddLeftRegular_of_ne_top, isAddRegular_mk, mk_mul, mk_zero, zero_mul
-/
noncomputable instance : LinearOrderedAddCommMonoidWithTop (ArchimedeanClass R) where
  top_add' x := by induction x with | mk x => rw [← mk_zero, ← mk_mul, zero_mul]
  isAddLeftRegular_of_ne_top x := by induction x with | mk x => simp +contextual [isAddRegular_mk]

variable (R) in
/--
Definition of `addValuation` / `addValuation` 的定义

English:
definition addValuation
  signature: : AddValuation R (ArchimedeanClass R)
  body: AddValuation.of mk
  rfl rfl min_le_mk_add mk_mul

中文:
定义 addValuation
  签名: : AddValuation R (ArchimedeanClass R)
  定义体: AddValuation.of mk
  rfl rfl min_le_mk_add mk_mul

Depends on / 依赖: AddValuation, AddValuation.of
-/
noncomputable def addValuation : AddValuation R (ArchimedeanClass R) := AddValuation.of mk
  rfl rfl min_le_mk_add mk_mul

/--
theorem `addValuation_apply` / 定理 `addValuation_apply`

English:
theorem addValuation_apply
  given: (a : R)
  statement: addValuation R a = mk a
  proof: rfl

中文:
定理 addValuation_apply
  条件: (a : R)
  结论: addValuation R a = mk a
  证明: rfl
-/
@[simp] theorem addValuation_apply (a : R) : addValuation R a = mk a := rfl

variable {S : Type*} [LinearOrder S] [CommRing S] [IsStrictOrderedRing S]

@[simp]
/--
theorem `orderHom_zero` / 定理 `orderHom_zero`

English:
theorem orderHom_zero
  given: (f : S ->+o R)
  statement: orderHom f 0 = mk (f 1)
  proof: by
  rw [← mk_one]; rw [orderHom_mk]

@[simp]

中文:
定理 orderHom_zero
  条件: (f : S ->+o R)
  结论: orderHom f 0 = mk (f 1)
  证明: by
  rw [← mk_one]; rw [orderHom_mk]

@[simp]

Depends on / 依赖: mk_one, orderHom_mk
-/
theorem orderHom_zero (f : S ->+o R) : orderHom f 0 = mk (f 1) := by
  rw [← mk_one]; rw [orderHom_mk]

@[simp]
/--
theorem `mk_eq_zero_of_archimedean` / 定理 `mk_eq_zero_of_archimedean`

English:
theorem mk_eq_zero_of_archimedean
  given: [Archimedean S] {x : S} (h : x != 0)
  statement: mk x = 0
  proof: mk_eq_mk_of_archimedean h one_ne_zero

中文:
定理 mk_eq_zero_of_archimedean
  条件: [阿基米德 S] {x : S} (h : x != 0)
  结论: mk x = 0
  证明: mk_eq_mk_of_archimedean h one_ne_zero

Depends on / 依赖: mk_eq_mk_of_archimedean, one_ne_zero
-/
theorem mk_eq_zero_of_archimedean [Archimedean S] {x : S} (h : x != 0) : mk x = 0 :=
  mk_eq_mk_of_archimedean h one_ne_zero

/--
theorem `eq_zero_or_top_of_archimedean` / 定理 `eq_zero_or_top_of_archimedean`

English:
theorem eq_zero_or_top_of_archimedean
  given: [Archimedean S] (x : ArchimedeanClass S)
  statement: x = 0 ∨ x = ⊤
  proof: by
  induction x with | mk x
  obtain rfl | h := eq_or_ne x 0 <;> simp_all

中文:
定理 eq_zero_or_top_of_archimedean
  条件: [阿基米德 S] (x : ArchimedeanClass S)
  结论: x = 0 ∨ x = ⊤
  证明: by
  induction x with | mk x
  obtain rfl | h := eq_or_ne x 0 <;> simp_all

Depends on / 依赖: eq_or_ne
-/
theorem eq_zero_or_top_of_archimedean [Archimedean S] (x : ArchimedeanClass S) : x = 0 ∨ x = ⊤ := by
  induction x with | mk x
  obtain rfl | h := eq_or_ne x 0 <;> simp_all

/--
theorem `mk_map_of_archimedean` / 定理 `mk_map_of_archimedean`

English:
theorem mk_map_of_archimedean
  given: [Archimedean S] (f : S ->+o R) {x : S} (h : x != 0)
  proof: by
  rw [← orderHom_mk]; rw [mk_eq_zero_of_archimedean h]; rw [orderHom_zero]

中文:
定理 mk_map_of_archimedean
  条件: [阿基米德 S] (f : S ->+o R) {x : S} (h : x != 0)
  证明: by
  rw [← orderHom_mk]; rw [mk_eq_zero_of_archimedean h]; rw [orderHom_zero]

Depends on / 依赖: mk_eq_zero_of_archimedean, orderHom_mk, orderHom_zero
-/
theorem mk_map_of_archimedean [Archimedean S] (f : S ->+o R) {x : S} (h : x != 0) :
    mk (f x) = mk (f 1) := by
  rw [← orderHom_mk]; rw [mk_eq_zero_of_archimedean h]; rw [orderHom_zero]

/--
theorem `mk_map_of_archimedean'` / 定理 `mk_map_of_archimedean'`

English:
theorem mk_map_of_archimedean'
  given: [Archimedean S] (f : S ->+*o R) {x : S} (h : x != 0)
  proof: by
  simpa using mk_map_of_archimedean f.toOrderAddMonoidHom h

中文:
定理 mk_map_of_archimedean'
  条件: [阿基米德 S] (f : S ->+*o R) {x : S} (h : x != 0)
  证明: by
  simpa using mk_map_of_archimedean f.toOrderAddMonoidHom h

Depends on / 依赖: f.toOrderAddMonoidHom, mk_map_of_archimedean, toOrderAddMonoidHom
-/
theorem mk_map_of_archimedean' [Archimedean S] (f : S ->+*o R) {x : S} (h : x != 0) :
    mk (f x) = 0 := by
  simpa using mk_map_of_archimedean f.toOrderAddMonoidHom h

/--
theorem `mk_le_mk_add_of_archimedean` / 定理 `mk_le_mk_add_of_archimedean`

English:
theorem mk_le_mk_add_of_archimedean
  given: [Archimedean S] (f : S ->+*o R) (x : R) (y : S)
  proof: by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [mk_map_of_archimedean' f hy, zero_add]

中文:
定理 mk_le_mk_add_of_archimedean
  条件: [阿基米德 S] (f : S ->+*o R) (x : R) (y : S)
  证明: by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [mk_map_of_archimedean' f hy, zero_add]

Depends on / 依赖: eq_or_ne, mk_map_of_archimedean, zero_add
-/
theorem mk_le_mk_add_of_archimedean [Archimedean S] (f : S ->+*o R) (x : R) (y : S) :
    mk x <= mk (f y) + mk x := by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [mk_map_of_archimedean' f hy, zero_add]

/--
theorem `mk_le_add_mk_of_archimedean` / 定理 `mk_le_add_mk_of_archimedean`

English:
theorem mk_le_add_mk_of_archimedean
  given: [Archimedean S] (f : S ->+*o R) (x : R) (y : S)
  proof: by
  rw [add_comm]
  exact mk_le_mk_add_of_archimedean f x y

中文:
定理 mk_le_add_mk_of_archimedean
  条件: [阿基米德 S] (f : S ->+*o R) (x : R) (y : S)
  证明: by
  rw [add_comm]
  exact mk_le_mk_add_of_archimedean f x y

Depends on / 依赖: add_comm, mk_le_mk_add_of_archimedean
-/
theorem mk_le_add_mk_of_archimedean [Archimedean S] (f : S ->+*o R) (x : R) (y : S) :
    mk x <= mk x + mk (f y) := by
  rw [add_comm]
  exact mk_le_mk_add_of_archimedean f x y

/--
theorem `mk_map_nonneg_of_archimedean` / 定理 `mk_map_nonneg_of_archimedean`

English:
theorem mk_map_nonneg_of_archimedean
  given: [Archimedean S] (f : S ->+*o R) (y : S)
  statement: 0 <= mk (f y)
  proof: by
  simpa using mk_le_mk_add_of_archimedean f 1 y

中文:
定理 mk_map_nonneg_of_archimedean
  条件: [阿基米德 S] (f : S ->+*o R) (y : S)
  结论: 0 <= mk (f y)
  证明: by
  simpa using mk_le_mk_add_of_archimedean f 1 y

Depends on / 依赖: mk_le_mk_add_of_archimedean
-/
theorem mk_map_nonneg_of_archimedean [Archimedean S] (f : S ->+*o R) (y : S) : 0 <= mk (f y) := by
  simpa using mk_le_mk_add_of_archimedean f 1 y

/--
theorem `lt_of_pos_of_archimedean` / 定理 `lt_of_pos_of_archimedean`

English:
theorem lt_of_pos_of_archimedean
  statement: [Archimedean S] (f : S ->+*o R)
  proof: by
  apply lt_of_mk_lt_mk_of_nonneg
  · rwa [mk_map_of_archimedean' f hy.ne']
  · simpa using f.monotone' hy.le

中文:
定理 lt_of_pos_of_archimedean
  结论: [阿基米德 S] (f : S ->+*o R)
  证明: by
  apply lt_of_mk_lt_mk_of_nonneg
  · rwa [mk_map_of_archimedean' f hy.ne']
  · simpa using f.monotone' hy.le

Depends on / 依赖: f.monotone, hy.le, hy.ne, lt_of_mk_lt_mk_of_nonneg, mk_map_of_archimedean, monotone
-/
theorem lt_of_pos_of_archimedean [Archimedean S] (f : S ->+*o R)
    {x : R} (hx : 0 < mk x) {y : S} (hy : 0 < y) : x < f y := by
  apply lt_of_mk_lt_mk_of_nonneg
  · rwa [mk_map_of_archimedean' f hy.ne']
  · simpa using f.monotone' hy.le

/--
theorem `lt_of_neg_of_archimedean` / 定理 `lt_of_neg_of_archimedean`

English:
theorem lt_of_neg_of_archimedean
  statement: [Archimedean S] (f : S ->+*o R)
  proof: by
  apply lt_of_mk_lt_mk_of_nonpos
  · rwa [mk_map_of_archimedean' f hy.ne]
  · simpa using f.monotone' hy.le

@[simp]

中文:
定理 lt_of_neg_of_archimedean
  结论: [阿基米德 S] (f : S ->+*o R)
  证明: by
  apply lt_of_mk_lt_mk_of_nonpos
  · rwa [mk_map_of_archimedean' f hy.ne]
  · simpa using f.monotone' hy.le

@[simp]

Depends on / 依赖: f.monotone, hy.le, hy.ne, lt_of_mk_lt_mk_of_nonpos, mk_map_of_archimedean, monotone
-/
theorem lt_of_neg_of_archimedean [Archimedean S] (f : S ->+*o R)
    {x : R} (hx : 0 < mk x) {y : S} (hy : y < 0) : f y < x := by
  apply lt_of_mk_lt_mk_of_nonpos
  · rwa [mk_map_of_archimedean' f hy.ne]
  · simpa using f.monotone' hy.le

@[simp]
/--
theorem `mk_intCast` / 定理 `mk_intCast`

English:
theorem mk_intCast
  given: {n : Int} (h : n != 0)
  statement: mk (n : S) = 0
  proof: by
  obtain _ | _ := subsingleton_or_nontrivial S
  · exact Subsingleton.allEq ..
  · exact mk_map_of_archimedean' ⟨Int.castRingHom S, fun _ => by simp⟩ h

中文:
定理 mk_intCast
  条件: {n : 整数} (h : n != 0)
  结论: mk (n : S) = 0
  证明: by
  obtain _ | _ := subsingleton_or_nontrivial S
  · exact Subsingleton.allEq ..
  · exact mk_map_of_archimedean' ⟨Int.castRingHom S, fun _ => by simp⟩ h

Depends on / 依赖: Int.castRingHom, Subsingleton, Subsingleton.allEq, castRingHom, mk_map_of_archimedean, subsingleton_or_nontrivial
-/
theorem mk_intCast {n : Int} (h : n != 0) : mk (n : S) = 0 := by
  obtain _ | _ := subsingleton_or_nontrivial S
  · exact Subsingleton.allEq ..
  · exact mk_map_of_archimedean' ⟨Int.castRingHom S, fun _ => by simp⟩ h

/--
theorem `mk_intCast_nonneg` / 定理 `mk_intCast_nonneg`

English:
theorem mk_intCast_nonneg
  given: (n : Int)
  statement: 0 <= mk (n : S)
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · rw [mk_intCast hn]

@[simp]

中文:
定理 mk_intCast_nonneg
  条件: (n : 整数)
  结论: 0 <= mk (n : S)
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · rw [mk_intCast hn]

@[simp]

Depends on / 依赖: eq_or_ne, mk_intCast
-/
theorem mk_intCast_nonneg (n : Int) : 0 <= mk (n : S) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · rw [mk_intCast hn]

@[simp]
/--
theorem `mk_natCast` / 定理 `mk_natCast`

English:
theorem mk_natCast
  given: {n : Nat}
  statement: n != 0 -> mk (n : S) = 0
  proof: mod_cast mk_intCast (n := n)

@[simp]

中文:
定理 mk_natCast
  条件: {n : 自然数}
  结论: n != 0 -> mk (n : S) = 0
  证明: mod_cast mk_intCast (n := n)

@[simp]

Depends on / 依赖: mk_intCast, mod_cast
-/
theorem mk_natCast {n : Nat} : n != 0 -> mk (n : S) = 0 :=
  mod_cast mk_intCast (n := n)

@[simp]
/--
theorem `mk_ofNat` / 定理 `mk_ofNat`

English:
theorem mk_ofNat
  given: {n : Nat} [n.AtLeastTwo]
  statement: mk (ofNat(n) : S) = 0
  proof: mod_cast mk_intCast (n := n) (mod_cast NeZero.ne n)

中文:
定理 mk_of自然数
  条件: {n : 自然数} [n.AtLeastTwo]
  结论: mk (of自然数(n) : S) = 0
  证明: mod_cast mk_intCast (n := n) (mod_cast NeZero.ne n)

Depends on / 依赖: NeZero, NeZero.ne, mk_intCast, mod_cast
-/
theorem mk_ofNat {n : Nat} [n.AtLeastTwo] : mk (ofNat(n) : S) = 0 :=
  mod_cast mk_intCast (n := n) (mod_cast NeZero.ne n)

/--
theorem `mk_natCast_nonneg` / 定理 `mk_natCast_nonneg`

English:
theorem mk_natCast_nonneg
  given: (n : Nat)
  statement: 0 <= mk (n : S)
  proof: mod_cast mk_intCast_nonneg n

中文:
定理 mk_natCast_nonneg
  条件: (n : 自然数)
  结论: 0 <= mk (n : S)
  证明: mod_cast mk_intCast_nonneg n

Depends on / 依赖: mk_intCast_nonneg, mod_cast
-/
theorem mk_natCast_nonneg (n : Nat) : 0 <= mk (n : S) :=
  mod_cast mk_intCast_nonneg n

/--
theorem `exists_nat_ge_of_mk_nonneg` / 定理 `exists_nat_ge_of_mk_nonneg`

English:
theorem exists_nat_ge_of_mk_nonneg
  given: {x : R} (hx : 0 <= mk x)
  statement: exists n : Nat, x <= n
  proof: by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, le_of_abs_le ?_⟩
  simpa using hn

中文:
定理 存在_nat_ge_of_mk_nonneg
  条件: {x : R} (hx : 0 <= mk x)
  结论: 存在 n : 自然数, x <= n
  证明: by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, le_of_abs_le ?_⟩
  simpa using hn

Depends on / 依赖: le_of_abs_le
-/
theorem exists_nat_ge_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Nat, x <= n := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, le_of_abs_le ?_⟩
  simpa using hn

/--
theorem `exists_nat_gt_of_mk_nonneg` / 定理 `exists_nat_gt_of_mk_nonneg`

English:
theorem exists_nat_gt_of_mk_nonneg
  given: {x : R} (hx : 0 <= mk x)
  statement: exists n : Nat, x < n
  proof: by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  refine ⟨n + 1, hn.trans_lt ?_⟩
  simp

中文:
定理 存在_nat_gt_of_mk_nonneg
  条件: {x : R} (hx : 0 <= mk x)
  结论: 存在 n : 自然数, x < n
  证明: by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  refine ⟨n + 1, hn.trans_lt ?_⟩
  simp

Depends on / 依赖: exists_nat_ge_of_mk_nonneg, hn.trans_lt, trans_lt
-/
theorem exists_nat_gt_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Nat, x < n := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  refine ⟨n + 1, hn.trans_lt ?_⟩
  simp

/--
theorem `exists_int_ge_of_mk_nonneg` / 定理 `exists_int_ge_of_mk_nonneg`

English:
theorem exists_int_ge_of_mk_nonneg
  given: {x : R} (hx : 0 <= mk x)
  statement: exists n : Int, x <= n
  proof: by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩

中文:
定理 存在_int_ge_of_mk_nonneg
  条件: {x : R} (hx : 0 <= mk x)
  结论: 存在 n : 整数, x <= n
  证明: by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩

Depends on / 依赖: exists_nat_ge_of_mk_nonneg, mod_cast
-/
theorem exists_int_ge_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Int, x <= n := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩

/--
theorem `exists_int_gt_of_mk_nonneg` / 定理 `exists_int_gt_of_mk_nonneg`

English:
theorem exists_int_gt_of_mk_nonneg
  given: {x : R} (hx : 0 <= mk x)
  statement: exists n : Int, x < n
  proof: by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩

中文:
定理 存在_int_gt_of_mk_nonneg
  条件: {x : R} (hx : 0 <= mk x)
  结论: 存在 n : 整数, x < n
  证明: by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩

Depends on / 依赖: exists_nat_gt_of_mk_nonneg, mod_cast
-/
theorem exists_int_gt_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Int, x < n := by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩

/--
theorem `exists_int_le_of_mk_nonneg` / 定理 `exists_int_le_of_mk_nonneg`

English:
theorem exists_int_le_of_mk_nonneg
  given: {x : R} (hx : 0 <= mk x)
  statement: exists n : Int, n <= x
  proof: by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_le]

中文:
定理 存在_int_le_of_mk_nonneg
  条件: {x : R} (hx : 0 <= mk x)
  结论: 存在 n : 整数, n <= x
  证明: by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_le]

Depends on / 依赖: exists_nat_ge_of_mk_nonneg, mk_neg, neg_le
-/
theorem exists_int_le_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Int, n <= x := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_le]

/--
theorem `exists_int_lt_of_mk_nonneg` / 定理 `exists_int_lt_of_mk_nonneg`

English:
theorem exists_int_lt_of_mk_nonneg
  given: {x : R} (hx : 0 <= mk x)
  statement: exists n : Int, n < x
  proof: by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_lt]

中文:
定理 存在_int_lt_of_mk_nonneg
  条件: {x : R} (hx : 0 <= mk x)
  结论: 存在 n : 整数, n < x
  证明: by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_lt]

Depends on / 依赖: exists_nat_gt_of_mk_nonneg, mk_neg, neg_lt
-/
theorem exists_int_lt_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Int, n < x := by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_lt]

/--
theorem `mk_nonneg_of_le_of_le_of_archimedean` / 定理 `mk_nonneg_of_le_of_le_of_archimedean`

English:
theorem mk_nonneg_of_le_of_le_of_archimedean
  statement: [Archimedean S] (f : S ->+*o R) {x : R} {r s : S}
  proof: by
  apply (min_le_mk_of_le_of_le hr hs).trans'
  simp [mk_map_nonneg_of_archimedean]

中文:
定理 mk_nonneg_of_le_of_le_of_archimedean
  结论: [阿基米德 S] (f : S ->+*o R) {x : R} {r s : S}
  证明: by
  apply (min_le_mk_of_le_of_le hr hs).trans'
  simp [mk_map_nonneg_of_archimedean]

Depends on / 依赖: min_le_mk_of_le_of_le, mk_map_nonneg_of_archimedean
-/
theorem mk_nonneg_of_le_of_le_of_archimedean [Archimedean S] (f : S ->+*o R) {x : R} {r s : S}
    (hr : f r <= x) (hs : x <= f s) : 0 <= mk x := by
  apply (min_le_mk_of_le_of_le hr hs).trans'
  simp [mk_map_nonneg_of_archimedean]

end IsOrderedRing

section IsStrictOrderedRing
variable [IsStrictOrderedRing R]

/--
theorem `add_left_cancel_of_ne_top` / 定理 `add_left_cancel_of_ne_top`

English:
theorem add_left_cancel_of_ne_top
  given: {x y z : ArchimedeanClass R} (hx : x != ⊤) (h : x + y = x + z)
  proof: by
  simp_all

中文:
定理 add_left_cancel_of_ne_top
  条件: {x y z : ArchimedeanClass R} (hx : x != ⊤) (h : x + y = x + z)
  证明: by
  simp_all
-/
theorem add_left_cancel_of_ne_top {x y z : ArchimedeanClass R} (hx : x != ⊤) (h : x + y = x + z) :
    y = z := by
  simp_all

/--
theorem `add_right_cancel_of_ne_top` / 定理 `add_right_cancel_of_ne_top`

English:
theorem add_right_cancel_of_ne_top
  given: {x y z : ArchimedeanClass R} (hx : x != ⊤) (h : y + x = z + x)
  proof: by
  simp_rw [← add_comm x] at h
  exact add_left_cancel_of_ne_top hx h

中文:
定理 add_right_cancel_of_ne_top
  条件: {x y z : ArchimedeanClass R} (hx : x != ⊤) (h : y + x = z + x)
  证明: by
  simp_rw [← add_comm x] at h
  exact add_left_cancel_of_ne_top hx h

Depends on / 依赖: add_comm, add_left_cancel_of_ne_top, simp_rw
-/
theorem add_right_cancel_of_ne_top {x y z : ArchimedeanClass R} (hx : x != ⊤) (h : y + x = z + x) :
    y = z := by
  simp_rw [← add_comm x] at h
  exact add_left_cancel_of_ne_top hx h

/--
theorem `mk_le_mk_iff_denselyOrdered` / 定理 `mk_le_mk_iff_denselyOrdered`

English:
theorem mk_le_mk_iff_denselyOrdered
  statement: [Ring S] [IsStrictOrderedRing S]
  proof: by
  have H {q} : 0 < f q ↔ 0 < q := by simpa using hf.lt_iff_lt (a := 0)
  constructor
  · rintro ⟨(_ | n), hn⟩
    · simp_all [exists_zero_lt]
    · obtain ⟨q, hq₀, hq⟩ := exists_nsmul_lt_of_pos (one_pos (α := R)) (n + 1)
      refine ⟨q, H.2 hq₀, le_of_mul_le_mul_left ?_ n.cast_add_one_pos⟩
      simpa [← mul_assoc] using mul_le_mul (hf hq).le hn (abs_nonneg y) (by simp)
  · rintro ⟨q, hq₀, hq⟩
    have hq₀' := H.1 hq₀
    obtain ⟨n, hn⟩ := exists_lt_nsmul hq₀' 1
    refine ⟨n, le_of_mul_le_mul_left ?_ hq₀⟩
    have h : 0 <= f (n • q) := by
      rw [← f.map_zero]
      exact hf.monotone (nsmul_nonneg hq₀'.le n)
    simpa [mul_comm, mul_assoc] using mul_le_mul (hf hn).le hq (mul_nonneg hq₀.le (abs_nonneg y)) h

中文:
定理 mk_le_mk_iff_denselyOrdered
  结论: [环 S] [是StrictOrdered环 S]
  证明: by
  have H {q} : 0 < f q ↔ 0 < q := by simpa using hf.lt_iff_lt (a := 0)
  constructor
  · rintro ⟨(_ | n), hn⟩
    · simp_all [exists_zero_lt]
    · obtain ⟨q, hq₀, hq⟩ := exists_nsmul_lt_of_pos (one_pos (α := R)) (n + 1)
      refine ⟨q, H.2 hq₀, le_of_mul_le_mul_left ?_ n.cast_add_one_pos⟩
      simpa [← mul_assoc] using mul_le_mul (hf hq).le hn (abs_nonneg y) (by simp)
  · rintro ⟨q, hq₀, hq⟩
    have hq₀' := H.1 hq₀
    obtain ⟨n, hn⟩ := exists_lt_nsmul hq₀' 1
    refine ⟨n, le_of_mul_le_mul_left ?_ hq₀⟩
    have h : 0 <= f (n • q) := by
      rw [← f.map_zero]
      exact hf.monotone (nsmul_nonneg hq₀'.le n)
    simpa [mul_comm, mul_assoc] using mul_le_mul (hf hn).le hq (mul_nonneg hq₀.le (abs_nonneg y)) h

Depends on / 依赖: abs_nonneg, cast_add_one_pos, exists_lt_nsmul, exists_nsmul_lt_of_pos, exists_zero_lt, hf.lt_iff_lt, le_of_mul_le_mul_left, lt_iff_lt, mul_assoc, mul_le_mul, n.cast_add_one_pos, one_pos
-/
theorem mk_le_mk_iff_denselyOrdered [Ring S] [IsStrictOrderedRing S]
    [DenselyOrdered R] [Archimedean R] {x y : S} (f : R ->+* S) (hf : StrictMono f) :
    mk x <= mk y ↔ exists q : R, 0 < f q ∧ f q * |y| <= |x| := by
  have H {q} : 0 < f q ↔ 0 < q := by simpa using hf.lt_iff_lt (a := 0)
  constructor
  · rintro ⟨(_ | n), hn⟩
    · simp_all [exists_zero_lt]
    · obtain ⟨q, hq₀, hq⟩ := exists_nsmul_lt_of_pos (one_pos (α := R)) (n + 1)
      refine ⟨q, H.2 hq₀, le_of_mul_le_mul_left ?_ n.cast_add_one_pos⟩
      simpa [← mul_assoc] using mul_le_mul (hf hq).le hn (abs_nonneg y) (by simp)
  · rintro ⟨q, hq₀, hq⟩
    have hq₀' := H.1 hq₀
    obtain ⟨n, hn⟩ := exists_lt_nsmul hq₀' 1
    refine ⟨n, le_of_mul_le_mul_left ?_ hq₀⟩
    have h : 0 <= f (n • q) := by
      rw [← f.map_zero]
      exact hf.monotone (nsmul_nonneg hq₀'.le n)
    simpa [mul_comm, mul_assoc] using mul_le_mul (hf hn).le hq (mul_nonneg hq₀.le (abs_nonneg y)) h

end IsStrictOrderedRing
end Ring

section Field
variable [Field R] [IsOrderedRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (ArchimedeanClass R)
  body: lift (fun x => mk x⁻¹) fun x y h => by
    obtain rfl | hx := eq_or_ne x 0
    · simp_all
    obtain rfl | hy := eq_or_ne y 0
    · simp_all
    have hx' : mk x != ⊤ := by simpa using hx
    apply add_left_cancel_of_ne_top hx'
    nth_rw 2 [h]
    simp [← mk_mul, hx, hy]

中文:
实例 :
  签名: 取负 (ArchimedeanClass R)
  定义体: lift (fun x => mk x⁻¹) fun x y h => by
    obtain rfl | hx := eq_or_ne x 0
    · simp_all
    obtain rfl | hy := eq_or_ne y 0
    · simp_all
    have hx' : mk x != ⊤ := by simpa using hx
    apply add_left_cancel_of_ne_top hx'
    nth_rw 2 [h]
    simp [← mk_mul, hx, hy]

Depends on / 依赖: add_left_cancel_of_ne_top, eq_or_ne, mk_mul, nth_rw
-/
instance : Neg (ArchimedeanClass R) where
  neg := lift (fun x => mk x⁻¹) fun x y h => by
    obtain rfl | hx := eq_or_ne x 0
    · simp_all
    obtain rfl | hy := eq_or_ne y 0
    · simp_all
    have hx' : mk x != ⊤ := by simpa using hx
    apply add_left_cancel_of_ne_top hx'
    nth_rw 2 [h]
    simp [← mk_mul, hx, hy]

/--
theorem `mk_inv` / 定理 `mk_inv`

English:
theorem mk_inv
  given: (x : R)
  statement: mk x⁻¹ = -mk x
  proof: rfl

中文:
定理 mk_inv
  条件: (x : R)
  结论: mk x⁻¹ = -mk x
  证明: rfl
-/
@[simp] theorem mk_inv (x : R) : mk x⁻¹ = -mk x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Int (ArchimedeanClass R)
  body: lift (fun x => mk (x ^ n)) fun x y h => by
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp [h]

中文:
实例 :
  签名: 标量乘法 整数 (ArchimedeanClass R)
  定义体: lift (fun x => mk (x ^ n)) fun x y h => by
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp [h]

Depends on / 依赖: eq_nat_or_neg, n.eq_nat_or_neg
-/
instance : SMul Int (ArchimedeanClass R) where
  smul n := lift (fun x => mk (x ^ n)) fun x y h => by
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp [h]

/--
theorem `mk_zpow` / 定理 `mk_zpow`

English:
theorem mk_zpow
  given: (n : Int) (x : R)
  statement: mk (x ^ n) = n • mk x
  proof: rfl

中文:
定理 mk_zpow
  条件: (n : 整数) (x : R)
  结论: mk (x ^ n) = n • mk x
  证明: rfl
-/
@[simp] theorem mk_zpow (n : Int) (x : R) : mk (x ^ n) = n • mk x := rfl

/--
theorem `zsmul_succ'` / 定理 `zsmul_succ'`

English:
theorem zsmul_succ'
  given: (n : Nat) (x : ArchimedeanClass R)
  proof: by
  induction x with | mk x
  rw [← mk_zpow]; rw [Nat.cast_succ]
  obtain rfl | hx := eq_or_ne x 0
  · simp [zero_zpow _ n.cast_add_one_ne_zero]
  · rw [zpow_add_one₀ hx, mk_mul, mk_zpow]

中文:
定理 zsmul_succ'
  条件: (n : 自然数) (x : ArchimedeanClass R)
  证明: by
  induction x with | mk x
  rw [← mk_zpow]; rw [Nat.cast_succ]
  obtain rfl | hx := eq_or_ne x 0
  · simp [zero_zpow _ n.cast_add_one_ne_zero]
  · rw [zpow_add_one₀ hx, mk_mul, mk_zpow]
-/
private theorem zsmul_succ' (n : Nat) (x : ArchimedeanClass R) :
    (n.succ : Int) • x = (n : Int) • x + x := by
  induction x with | mk x
  rw [← mk_zpow]; rw [Nat.cast_succ]
  obtain rfl | hx := eq_or_ne x 0
  · simp [zero_zpow _ n.cast_add_one_ne_zero]
  · rw [zpow_add_one₀ hx, mk_mul, mk_zpow]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedAddCommGroupWithTop (ArchimedeanClass R)
  body: by simp [← mk_zero, ← mk_inv]
  top_add' := by simp
  add_neg_cancel_of_ne_top x h := by
    induction x with | mk x
    simp [← mk_inv, ← mk_mul, mul_inv_cancel₀ (mk_eq_top_iff.not.1 h)]
  zsmul_zero' x := by induction x with | mk x => rw [← mk_zpow, zpow_zero, mk_one]
  zsmul_succ' := by exact zsmul_succ'
  zsmul_neg' n x := by
    induction x with | mk x
    rw [← mk_zpow]; rw [zpow_negSucc]; rw [pow_succ]; rw [zsmul_succ']; rw [mk_inv]; rw [mk_mul]; rw [← zpow_natCast]; rw [mk_zpow]

@[simp]

中文:
实例 :
  签名: LinearOrderedAddComm群带顶 (ArchimedeanClass R)
  定义体: by simp [← mk_zero, ← mk_inv]
  top_add' := by simp
  add_neg_cancel_of_ne_top x h := by
    induction x with | mk x
    simp [← mk_inv, ← mk_mul, mul_inv_cancel₀ (mk_eq_top_iff.not.1 h)]
  zsmul_zero' x := by induction x with | mk x => rw [← mk_zpow, zpow_zero, mk_one]
  zsmul_succ' := by exact zsmul_succ'
  zsmul_neg' n x := by
    induction x with | mk x
    rw [← mk_zpow]; rw [zpow_negSucc]; rw [pow_succ]; rw [zsmul_succ']; rw [mk_inv]; rw [mk_mul]; rw [← zpow_natCast]; rw [mk_zpow]

@[simp]

Depends on / 依赖: add_neg_cancel_of_ne_top, mk_eq_top_iff, mk_eq_top_iff.not, mk_inv, mk_mul, mk_one, mk_zero, mk_zpow, pow_succ, top_add, zpow_natCast, zpow_negSucc, zpow_zero, zsmul_neg, zsmul_succ, zsmul_zero
-/
noncomputable instance : LinearOrderedAddCommGroupWithTop (ArchimedeanClass R) where
  neg_top := by simp [← mk_zero, ← mk_inv]
  top_add' := by simp
  add_neg_cancel_of_ne_top x h := by
    induction x with | mk x
    simp [← mk_inv, ← mk_mul, mul_inv_cancel₀ (mk_eq_top_iff.not.1 h)]
  zsmul_zero' x := by induction x with | mk x => rw [← mk_zpow, zpow_zero, mk_one]
  zsmul_succ' := by exact zsmul_succ'
  zsmul_neg' n x := by
    induction x with | mk x
    rw [← mk_zpow]; rw [zpow_negSucc]; rw [pow_succ]; rw [zsmul_succ']; rw [mk_inv]; rw [mk_mul]; rw [← zpow_natCast]; rw [mk_zpow]

@[simp]
/--
theorem `mk_div` / 定理 `mk_div`

English:
theorem mk_div
  given: (x y : R)
  statement: mk (x / y) = mk x - mk y
  proof: by
  rw [div_eq_mul_inv]; rw [mk_mul]; rw [mk_inv]; rw [sub_eq_add_neg]

@[simp]

中文:
定理 mk_div
  条件: (x y : R)
  结论: mk (x / y) = mk x - mk y
  证明: by
  rw [div_eq_mul_inv]; rw [mk_mul]; rw [mk_inv]; rw [sub_eq_add_neg]

@[simp]

Depends on / 依赖: div_eq_mul_inv, mk_inv, mk_mul, sub_eq_add_neg
-/
theorem mk_div (x y : R) : mk (x / y) = mk x - mk y := by
  rw [div_eq_mul_inv]; rw [mk_mul]; rw [mk_inv]; rw [sub_eq_add_neg]

@[simp]
/--
theorem `mk_ratCast` / 定理 `mk_ratCast`

English:
theorem mk_ratCast
  given: {q : Rat} (h : q != 0)
  statement: mk (q : R) = 0
  proof: by
  simpa using mk_map_of_archimedean ⟨(Rat.castHom R).toAddMonoidHom, fun _ => by simp⟩ h

中文:
定理 mk_ratCast
  条件: {q : 有理数} (h : q != 0)
  结论: mk (q : R) = 0
  证明: by
  simpa using mk_map_of_archimedean ⟨(Rat.castHom R).toAddMonoidHom, fun _ => by simp⟩ h

Depends on / 依赖: Rat.castHom, castHom, mk_map_of_archimedean, toAddMonoidHom
-/
theorem mk_ratCast {q : Rat} (h : q != 0) : mk (q : R) = 0 := by
  simpa using mk_map_of_archimedean ⟨(Rat.castHom R).toAddMonoidHom, fun _ => by simp⟩ h

/--
theorem `mk_ratCast_nonneg` / 定理 `mk_ratCast_nonneg`

English:
theorem mk_ratCast_nonneg
  given: (q : Rat)
  statement: 0 <= mk (q : R)
  proof: by
  obtain rfl | hn := eq_or_ne q 0
  · simp
  · rw [mk_ratCast hn]

中文:
定理 mk_ratCast_nonneg
  条件: (q : 有理数)
  结论: 0 <= mk (q : R)
  证明: by
  obtain rfl | hn := eq_or_ne q 0
  · simp
  · rw [mk_ratCast hn]

Depends on / 依赖: eq_or_ne, mk_ratCast
-/
theorem mk_ratCast_nonneg (q : Rat) : 0 <= mk (q : R) := by
  obtain rfl | hn := eq_or_ne q 0
  · simp
  · rw [mk_ratCast hn]

/--
theorem `mk_le_mk_iff_ratCast` / 定理 `mk_le_mk_iff_ratCast`

English:
theorem mk_le_mk_iff_ratCast
  given: {x y : R}
  statement: mk x <= mk y ↔ exists q : Rat, 0 < q ∧ q * |y| <= |x|
  proof: by
  simpa using mk_le_mk_iff_denselyOrdered (Rat.castHom _) Rat.cast_strictMono (x := x)

中文:
定理 mk_le_mk_iff_ratCast
  条件: {x y : R}
  结论: mk x <= mk y ↔ 存在 q : 有理数, 0 < q ∧ q * |y| <= |x|
  证明: by
  simpa using mk_le_mk_iff_denselyOrdered (Rat.castHom _) Rat.cast_strictMono (x := x)

Depends on / 依赖: Rat.castHom, Rat.cast_strictMono, castHom, cast_strictMono, mk_le_mk_iff_denselyOrdered
-/
theorem mk_le_mk_iff_ratCast {x y : R} : mk x <= mk y ↔ exists q : Rat, 0 < q ∧ q * |y| <= |x| := by
  simpa using mk_le_mk_iff_denselyOrdered (Rat.castHom _) Rat.cast_strictMono (x := x)

end Field
end ArchimedeanClass
