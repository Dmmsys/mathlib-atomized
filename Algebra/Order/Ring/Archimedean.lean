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

/-
**ArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (ArchimedeanClass R) where
  zero := mk 1
/-
**ArchimedeanClass.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : CommRing R] [inst_2 : Is
StrictOrderedRing R],   ArchimedeanClass.mk 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
@[simp] theorem mk_one : mk (1 : R) = 0 := rfl
/-
**ArchimedeanClass.top_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : CommRing R] [inst_2 : Is
StrictOrderedRing R], ⊤ ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma top_ne_zero : (⊤ : ArchimedeanClass R) ≠ 0 := by simp [← mk_one]
/-
**ArchimedeanClass.zero_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : CommRing R] [inst_2 : Is
StrictOrderedRing R], 0 ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.top_ne_zero`：∀ {R : Type u_1} [inst : LinearOrder R] [i
nst_1 : CommRing R] [inst_2 : IsStrictOrderedRing R], ⊤ ≠ 0
-/
@[simp] lemma zero_ne_top : 0 ≠ (⊤ : ArchimedeanClass R) := top_ne_zero.symm
/-
**ArchimedeanClass.mk_mul_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mk_mul_le_of_le {x₁ y₁ x₂ y₂ : R} (hx : mk x₁ ≤ mk x₂) (hy : mk y₁ ≤ mk y₂) :
    mk (x₁ * y₁) ≤ mk (x₂ * y₂) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  use m * n
  convert mul_le_mul hm hn (abs_nonneg _) (nsmul_nonneg (abs_nonneg _) _) <;>
    simp_rw [ArchimedeanOrder.val_of, abs_mul]
  ring

/-- Multiplication in `R` transfers to addition in `ArchimedeanClass R`. -/
/-
**ArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication in `R` transfers to addition in `ArchimedeanClass R`.
-/
instance : Add (ArchimedeanClass R) where
  add := lift₂ (fun x y ↦ .mk <| x * y) fun _ _ _ _ hx hy ↦ by
    exact (mk_mul_le_of_le hx.le hy.le).antisymm (mk_mul_le_of_le hx.ge hy.ge)
/-
**ArchimedeanClass.mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : CommRing R] [inst_2 : Is
StrictOrderedRing R] (x y : R),   ArchimedeanClass.mk (x * y) = ArchimedeanClass
.mk x + ArchimedeanClass.mk y
参数：x y : R；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
@[simp] theorem mk_mul (x y : R) : mk (x * y) = mk x + mk y := rfl
/-
**ArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (ArchimedeanClass R) where
  smul n := lift (fun x ↦ mk (x ^ n)) fun x y h ↦ by
    induction n with
    | zero => simp
    | succ n IH => simp_rw [pow_succ, mk_mul, IH, h]
/-
**ArchimedeanClass.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : CommRing R] [inst_2 : Is
StrictOrderedRing R] (n : ℕ) (x : R),   ArchimedeanClass.mk (x ^ n) = n • Archim
edeanClass.mk x
参数：n : ℕ；x : R；x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
@[simp] theorem mk_pow (n : ℕ) (x : R) : mk (x ^ n) = n • mk x := rfl
/-
**ArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMagma (ArchimedeanClass R) where
  add_comm x y := by
    induction x with | mk x
    induction y with | mk y
    rw [← mk_mul, mul_comm, mk_mul]
/-
**ArchimedeanClass.zero_add'** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem zero_add' (x : ArchimedeanClass R) : 0 + x = x := by
  induction x with | mk x
  rw [← mk_one, ← mk_mul, one_mul]
/-
**ArchimedeanClass.add_assoc'** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem add_assoc' (x y z : ArchimedeanClass R) : x + y + z = x + (y + z) := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  simp_rw [← mk_mul, mul_assoc]
/-
**ArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (ArchimedeanClass R) where
  add_assoc := private add_assoc'
  zero_add := private zero_add'
  add_zero x := private add_comm x _ ▸ zero_add' x
  nsmul_zero x := by induction x with | mk x => rw [← mk_pow, pow_zero, mk_one]
  nsmul_succ n x := by induction x with | mk x => rw [← mk_pow, pow_succ, mk_mul, mk_pow]
/-
**ArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedAddMonoid (ArchimedeanClass R) where
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    rw [← mk_mul, ← mk_mul]
    exact mk_mul_le_of_le h le_rfl
/-
**ArchimedeanClass.isAddRegular_mk** 是 Mathlib 中的一个引理，位于命名空间 `ArchimedeanClass`。
形式化陈述：isAddRegular_mk {x : R} (hx : x != 0) : IsAddRegular (mk x)
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isAddLeftRegular_iff_isAddRegular`：∀ {G : Type u_1} [inst : AddCommMagma
 G] {a : G}, IsAddLeftRegular a ↔ IsAddRegular a
· 使用定理 `ArchimedeanClass.ind`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_1 :
 LinearOrder M] [inst_2 : IsOrderedAddMonoid M]   {motive : ArchimedeanClass M →
 Prop},   …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma isAddRegular_mk {x : R} (hx : x ≠ 0) : IsAddRegular (mk x) := by
  rw [← isAddLeftRegular_iff_isAddRegular]
  rintro y z hyz
  induction y with | mk y =>
  induction z with | mk z =>
  simpa [← mk_mul, mk_eq_mk, mul_left_comm _ (|x|), abs_pos.2 hx] using hyz
/-
**ArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LinearOrderedAddCommMonoidWithTop (ArchimedeanClass R) where
  top_add' x := by induction x with | mk x => rw [← mk_zero, ← mk_mul, zero_mul]
  isAddLeftRegular_of_ne_top x := by induction x with | mk x => simp +contextual [isAddRegular_mk]

variable (R) in
/-- `ArchimedeanClass.mk` defines an `AddValuation` on the ring `R`. -/
/-
**ArchimedeanClass.addValuation** 是 Mathlib 中的一个定义，位于命名空间 `ArchimedeanClass`。
形式化陈述：addValuation : AddValuation R (ArchimedeanClass R)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.mk_mul`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1
 : CommRing R] [inst_2 : IsStrictOrderedRing R] (x y : R),   ArchimedeanClass.mk
 (x * y) = Ar…

--- 原说明 ---
`ArchimedeanClass.mk` defines an `AddValuation` on the ring `R`.
-/
noncomputable def addValuation : AddValuation R (ArchimedeanClass R) := AddValuation.of mk
  rfl rfl min_le_mk_add mk_mul
/-
**ArchimedeanClass.addValuation_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClas
s`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : CommRing R] [inst_2 : Is
StrictOrderedRing R] (a : R),   (ArchimedeanClass.addValuation R) a = Archimedea
nClass.mk a
参数：a : R；ArchimedeanClass.addValuation R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
@[simp] theorem addValuation_apply (a : R) : addValuation R a = mk a := rfl

variable {S : Type*} [LinearOrder S] [CommRing S] [IsStrictOrderedRing S]

@[simp]
/-
**ArchimedeanClass.orderHom_zero** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：orderHom_zero (f : S ->+o R) : orderHom f 0 = mk (f 1)
参数：f : S ->+o R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.mk_one`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1
 : CommRing R] [inst_2 : IsStrictOrderedRing R],   ArchimedeanClass.mk 1 = 0
· 使用定理 `ArchimedeanClass.orderHom_mk`：∀ {M : Type u_1} [inst : AddCommGroup M] [
inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {N : Type u_2}   [inst_3
 : AddCommGroup N]…
-/
theorem orderHom_zero (f : S →+o R) : orderHom f 0 = mk (f 1) := by
  rw [← mk_one, orderHom_mk]

@[simp]
/-
**ArchimedeanClass.mk_eq_zero_of_archimedean** 是 Mathlib 中的一个定理，位于命名空间 `Archimed
eanClass`。
形式化陈述：mk_eq_zero_of_archimedean [Archimedean S] {x : S} (h : x != 0) : mk x = 0
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.mk_eq_mk_of_archimedean`：∀ {M : Type u_1} [inst : AddCo
mmGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M}   
[Archimedean M], a ≠ 0 → b ≠ 0…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
theorem mk_eq_zero_of_archimedean [Archimedean S] {x : S} (h : x ≠ 0) : mk x = 0 :=
  mk_eq_mk_of_archimedean h one_ne_zero
/-
**ArchimedeanClass.eq_zero_or_top_of_archimedean** 是 Mathlib 中的一个定理，位于命名空间 `Arch
imedeanClass`。
形式化陈述：eq_zero_or_top_of_archimedean [Archimedean S] (x : ArchimedeanClass S) : x
 = 0 ∨ x = ⊤
参数：x : ArchimedeanClass S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.ind`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_1 :
 LinearOrder M] [inst_2 : IsOrderedAddMonoid M]   {motive : ArchimedeanClass M →
 Prop},   …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArchimedeanClass.mk_eq_zero_of_archimedean`：mk_eq_zero_of_archimedean [A
rchimedean S] {x : S} (h : x != 0) : mk x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem eq_zero_or_top_of_archimedean [Archimedean S] (x : ArchimedeanClass S) : x = 0 ∨ x = ⊤ := by
  induction x with | mk x
  obtain rfl | h := eq_or_ne x 0 <;> simp_all

/-- See `mk_map_of_archimedean'` for a version taking `M →+*o R`. -/
/-
**ArchimedeanClass.mk_map_of_archimedean** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanC
lass`。
形式化陈述：mk_map_of_archimedean [Archimedean S] (f : S ->+o R) {x : S} (h : x != 0) 
: mk (f x) = mk (f 1)
参数：f : S ->+o R；h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.orderHom_mk`：∀ {M : Type u_1} [inst : AddCommGroup M] [
inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {N : Type u_2}   [inst_3
 : AddCommGroup N]…
· 使用定理 `ArchimedeanClass.mk_eq_zero_of_archimedean`：mk_eq_zero_of_archimedean [A
rchimedean S] {x : S} (h : x != 0) : mk x = 0
· 使用定理 `ArchimedeanClass.orderHom_zero`：orderHom_zero (f : S ->+o R) : orderHom 
f 0 = mk (f 1)

--- 原说明 ---
See `mk_map_of_archimedean'` for a version taking `M →+*o R`.
-/
theorem mk_map_of_archimedean [Archimedean S] (f : S →+o R) {x : S} (h : x ≠ 0) :
    mk (f x) = mk (f 1) := by
  rw [← orderHom_mk, mk_eq_zero_of_archimedean h, orderHom_zero]

/-- See `mk_map_of_archimedean` for a version taking `M →+o R`. -/
/-
**ArchimedeanClass.mk_map_of_archimedean'** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean
Class`。
形式化陈述：mk_map_of_archimedean' [Archimedean S] (f : S ->+*o R) {x : S} (h : x != 0
) : mk (f x) = 0
参数：f : S ->+*o R；h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `ArchimedeanClass.mk_map_of_archimedean`：mk_map_of_archimedean [Archimede
an S] (f : S ->+o R) {x : S} (h : x != 0) : mk (f x) = mk (f 1)

--- 原说明 ---
See `mk_map_of_archimedean` for a version taking `M →+o R`.
-/
theorem mk_map_of_archimedean' [Archimedean S] (f : S →+*o R) {x : S} (h : x ≠ 0) :
    mk (f x) = 0 := by
  simpa using mk_map_of_archimedean f.toOrderAddMonoidHom h
/-
**ArchimedeanClass.mk_le_mk_add_of_archimedean** 是 Mathlib 中的一个定理，位于命名空间 `Archim
edeanClass`。
形式化陈述：mk_le_mk_add_of_archimedean [Archimedean S] (f : S ->+*o R) (x : R) (y : S
) : mk x <= mk (f y) + mk x
参数：f : S ->+*o R；x : R；y : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.mk_map_of_archimedean'`：mk_map_of_archimedean' [Archime
dean S] (f : S ->+*o R) {x : S} (h : x != 0) : mk (f x) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mk_le_mk_add_of_archimedean [Archimedean S] (f : S →+*o R) (x : R) (y : S) :
    mk x ≤ mk (f y) + mk x := by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [mk_map_of_archimedean' f hy, zero_add]
/-
**ArchimedeanClass.mk_le_add_mk_of_archimedean** 是 Mathlib 中的一个定理，位于命名空间 `Archim
edeanClass`。
形式化陈述：mk_le_add_mk_of_archimedean [Archimedean S] (f : S ->+*o R) (x : R) (y : S
) : mk x <= mk x + mk (f y)
参数：f : S ->+*o R；x : R；y : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ArchimedeanClass.mk_le_mk_add_of_archimedean`：mk_le_mk_add_of_archimedea
n [Archimedean S] (f : S ->+*o R) (x : R) (y : S) : mk x <= mk (f y) + mk x
-/
theorem mk_le_add_mk_of_archimedean [Archimedean S] (f : S →+*o R) (x : R) (y : S) :
    mk x ≤ mk x + mk (f y) := by
  rw [add_comm]
  exact mk_le_mk_add_of_archimedean f x y
/-
**ArchimedeanClass.mk_map_nonneg_of_archimedean** 是 Mathlib 中的一个定理，位于命名空间 `Archi
medeanClass`。
形式化陈述：mk_map_nonneg_of_archimedean [Archimedean S] (f : S ->+*o R) (y : S) : 0 <
= mk (f y)
参数：f : S ->+*o R；y : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ArchimedeanClass.mk_le_mk_add_of_archimedean`：mk_le_mk_add_of_archimedea
n [Archimedean S] (f : S ->+*o R) (x : R) (y : S) : mk x <= mk (f y) + mk x
-/
theorem mk_map_nonneg_of_archimedean [Archimedean S] (f : S →+*o R) (y : S) : 0 ≤ mk (f y) := by
  simpa using mk_le_mk_add_of_archimedean f 1 y
/-
**ArchimedeanClass.lt_of_pos_of_archimedean** 是 Mathlib 中的一个定理，位于命名空间 `Archimede
anClass`。
形式化陈述：lt_of_pos_of_archimedean [Archimedean S] (f : S ->+*o R) {x : R} (hx : 0 <
 mk x) {y : S} (hy : 0 < y) : x < f y
参数：f : S ->+*o R；hx : 0 < mk x；hy : 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg`：∀ {M : Type u_1} [inst : AddC
ommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M}, 
  ArchimedeanClass.mk a < Archi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArchimedeanClass.mk_map_of_archimedean'`：mk_map_of_archimedean' [Archime
dean S] (f : S ->+*o R) {x : S} (h : x != 0) : mk (f x) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderRingHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : α ->+*o β) : f.toRi
ngHom = f
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `OrderRingHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : NonAssoc
Semiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3 : Preo
rder β] (sel…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem lt_of_pos_of_archimedean [Archimedean S] (f : S →+*o R)
    {x : R} (hx : 0 < mk x) {y : S} (hy : 0 < y) : x < f y := by
  apply lt_of_mk_lt_mk_of_nonneg
  · rwa [mk_map_of_archimedean' f hy.ne']
  · simpa using f.monotone' hy.le
/-
**ArchimedeanClass.lt_of_neg_of_archimedean** 是 Mathlib 中的一个定理，位于命名空间 `Archimede
anClass`。
形式化陈述：lt_of_neg_of_archimedean [Archimedean S] (f : S ->+*o R) {x : R} (hx : 0 <
 mk x) {y : S} (hy : y < 0) : f y < x
参数：f : S ->+*o R；hx : 0 < mk x；hy : y < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.lt_of_mk_lt_mk_of_nonpos`：∀ {M : Type u_1} [inst : AddC
ommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M}, 
  ArchimedeanClass.mk a < Archi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArchimedeanClass.mk_map_of_archimedean'`：mk_map_of_archimedean' [Archime
dean S] (f : S ->+*o R) {x : S} (h : x != 0) : mk (f x) = 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `OrderRingHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : α ->+*o β) : f.toRi
ngHom = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `OrderRingHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : NonAssoc
Semiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3 : Preo
rder β] (sel…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem lt_of_neg_of_archimedean [Archimedean S] (f : S →+*o R)
    {x : R} (hx : 0 < mk x) {y : S} (hy : y < 0) : f y < x := by
  apply lt_of_mk_lt_mk_of_nonpos
  · rwa [mk_map_of_archimedean' f hy.ne]
  · simpa using f.monotone' hy.le

@[simp]
/-
**ArchimedeanClass.mk_intCast** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：mk_intCast {n : Int} (h : n != 0) : mk (n : S) = 0
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `ArchimedeanClass.instSubsingleton`：∀ {M : Type u_1} [inst : AddCommGroup
 M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] [Subsingleton M],  
 Subsingleton (Archimed…
· 使用定理 `ArchimedeanClass.mk_map_of_archimedean'`：mk_map_of_archimedean' [Archime
dean S] (f : S ->+*o R) {x : S} (h : x != 0) : mk (f x) = 0
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mk_intCast {n : ℤ} (h : n ≠ 0) : mk (n : S) = 0 := by
  obtain _ | _ := subsingleton_or_nontrivial S
  · exact Subsingleton.allEq ..
  · exact mk_map_of_archimedean' ⟨Int.castRingHom S, fun _ ↦ by simp⟩ h
/-
**ArchimedeanClass.mk_intCast_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass
`。
形式化陈述：mk_intCast_nonneg (n : Int) : 0 <= mk (n : S)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.mk_intCast`：mk_intCast {n : Int} (h : n != 0) : mk (n :
 S) = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mk_intCast_nonneg (n : ℤ) : 0 ≤ mk (n : S) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · rw [mk_intCast hn]

@[simp]
/-
**ArchimedeanClass.mk_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：mk_natCast {n : Nat} : n != 0 -> mk (n : S) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ArchimedeanClass.mk_intCast`：mk_intCast {n : Int} (h : n != 0) : mk (n :
 S) = 0
-/
theorem mk_natCast {n : ℕ} : n ≠ 0 → mk (n : S) = 0 :=
  mod_cast mk_intCast (n := n)

@[simp]
/-
**ArchimedeanClass.mk_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：mk_ofNat {n : Nat} [n.AtLeastTwo] : mk (ofNat(n) : S) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ArchimedeanClass.mk_intCast`：mk_intCast {n : Int} (h : n != 0) : mk (n :
 S) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
theorem mk_ofNat {n : ℕ} [n.AtLeastTwo] : mk (ofNat(n) : S) = 0 :=
  mod_cast mk_intCast (n := n) (mod_cast NeZero.ne n)
/-
**ArchimedeanClass.mk_natCast_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass
`。
形式化陈述：mk_natCast_nonneg (n : Nat) : 0 <= mk (n : S)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ArchimedeanClass.mk_intCast_nonneg`：mk_intCast_nonneg (n : Int) : 0 <= m
k (n : S)
-/
theorem mk_natCast_nonneg (n : ℕ) : 0 ≤ mk (n : S) :=
  mod_cast mk_intCast_nonneg n
/-
**ArchimedeanClass.exists_nat_ge_of_mk_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Archime
deanClass`。
形式化陈述：exists_nat_ge_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Nat, x <=
 n
参数：hx : 0 <= mk x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `le_of_abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearO
rder G] [IsOrderedAddMonoid G] {a b : G}, |a| ≤ b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem exists_nat_ge_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℕ, x ≤ n := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, le_of_abs_le ?_⟩
  simpa using hn
/-
**ArchimedeanClass.exists_nat_gt_of_mk_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Archime
deanClass`。
形式化陈述：exists_nat_gt_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Nat, x < 
n
参数：hx : 0 <= mk x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.exists_nat_ge_of_mk_nonneg`：exists_nat_ge_of_mk_nonneg 
{x : R} (hx : 0 <= mk x) : exists n : Nat, x <= n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
theorem exists_nat_gt_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℕ, x < n := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  refine ⟨n + 1, hn.trans_lt ?_⟩
  simp
/-
**ArchimedeanClass.exists_int_ge_of_mk_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Archime
deanClass`。
形式化陈述：exists_int_ge_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Int, x <=
 n
参数：hx : 0 <= mk x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.exists_nat_ge_of_mk_nonneg`：exists_nat_ge_of_mk_nonneg 
{x : R} (hx : 0 <= mk x) : exists n : Nat, x <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
-/
theorem exists_int_ge_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, x ≤ n := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩
/-
**ArchimedeanClass.exists_int_gt_of_mk_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Archime
deanClass`。
形式化陈述：exists_int_gt_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Int, x < 
n
参数：hx : 0 <= mk x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.exists_nat_gt_of_mk_nonneg`：exists_nat_gt_of_mk_nonneg 
{x : R} (hx : 0 <= mk x) : exists n : Nat, x < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
-/
theorem exists_int_gt_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, x < n := by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩
/-
**ArchimedeanClass.exists_int_le_of_mk_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Archime
deanClass`。
形式化陈述：exists_int_le_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Int, n <=
 x
参数：hx : 0 <= mk x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.exists_nat_ge_of_mk_nonneg`：exists_nat_ge_of_mk_nonneg 
{x : R} (hx : 0 <= mk x) : exists n : Nat, x <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.mk_neg`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_
1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] (a : M),   ArchimedeanClass.m
k (-a) = Arch…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem exists_int_le_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, n ≤ x := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_le]
/-
**ArchimedeanClass.exists_int_lt_of_mk_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Archime
deanClass`。
形式化陈述：exists_int_lt_of_mk_nonneg {x : R} (hx : 0 <= mk x) : exists n : Int, n < 
x
参数：hx : 0 <= mk x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.exists_nat_gt_of_mk_nonneg`：exists_nat_gt_of_mk_nonneg 
{x : R} (hx : 0 <= mk x) : exists n : Nat, x < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.mk_neg`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_
1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] (a : M),   ArchimedeanClass.m
k (-a) = Arch…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem exists_int_lt_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, n < x := by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_lt]
/-
**ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean** 是 Mathlib 中的一个定理，位于命名空
间 `ArchimedeanClass`。
形式化陈述：mk_nonneg_of_le_of_le_of_archimedean [Archimedean S] (f : S ->+*o R) {x : 
R} {r s : S} (hr : f r <= x) (hs : x <= f s) : 0 <= mk x
参数：f : S ->+*o R；hr : f r <= x；hs : x <= f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.min_le_mk_of_le_of_le`：∀ {M : Type u_1} [inst : AddComm
Group M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {x y z : M},  
 y ≤ x → x ≤ z → min (Archim…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem mk_nonneg_of_le_of_le_of_archimedean [Archimedean S] (f : S →+*o R) {x : R} {r s : S}
    (hr : f r ≤ x) (hs : x ≤ f s) : 0 ≤ mk x := by
  apply (min_le_mk_of_le_of_le hr hs).trans'
  simp [mk_map_nonneg_of_archimedean]

end IsOrderedRing

section IsStrictOrderedRing
variable [IsStrictOrderedRing R]

/-
**ArchimedeanClass.add_left_cancel_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Archimed
eanClass`。
形式化陈述：add_left_cancel_of_ne_top {x y z : ArchimedeanClass R} (hx : x != ⊤) (h : 
x + y = x + z) : y = z
参数：hx : x != ⊤；h : x + y = x + z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_left_cancel_of_ne_top {x y z : ArchimedeanClass R} (hx : x ≠ ⊤) (h : x + y = x + z) :
    y = z := by
  simp_all
/-
**ArchimedeanClass.add_right_cancel_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Archime
deanClass`。
形式化陈述：add_right_cancel_of_ne_top {x y z : ArchimedeanClass R} (hx : x != ⊤) (h :
 y + x = z + x) : y = z
参数：hx : x != ⊤；h : y + x = z + x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.add_left_cancel_of_ne_top`：add_left_cancel_of_ne_top {x
 y z : ArchimedeanClass R} (hx : x != ⊤) (h : x + y = x + z) : y = z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem add_right_cancel_of_ne_top {x y z : ArchimedeanClass R} (hx : x ≠ ⊤) (h : y + x = z + x) :
    y = z := by
  simp_rw [← add_comm x] at h
  exact add_left_cancel_of_ne_top hx h
/-
**ArchimedeanClass.mk_le_mk_iff_denselyOrdered** 是 Mathlib 中的一个定理，位于命名空间 `Archim
edeanClass`。
形式化陈述：mk_le_mk_iff_denselyOrdered [Ring S] [IsStrictOrderedRing S] [DenselyOrder
ed R] [Archimedean R] {x y : S} (f : R ->+* S) (hf : StrictMono f) : mk x <= mk 
y ↔ exists q : R, 0 < f q ∧ f q * |y| <= |x|
参数：f : R ->+* S；hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `exists_nsmul_lt_of_pos`：∀ {M : Type u_2} [inst : LinearOrder M] [Densely
Ordered M] {x : M} [inst_2 : AddCommMonoid M] [ExistsAddOfLE M]   [IsOrderedCanc
elAddMonoid …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_of_mul_le_mul_left`：le_of_mul_le_mul_left [PosMulReflectLE α] (bc : a
 * b <= a * c) (a0 : 0 < a) : b <= c
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
（共 61 条，此处仅展示前 30 条）
-/
theorem mk_le_mk_iff_denselyOrdered [Ring S] [IsStrictOrderedRing S]
    [DenselyOrdered R] [Archimedean R] {x y : S} (f : R →+* S) (hf : StrictMono f) :
    mk x ≤ mk y ↔ ∃ q : R, 0 < f q ∧ f q * |y| ≤ |x| := by
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
    have h : 0 ≤ f (n • q) := by
      rw [← f.map_zero]
      exact hf.monotone (nsmul_nonneg hq₀'.le n)
    simpa [mul_comm, mul_assoc] using mul_le_mul (hf hn).le hq (mul_nonneg hq₀.le (abs_nonneg y)) h

end IsStrictOrderedRing
end Ring

section Field
variable [Field R] [IsOrderedRing R]

/-
**ArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (ArchimedeanClass R) where
  neg := lift (fun x ↦ mk x⁻¹) fun x y h ↦ by
    obtain rfl | hx := eq_or_ne x 0
    · simp_all
    obtain rfl | hy := eq_or_ne y 0
    · simp_all
    have hx' : mk x ≠ ⊤ := by simpa using hx
    apply add_left_cancel_of_ne_top hx'
    nth_rw 2 [h]
    simp [← mk_mul, hx, hy]
/-
**ArchimedeanClass.mk_inv** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : Field R] [inst_2 : IsOrd
eredRing R] (x : R),   ArchimedeanClass.mk x⁻¹ = -ArchimedeanClass.mk x
参数：x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
@[simp] theorem mk_inv (x : R) : mk x⁻¹ = -mk x := rfl
/-
**ArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℤ (ArchimedeanClass R) where
  smul n := lift (fun x ↦ mk (x ^ n)) fun x y h ↦ by
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp [h]
/-
**ArchimedeanClass.mk_zpow** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : Field R] [inst_2 : IsOrd
eredRing R] (n : ℤ) (x : R),   ArchimedeanClass.mk (x ^ n) = n • ArchimedeanClas
s.mk x
参数：n : ℤ；x : R；x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
@[simp] theorem mk_zpow (n : ℤ) (x : R) : mk (x ^ n) = n • mk x := rfl
/-
**ArchimedeanClass.zsmul_succ'** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem zsmul_succ' (n : ℕ) (x : ArchimedeanClass R) :
    (n.succ : ℤ) • x = (n : ℤ) • x + x := by
  induction x with | mk x
  rw [← mk_zpow, Nat.cast_succ]
  obtain rfl | hx := eq_or_ne x 0
  · simp [zero_zpow _ n.cast_add_one_ne_zero]
  · rw [zpow_add_one₀ hx, mk_mul, mk_zpow]
/-
**ArchimedeanClass.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
    rw [← mk_zpow, zpow_negSucc, pow_succ, zsmul_succ', mk_inv, mk_mul, ← zpow_natCast, mk_zpow]

@[simp]
/-
**ArchimedeanClass.mk_div** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：mk_div (x y : R) : mk (x / y) = mk x - mk y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `ArchimedeanClass.mk_mul`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1
 : CommRing R] [inst_2 : IsStrictOrderedRing R] (x y : R),   ArchimedeanClass.mk
 (x * y) = Ar…
· 使用定理 `ArchimedeanClass.mk_inv`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1
 : Field R] [inst_2 : IsOrderedRing R] (x : R),   ArchimedeanClass.mk x⁻¹ = -Arc
himedeanClass…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem mk_div (x y : R) : mk (x / y) = mk x - mk y := by
  rw [div_eq_mul_inv, mk_mul, mk_inv, sub_eq_add_neg]

@[simp]
/-
**ArchimedeanClass.mk_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：mk_ratCast {q : Rat} (h : q != 0) : mk (q : R) = 0
参数：h : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `ArchimedeanClass.mk_map_of_archimedean`：mk_map_of_archimedean [Archimede
an S] (f : S ->+o R) {x : S} (h : x != 0) : mk (f x) = mk (f 1)
· 使用定理 `instArchimedeanRat`：Archimedean ℚ
-/
theorem mk_ratCast {q : ℚ} (h : q ≠ 0) : mk (q : R) = 0 := by
  simpa using mk_map_of_archimedean ⟨(Rat.castHom R).toAddMonoidHom, fun _ ↦ by simp⟩ h
/-
**ArchimedeanClass.mk_ratCast_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass
`。
形式化陈述：mk_ratCast_nonneg (q : Rat) : 0 <= mk (q : R)
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.mk_ratCast`：mk_ratCast {q : Rat} (h : q != 0) : mk (q :
 R) = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mk_ratCast_nonneg (q : ℚ) : 0 ≤ mk (q : R) := by
  obtain rfl | hn := eq_or_ne q 0
  · simp
  · rw [mk_ratCast hn]
/-
**ArchimedeanClass.mk_le_mk_iff_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanCl
ass`。
形式化陈述：mk_le_mk_iff_ratCast {x y : R} : mk x <= mk y ↔ exists q : Rat, 0 < q ∧ q 
* |y| <= |x|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArchimedeanClass.mk_le_mk_iff_denselyOrdered`：mk_le_mk_iff_denselyOrdere
d [Ring S] [IsStrictOrderedRing S] [DenselyOrdered R] [Archimedean R] {x y : S} 
(f : R ->+* S) (hf : StrictMono f)…
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instArchimedeanRat`：Archimedean ℚ
· 使用定理 `Rat.cast_strictMono`：cast_strictMono : StrictMono ((↑) : Rat -> K)
-/
theorem mk_le_mk_iff_ratCast {x y : R} : mk x ≤ mk y ↔ ∃ q : ℚ, 0 < q ∧ q * |y| ≤ |x| := by
  simpa using mk_le_mk_iff_denselyOrdered (Rat.castHom _) Rat.cast_strictMono (x := x)

end Field
end ArchimedeanClass

