/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Conversion between `AddMonoidAlgebra` and homogeneous `DirectSum`

This module provides conversions between `AddMonoidAlgebra` and `DirectSum`.
The latter is essentially a dependent version of the former.

Note that since `DirectSum.instMul` combines indices additively, there is no equivalent to
`MonoidAlgebra`.

## Main definitions

* `AddMonoidAlgebra.toDirectSum : AddMonoidAlgebra M ι → (⨁ i : ι, M)`
* `DirectSum.toAddMonoidAlgebra : (⨁ i : ι, M) → AddMonoidAlgebra M ι`
* Bundled equiv versions of the above:
  * `addMonoidAlgebraEquivDirectSum : AddMonoidAlgebra M ι ≃ (⨁ i : ι, M)`
  * `addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ (⨁ i : ι, M)`
  * `addMonoidAlgebraRingEquivDirectSum R : AddMonoidAlgebra M ι ≃+* (⨁ i : ι, M)`
  * `addMonoidAlgebraAlgEquivDirectSum R : AddMonoidAlgebra A ι ≃ₐ[R] (⨁ i : ι, A)`

## Theorems

The defining feature of these operations is that they map `AddMonoidAlgebra.single` to
`DirectSum.of` and vice versa:

* `AddMonoidAlgebra.toDirectSum_single`
* `DirectSum.toAddMonoidAlgebra_of`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to
`AddMonoidAlgebra.toDirectSum`:

* `addMonoidAlgebraAddEquivDirectSum_apply`
* `add_monoid_algebra_lequiv_direct_sum_apply`
* `addMonoidAlgebraAddEquivDirectSum_symm_apply`
* `add_monoid_algebra_lequiv_direct_sum_symm_apply`

## Implementation notes

This file largely just copies the API of `Mathlib/Data/Finsupp/ToDFinsupp.lean`, and reuses the
proofs. Recall that `AddMonoidAlgebra M ι` is defeq to `ι →₀ M` and `⨁ i : ι, M` is defeq to
`Π₀ i : ι, M`.
-/

@[expose] public section


variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

open DirectSum

/-! ### Basic definitions and lemmas -/


section Defs

/-- Interpret an `AddMonoidAlgebra` as a homogeneous `DirectSum`. -/
/-
**AddMonoidAlgebra.toDirectSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidAlgebra.toDirectSum [Semiring M] (f : AddMonoidAlgebra M ι) : ⨁ _
 : ι, M
参数：f : AddMonoidAlgebra M ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret an `AddMonoidAlgebra` as a homogeneous `DirectSum`.
-/
def AddMonoidAlgebra.toDirectSum [Semiring M] (f : AddMonoidAlgebra M ι) : ⨁ _ : ι, M :=
  f.coeff.toDFinsupp

section

variable [DecidableEq ι] [Semiring M]

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_single** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddMonoidAlgebra.toDirectSum_single (i : ι) (m : M) : toDirectSum (single 
i m) = .of _ i m
参数：i : ι；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_single`：Finsupp.toDFinsupp_single (i : ι) (m : M) : (
Finsupp.single i m).toDFinsupp = DFinsupp.single i m
-/
lemma AddMonoidAlgebra.toDirectSum_single (i : ι) (m : M) : toDirectSum (single i m) = .of _ i m :=
  Finsupp.toDFinsupp_single i m

variable [∀ m : M, Decidable (m ≠ 0)]

/-- Interpret a homogeneous `DirectSum` as an `AddMonoidAlgebra`. -/
/-
**DirectSum.toAddMonoidAlgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DirectSum.toAddMonoidAlgebra (f : ⨁ _ : ι, M) : AddMonoidAlgebra M ι
参数：f : ⨁ _ : ι, M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a homogeneous `DirectSum` as an `AddMonoidAlgebra`.
-/
def DirectSum.toAddMonoidAlgebra (f : ⨁ _ : ι, M) : AddMonoidAlgebra M ι := .ofCoeff f.toFinsupp

@[simp]
/-
**DirectSum.toAddMonoidAlgebra_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectSum.toAddMonoidAlgebra_of (i : ι) (m : M) : (DirectSum.of _ i m : ⨁ 
_ : ι, M).toAddMonoidAlgebra = .single i m
参数：i : ι；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `DFinsupp.toFinsupp_single`：DFinsupp.toFinsupp_single (i : ι) (m : M) : (
DFinsupp.single i m : Π₀ _ : ι, M).toFinsupp = Finsupp.single i m
-/
theorem DirectSum.toAddMonoidAlgebra_of (i : ι) (m : M) :
    (DirectSum.of _ i m : ⨁ _ : ι, M).toAddMonoidAlgebra = .single i m := by
  ext : 1; exact DFinsupp.toFinsupp_single i m

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra (f : AddMonoidAlgebra M ι)
 : f.toDirectSum.toAddMonoidAlgebra = f
参数：f : AddMonoidAlgebra M ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.toDFinsupp_toFinsupp`：Finsupp.toDFinsupp_toFinsupp (f : ι ->₀ M)
 : f.toDFinsupp.toFinsupp = f
-/
theorem AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra (f : AddMonoidAlgebra M ι) :
    f.toDirectSum.toAddMonoidAlgebra = f := by ext : 1; exact Finsupp.toDFinsupp_toFinsupp _

@[simp]
/-
**DirectSum.toAddMonoidAlgebra_toDirectSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectSum.toAddMonoidAlgebra_toDirectSum (f : ⨁ _ : ι, M) : f.toAddMonoidA
lgebra.toDirectSum = f
参数：f : ⨁ _ : ι, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.toFinsupp_toDFinsupp`：DFinsupp.toFinsupp_toDFinsupp (f : Π₀ _ :
 ι, M) : f.toFinsupp.toDFinsupp = f
-/
theorem DirectSum.toAddMonoidAlgebra_toDirectSum (f : ⨁ _ : ι, M) :
    f.toAddMonoidAlgebra.toDirectSum = f :=
  (DFinsupp.toFinsupp_toDFinsupp (show Π₀ _ : ι, M from f) :)

end

end Defs

/-! ### Lemmas about arithmetic operations -/


section Lemmas

namespace AddMonoidAlgebra

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：toDirectSum_zero [Semiring M] : (0 : AddMonoidAlgebra M ι).toDirectSum = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_zero`：toDFinsupp_zero [Zero M] : (0 : ι ->₀ M).toDFin
supp = 0
-/
theorem toDirectSum_zero [Semiring M] : (0 : AddMonoidAlgebra M ι).toDirectSum = 0 :=
  Finsupp.toDFinsupp_zero

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_add** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：toDirectSum_add [Semiring M] (f g : AddMonoidAlgebra M ι) : (f + g).toDire
ctSum = f.toDirectSum + g.toDirectSum
参数：f g : AddMonoidAlgebra M ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_add`：toDFinsupp_add [AddZeroClass M] (f g : ι ->₀ M) 
: (f + g).toDFinsupp = f.toDFinsupp + g.toDFinsupp
-/
theorem toDirectSum_add [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f + g).toDirectSum = f.toDirectSum + g.toDirectSum :=
  Finsupp.toDFinsupp_add _ _

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_natCast** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgeb
ra`。
形式化陈述：toDirectSum_natCast [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : Nat) :
 (n : AddMonoidAlgebra M ι).toDirectSum = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_single`：Finsupp.toDFinsupp_single (i : ι) (m : M) : (
Finsupp.single i m).toDFinsupp = DFinsupp.single i m
-/
theorem toDirectSum_natCast [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : ℕ) :
    (n : AddMonoidAlgebra M ι).toDirectSum = n :=
  Finsupp.toDFinsupp_single _ _

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra
`。
形式化陈述：toDirectSum_ofNat [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : Nat) [n.
AtLeastTwo] : (ofNat(n) : AddMonoidAlgebra M ι).toDirectSum = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_single`：Finsupp.toDFinsupp_single (i : ι) (m : M) : (
Finsupp.single i m).toDFinsupp = DFinsupp.single i m
-/
theorem toDirectSum_ofNat [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : AddMonoidAlgebra M ι).toDirectSum = ofNat(n) :=
  Finsupp.toDFinsupp_single _ _

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_sub** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：toDirectSum_sub [Ring M] (f g : AddMonoidAlgebra M ι) : (f - g).toDirectSu
m = f.toDirectSum - g.toDirectSum
参数：f g : AddMonoidAlgebra M ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_sub`：toDFinsupp_sub [AddGroup M] (f g : ι ->₀ M) : (f
 - g).toDFinsupp = f.toDFinsupp - g.toDFinsupp
-/
theorem toDirectSum_sub [Ring M] (f g : AddMonoidAlgebra M ι) :
    (f - g).toDirectSum = f.toDirectSum - g.toDirectSum :=
  Finsupp.toDFinsupp_sub _ _

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_neg** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：toDirectSum_neg [Ring M] (f : AddMonoidAlgebra M ι) : (-f).toDirectSum = -
 f.toDirectSum
参数：f : AddMonoidAlgebra M ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_neg`：toDFinsupp_neg [AddGroup M] (f : ι ->₀ M) : (-f)
.toDFinsupp = -f.toDFinsupp
-/
theorem toDirectSum_neg [Ring M] (f : AddMonoidAlgebra M ι) :
    (-f).toDirectSum = - f.toDirectSum :=
  Finsupp.toDFinsupp_neg _

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_intCast** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgeb
ra`。
形式化陈述：toDirectSum_intCast [DecidableEq ι] [AddMonoid ι] [Ring M] (z : Int) : (In
t.cast z : AddMonoidAlgebra M ι).toDirectSum = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_single`：Finsupp.toDFinsupp_single (i : ι) (m : M) : (
Finsupp.single i m).toDFinsupp = DFinsupp.single i m
-/
theorem toDirectSum_intCast [DecidableEq ι] [AddMonoid ι] [Ring M] (z : ℤ) :
    (Int.cast z : AddMonoidAlgebra M ι).toDirectSum = z :=
  Finsupp.toDFinsupp_single _ _

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_one** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：toDirectSum_one [DecidableEq ι] [Zero ι] [Semiring M] : (1 : AddMonoidAlge
bra M ι).toDirectSum = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_single`：Finsupp.toDFinsupp_single (i : ι) (m : M) : (
Finsupp.single i m).toDFinsupp = DFinsupp.single i m
-/
theorem toDirectSum_one [DecidableEq ι] [Zero ι] [Semiring M] :
    (1 : AddMonoidAlgebra M ι).toDirectSum = 1 :=
  Finsupp.toDFinsupp_single _ _

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：toDirectSum_mul [DecidableEq ι] [AddMonoid ι] [Semiring M] (f g : AddMonoi
dAlgebra M ι) : (f * g).toDirectSum = f.toDirectSum * g.toDirectSum
参数：f g : AddMonoidAlgebra M ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.toDirectSum_zero`：toDirectSum_zero [Semiring M] : (0 : 
AddMonoidAlgebra M ι).toDirectSum = 0
· 使用定理 `AddMonoidAlgebra.toDirectSum_add`：toDirectSum_add [Semiring M] (f g : Ad
dMonoidAlgebra M ι) : (f + g).toDirectSum = f.toDirectSum + g.toDirectSum
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddMonoidHom.map_mul_iff`：map_mul_iff (f : R ->+ S) : (forall x y, f (x 
* y) = f x * f y) ↔ (mul : R ->+ R ->+ R).compr₂ f = (mul.comp f).compl₂ f
· 使用定理 `AddMonoidAlgebra.addHom_ext'`：∀ {R : Type u_1} {M : Type u_4} [inst : Se
miring R] {N : Type u_8} [inst_1 : AddZeroClass N]   ⦃f g : AddMonoidAlgebra R M
 →+ N⦄,   (∀ (m : …
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidAlgebra.singleAddHom_apply`：∀ {R : Type u_1} {M : Type u_4} [in
st : Semiring R] (m : M) (r : R),   (AddMonoidAlgebra.singleAddHom m) r = AddMon
oidAlgebra.single m r
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用引理 `AddMonoidAlgebra.toDirectSum_single`：AddMonoidAlgebra.toDirectSum_single
 (i : ι) (m : M) : toDirectSum (single i m) = .of _ i m
· 使用定理 `DirectSum.of_mul_of`：of_mul_of {i j} (a : A i) (b : A j) : of A i a * of
 A j b = of _ (i + j) (GradedMonoid.GMul.mul a b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDirectSum_mul [DecidableEq ι] [AddMonoid ι] [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f * g).toDirectSum = f.toDirectSum * g.toDirectSum := by
  let to_hom : AddMonoidAlgebra M ι →+ ⨁ _ : ι, M :=
  { toFun := toDirectSum
    map_zero' := toDirectSum_zero
    map_add' := toDirectSum_add }
  change to_hom (f * g) = to_hom f * to_hom g
  revert f g
  rw [AddMonoidHom.map_mul_iff]
  ext xi xv yi yv : 4
  simp [to_hom, AddMonoidAlgebra.single_mul_single, DirectSum.of_mul_of]

end AddMonoidAlgebra

namespace DirectSum

variable [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**DirectSum.toAddMonoidAlgebra_zero** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoidAlgebra_zero [Semiring M] [forall m : M, Decidable (m != 0)] : 
toAddMonoidAlgebra 0 = (0 : AddMonoidAlgebra M ι)
参数：m != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.toFinsupp_zero`：toFinsupp_zero [Zero M] [forall m : M, Decidabl
e (m != 0)] : toFinsupp 0 = (0 : ι ->₀ M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toAddMonoidAlgebra_zero [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    toAddMonoidAlgebra 0 = (0 : AddMonoidAlgebra M ι) := by simp [toAddMonoidAlgebra]

@[simp]
/-
**DirectSum.toAddMonoidAlgebra_add** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoidAlgebra_add [Semiring M] [forall m : M, Decidable (m != 0)] (f 
g : ⨁ _ : ι, M) : (f + g).toAddMonoidAlgebra = toAddMonoidAlgebra f + toAddMonoi
dAlgebra g
参数：m != 0；f g : ⨁ _ : ι, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toAddMonoidAlgebra_add [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f + g).toAddMonoidAlgebra = toAddMonoidAlgebra f + toAddMonoidAlgebra g := by
  ext; simp [toAddMonoidAlgebra]

@[simp]
/-
**DirectSum.toAddMonoidAlgebra_natCast** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoidAlgebra_natCast [AddMonoid ι] [Semiring M] [forall m : M, Decid
able (m != 0)] (n : Nat) : (n : ⨁ _ : ι, M).toAddMonoidAlgebra = n
参数：m != 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `DFinsupp.toFinsupp_single`：DFinsupp.toFinsupp_single (i : ι) (m : M) : (
DFinsupp.single i m : Π₀ _ : ι, M).toFinsupp = Finsupp.single i m
-/
theorem toAddMonoidAlgebra_natCast [AddMonoid ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (n : ℕ) :
    (n : ⨁ _ : ι, M).toAddMonoidAlgebra = n := by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]
/-
**DirectSum.toAddMonoidAlgebra_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoidAlgebra_ofNat [AddMonoid ι] [Semiring M] [forall m : M, Decidab
le (m != 0)] (n : Nat) [n.AtLeastTwo] : (ofNat(n) : ⨁ _ : ι, M).toAddMonoidAlgeb
ra = ofNat(n)
参数：m != 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.toAddMonoidAlgebra_natCast`：toAddMonoidAlgebra_natCast [AddMon
oid ι] [Semiring M] [forall m : M, Decidable (m != 0)] (n : Nat) : (n : ⨁ _ : ι,
 M).toAddMonoidAlgebra = n
-/
theorem toAddMonoidAlgebra_ofNat [AddMonoid ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (n : ℕ)
    [n.AtLeastTwo] :
    (ofNat(n) : ⨁ _ : ι, M).toAddMonoidAlgebra = ofNat(n) :=
  toAddMonoidAlgebra_natCast _

@[simp]
/-
**DirectSum.toAddMonoidAlgebra_sub** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoidAlgebra_sub [Ring M] [forall m : M, Decidable (m != 0)] (f g : 
⨁ _ : ι, M) : (f - g).toAddMonoidAlgebra = toAddMonoidAlgebra f - toAddMonoidAlg
ebra g
参数：m != 0；f g : ⨁ _ : ι, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `DFinsupp.toFinsupp_sub`：toFinsupp_sub [AddGroup M] [forall m : M, Decida
ble (m != 0)] (f g : Π₀ _ : ι, M) : (toFinsupp (f - g) : ι ->₀ M) = toFinsupp f 
- toFinsupp …
-/
theorem toAddMonoidAlgebra_sub [Ring M] [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f - g).toAddMonoidAlgebra = toAddMonoidAlgebra f - toAddMonoidAlgebra g := by
  ext : 1; exact DFinsupp.toFinsupp_sub ..

@[simp]
/-
**DirectSum.toAddMonoidAlgebra_neg** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoidAlgebra_neg [Ring M] [forall m : M, Decidable (m != 0)] (f : ⨁ 
_ : ι, M) : (-f).toAddMonoidAlgebra = -toAddMonoidAlgebra f
参数：m != 0；f : ⨁ _ : ι, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `DFinsupp.toFinsupp_neg`：toFinsupp_neg [AddGroup M] [forall m : M, Decida
ble (m != 0)] (f : Π₀ _ : ι, M) : (toFinsupp (-f) : ι ->₀ M) = -toFinsupp f
-/
theorem toAddMonoidAlgebra_neg [Ring M] [∀ m : M, Decidable (m ≠ 0)] (f : ⨁ _ : ι, M) :
    (-f).toAddMonoidAlgebra = -toAddMonoidAlgebra f := by
  ext : 1; exact DFinsupp.toFinsupp_neg ..

@[simp]
/-
**DirectSum.toAddMonoidAlgebra_intCast** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoidAlgebra_intCast [AddMonoid ι] [Ring M] [forall m : M, Decidable
 (m != 0)] (z : Int) : (z : ⨁ _ : ι, M).toAddMonoidAlgebra = z
参数：m != 0；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `DFinsupp.toFinsupp_single`：DFinsupp.toFinsupp_single (i : ι) (m : M) : (
DFinsupp.single i m : Π₀ _ : ι, M).toFinsupp = Finsupp.single i m
-/
theorem toAddMonoidAlgebra_intCast [AddMonoid ι] [Ring M] [∀ m : M, Decidable (m ≠ 0)] (z : ℤ) :
    (z : ⨁ _ : ι, M).toAddMonoidAlgebra = z := by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]
/-
**DirectSum.toAddMonoidAlgebra_one** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoidAlgebra_one [Zero ι] [Semiring M] [forall m : M, Decidable (m !
= 0)] : (1 : ⨁ _ : ι, M).toAddMonoidAlgebra = 1
参数：m != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `DFinsupp.toFinsupp_single`：DFinsupp.toFinsupp_single (i : ι) (m : M) : (
DFinsupp.single i m : Π₀ _ : ι, M).toFinsupp = Finsupp.single i m
-/
theorem toAddMonoidAlgebra_one [Zero ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    (1 : ⨁ _ : ι, M).toAddMonoidAlgebra = 1 := by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]
/-
**DirectSum.toAddMonoidAlgebra_mul** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoidAlgebra_mul [AddMonoid ι] [Semiring M] [forall m : M, Decidable
 (m != 0)] (f g : ⨁ _ : ι, M) : (f * g).toAddMonoidAlgebra = toAddMonoidAlgebra 
f * toAddMonoidAlgebra g
参数：m != 0；f g : ⨁ _ : ι, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra`：AddMonoidAlgebra.toDire
ctSum_toAddMonoidAlgebra (f : AddMonoidAlgebra M ι) : f.toDirectSum.toAddMonoidA
lgebra = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.toAddMonoidAlgebra_toDirectSum`：DirectSum.toAddMonoidAlgebra_t
oDirectSum (f : ⨁ _ : ι, M) : f.toAddMonoidAlgebra.toDirectSum = f
· 使用定理 `AddMonoidAlgebra.toDirectSum_mul`：toDirectSum_mul [DecidableEq ι] [AddMo
noid ι] [Semiring M] (f g : AddMonoidAlgebra M ι) : (f * g).toDirectSum = f.toDi
rectSum * g.toDirectSu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toAddMonoidAlgebra_mul [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f * g).toAddMonoidAlgebra = toAddMonoidAlgebra f * toAddMonoidAlgebra g := by
  apply_fun AddMonoidAlgebra.toDirectSum
  · simp
  · apply Function.LeftInverse.injective
    apply AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra

end DirectSum

end Lemmas

/-! ### Bundled `Equiv`s -/


section Equivs

/-- `AddMonoidAlgebra.toDirectSum` and `DirectSum.toAddMonoidAlgebra` together form an
equiv. -/
@[simps -fullyApplied]
/-
**addMonoidAlgebraEquivDirectSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：addMonoidAlgebraEquivDirectSum [DecidableEq ι] [Semiring M] [forall m : M,
 Decidable (m != 0)] : AddMonoidAlgebra M ι ≃ ⨁ _ : ι, M where toFun
参数：m != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddMonoidAlgebra.toDirectSum` and `DirectSum.toAddMonoidAlgebra` together form 
an
equiv.
-/
def addMonoidAlgebraEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃ ⨁ _ : ι, M where
  toFun := AddMonoidAlgebra.toDirectSum
  invFun := DirectSum.toAddMonoidAlgebra

/-- The additive version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps! -fullyApplied]
/-
**addMonoidAlgebraAddEquivDirectSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：addMonoidAlgebraAddEquivDirectSum [DecidableEq ι] [Semiring M] [forall m :
 M, Decidable (m != 0)] : AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M where toEquiv
参数：m != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.toDirectSum_add`：toDirectSum_add [Semiring M] (f g : Ad
dMonoidAlgebra M ι) : (f + g).toDirectSum = f.toDirectSum + g.toDirectSum

--- 原说明 ---
The additive version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`.
-/
def addMonoidAlgebraAddEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M where
  toEquiv := addMonoidAlgebraEquivDirectSum
  map_add' := AddMonoidAlgebra.toDirectSum_add

/-- The ring version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps -fullyApplied]
/-
**addMonoidAlgebraRingEquivDirectSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：addMonoidAlgebraRingEquivDirectSum [DecidableEq ι] [AddMonoid ι] [Semiring
 M] [forall m : M, Decidable (m != 0)] : AddMonoidAlgebra M ι ≃+* ⨁ _ : ι, M
参数：m != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.toDirectSum_mul`：toDirectSum_mul [DecidableEq ι] [AddMo
noid ι] [Semiring M] (f g : AddMonoidAlgebra M ι) : (f * g).toDirectSum = f.toDi
rectSum * g.toDirectSu…

--- 原说明 ---
The ring version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`.
-/
def addMonoidAlgebraRingEquivDirectSum [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] : AddMonoidAlgebra M ι ≃+* ⨁ _ : ι, M :=
  { (addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_mul' := AddMonoidAlgebra.toDirectSum_mul }

/-- The algebra version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps -fullyApplied]
/-
**addMonoidAlgebraAlgEquivDirectSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：addMonoidAlgebraAlgEquivDirectSum [DecidableEq ι] [AddMonoid ι] [CommSemir
ing R] [Semiring A] [Algebra R A] [forall m : A, Decidable (m != 0)] : AddMonoid
Algebra A ι ≃ₐ[R] ⨁ _ : ι, A
参数：m != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`.
-/
def addMonoidAlgebraAlgEquivDirectSum [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
    [Algebra R A] [∀ m : A, Decidable (m ≠ 0)] : AddMonoidAlgebra A ι ≃ₐ[R] ⨁ _ : ι, A :=
  { (addMonoidAlgebraRingEquivDirectSum : AddMonoidAlgebra A ι ≃+* ⨁ _ : ι, A) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    commutes' := fun _r => AddMonoidAlgebra.toDirectSum_single _ _ }

@[simp]
/-
**AddMonoidAlgebra.toDirectSum_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidAlgebra.toDirectSum_pow [DecidableEq ι] [AddMonoid ι] [Semiring M
] (f : AddMonoidAlgebra M ι) (n : Nat) : (f ^ n).toDirectSum = f.toDirectSum ^ n
参数：f : AddMonoidAlgebra M ι；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem AddMonoidAlgebra.toDirectSum_pow [DecidableEq ι] [AddMonoid ι] [Semiring M]
    (f : AddMonoidAlgebra M ι) (n : ℕ) :
    (f ^ n).toDirectSum = f.toDirectSum ^ n := by
  classical exact map_pow addMonoidAlgebraRingEquivDirectSum f n

@[simp]
/-
**DirectSum.toAddMonoidAlgebra_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectSum.toAddMonoidAlgebra_pow [DecidableEq ι] [AddMonoid ι] [Semiring M
] [forall m : M, Decidable (m != 0)] (f : ⨁ _ : ι, M) (n : Nat) : (f ^ n).toAddM
onoidAlgebra = toAddMonoidAlgebra f ^ n
参数：m != 0；f : ⨁ _ : ι, M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem DirectSum.toAddMonoidAlgebra_pow [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] (f : ⨁ _ : ι, M) (n : ℕ) :
    (f ^ n).toAddMonoidAlgebra = toAddMonoidAlgebra f ^ n := by
  exact map_pow addMonoidAlgebraRingEquivDirectSum.symm f n

end Equivs

