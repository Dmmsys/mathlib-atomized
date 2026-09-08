/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Balance
public import Mathlib.Data.Complex.Basic

/-!
# Finite sums and products of complex numbers
-/

public section

open Fintype
open scoped BigOperators

namespace Complex

variable {α : Type*} (s : Finset α)

@[simp, norm_cast]
/-
**Complex.ofReal_prod** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_prod (f : α -> Real) : ((∏ i in s, f i : Real) : Complex) = ∏ i in 
s, (f i : Complex)
参数：f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem ofReal_prod (f : α → ℝ) : ((∏ i ∈ s, f i : ℝ) : ℂ) = ∏ i ∈ s, (f i : ℂ) :=
  map_prod ofRealHom _ _

@[simp, norm_cast]
/-
**Complex.ofReal_sum** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_sum (f : α -> Real) : ((∑ i in s, f i : Real) : Complex) = ∑ i in s
, (f i : Complex)
参数：f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
-/
theorem ofReal_sum (f : α → ℝ) : ((∑ i ∈ s, f i : ℝ) : ℂ) = ∑ i ∈ s, (f i : ℂ) :=
  map_sum ofRealHom _ _

@[simp, norm_cast]
/-
**Complex.ofReal_expect** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：ofReal_expect (f : α -> Real) : (𝔼 i in s, f i : Real) = 𝔼 i in s, (f i : 
Complex)
参数：f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_expect`：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} [inst : AddCo
mmMonoid M] [inst_1 : _root_.Module ℚ≥0 M]   [inst_2 : AddCommMonoid N] [inst_3 
…
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
-/
lemma ofReal_expect (f : α → ℝ) : (𝔼 i ∈ s, f i : ℝ) = 𝔼 i ∈ s, (f i : ℂ) :=
  map_expect ofRealHom ..

@[simp, norm_cast]
/-
**Complex.ofReal_balance** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：ofReal_balance [Fintype α] (f : α -> Real) (a : α) : ((balance f a : Real)
 : Complex) = balance ((↑) ∘ f) a
参数：f : α -> Real；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用引理 `Complex.ofReal_expect`：ofReal_expect (f : α -> Real) : (𝔼 i in s, f i : 
Real) = 𝔼 i in s, (f i : Complex)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofReal_balance [Fintype α] (f : α → ℝ) (a : α) :
    ((balance f a : ℝ) : ℂ) = balance ((↑) ∘ f) a := by simp [balance]
/-
**Complex.ofReal_comp_balance** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {ι : Type u_2} [inst : Fintype ι] (f : ι → ℝ),   Complex.ofReal ∘ Fintyp
e.balance f = Fintype.balance (Complex.ofReal ∘ f)
参数：f : ι → ℝ；Complex.ofReal ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `Complex.ofReal_balance`：ofReal_balance [Fintype α] (f : α -> Real) (a : 
α) : ((balance f a : Real) : Complex) = balance ((↑) ∘ f) a
-/
@[simp] lemma ofReal_comp_balance {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ofReal ∘ balance f = balance (ofReal ∘ f : ι → ℂ) := funext <| ofReal_balance _

@[simp]
/-
**Complex.re_sum** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：re_sum (f : α -> Complex) : (∑ i in s, f i).re = ∑ i in s, (f i).re
参数：f : α -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem re_sum (f : α → ℂ) : (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum reAddGroupHom f s

@[simp]
/-
**Complex.re_expect** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：re_expect (f : α -> Complex) : (𝔼 i in s, f i).re = 𝔼 i in s, (f i).re
参数：f : α -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_expect`：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} [inst : AddCo
mmMonoid M] [inst_1 : _root_.Module ℚ≥0 M]   [inst_2 : AddCommMonoid N] [inst_3 
…
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.re_nnqsmul`：∀ (q : ℚ≥0) (z : ℂ), (q • z).re = q • z.re
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `eq_nnratCast`：eq_nnratCast [DivisionSemiring α] [FunLike F Rat>=0 α] [Ri
ngHomClass F Rat>=0 α] (f : F) (q : Rat>=0) : f q = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma re_expect (f : α → ℂ) : (𝔼 i ∈ s, f i).re = 𝔼 i ∈ s, (f i).re :=
  map_expect (LinearMap.mk reAddGroupHom.toAddHom (by simp)) f s

@[simp]
/-
**Complex.re_balance** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：re_balance [Fintype α] (f : α -> Complex) (a : α) : re (balance f a) = bal
ance (re ∘ f) a
参数：f : α -> Complex；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.re_expect`：re_expect (f : α -> Complex) : (𝔼 i in s, f i).re = 𝔼
 i in s, (f i).re
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma re_balance [Fintype α] (f : α → ℂ) (a : α) : re (balance f a) = balance (re ∘ f) a := by
  simp [balance]
/-
**Complex.re_comp_balance** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {ι : Type u_2} [inst : Fintype ι] (f : ι → ℂ), Complex.re ∘ Fintype.bala
nce f = Fintype.balance (Complex.re ∘ f)
参数：f : ι → ℂ；Complex.re ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `Complex.re_balance`：re_balance [Fintype α] (f : α -> Complex) (a : α) : 
re (balance f a) = balance (re ∘ f) a
-/
@[simp] lemma re_comp_balance {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    re ∘ balance f = balance (re ∘ f) := funext <| re_balance _

@[simp]
/-
**Complex.im_sum** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：im_sum (f : α -> Complex) : (∑ i in s, f i).im = ∑ i in s, (f i).im
参数：f : α -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem im_sum (f : α → ℂ) : (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im :=
  map_sum imAddGroupHom f s

@[simp]
/-
**Complex.im_expect** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：im_expect (f : α -> Complex) : (𝔼 i in s, f i).im = 𝔼 i in s, (f i).im
参数：f : α -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_expect`：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} [inst : AddCo
mmMonoid M] [inst_1 : _root_.Module ℚ≥0 M]   [inst_2 : AddCommMonoid N] [inst_3 
…
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.im_nnqsmul`：∀ (q : ℚ≥0) (z : ℂ), (q • z).im = q • z.im
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `eq_nnratCast`：eq_nnratCast [DivisionSemiring α] [FunLike F Rat>=0 α] [Ri
ngHomClass F Rat>=0 α] (f : F) (q : Rat>=0) : f q = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma im_expect (f : α → ℂ) : (𝔼 i ∈ s, f i).im = 𝔼 i ∈ s, (f i).im :=
  map_expect (LinearMap.mk imAddGroupHom.toAddHom (by simp)) f s

@[simp]
/-
**Complex.im_balance** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：im_balance [Fintype α] (f : α -> Complex) (a : α) : im (balance f a) = bal
ance (im ∘ f) a
参数：f : α -> Complex；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.im_expect`：im_expect (f : α -> Complex) : (𝔼 i in s, f i).im = 𝔼
 i in s, (f i).im
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma im_balance [Fintype α] (f : α → ℂ) (a : α) : im (balance f a) = balance (im ∘ f) a := by
  simp [balance]
/-
**Complex.im_comp_balance** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {ι : Type u_2} [inst : Fintype ι] (f : ι → ℂ), Complex.im ∘ Fintype.bala
nce f = Fintype.balance (Complex.im ∘ f)
参数：f : ι → ℂ；Complex.im ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `Complex.im_balance`：im_balance [Fintype α] (f : α -> Complex) (a : α) : 
im (balance f a) = balance (im ∘ f) a
-/
@[simp] lemma im_comp_balance {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    im ∘ balance f = balance (im ∘ f) := funext <| im_balance _

end Complex

