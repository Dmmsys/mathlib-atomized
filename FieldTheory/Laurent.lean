/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Laurent expansions of rational functions

## Main declarations

* `RatFunc.laurent`: the Laurent expansion of the rational function `f` at `r`, as an `AlgHom`.
* `RatFunc.laurent_injective`: the Laurent expansion at `r` is unique

## Implementation details

Implemented as the quotient of two Taylor expansions, over domains.
An auxiliary definition is provided first to make the construction of the `AlgHom` easier,
  which works on `CommRing` which are not necessarily domains.
-/

@[expose] public section


universe u

namespace RatFunc

noncomputable section

open Polynomial

open scoped nonZeroDivisors

variable {R : Type u} [CommRing R] (r s : R) (p q : R[X]) (f : R⟮X⟯)

/-
**RatFunc.taylor_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：taylor_mem_nonZeroDivisors (hp : p in R[X]⁰) : taylor r p in R[X]⁰
参数：hp : p in R[X]⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nonZeroDivisors_iff_right`：mem_nonZeroDivisors_iff_right : r in M₀⁰ 
↔ forall x, x * r = 0 -> x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Polynomial.taylor_zero'`：taylor_zero' : taylor (0 : R) = LinearMap.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.map_eq_zero_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8
} {M₃ : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddComm
Monoid M] [inst…
· 使用定理 `Polynomial.taylor_injective`：taylor_injective (r : R) : Function.Injecti
ve (taylor r)
· 使用定理 `mul_right_mem_nonZeroDivisors_eq_zero_iff`：mul_right_mem_nonZeroDivisors
_eq_zero_iff (hr : r in M₀⁰) : x * r = 0 ↔ x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.taylor_mul`：taylor_mul (p q : R[X]) : taylor r (p * q) = tayl
or r p * taylor r q
· 使用定理 `Polynomial.taylor_taylor`：taylor_taylor (f : R[X]) (r s : R) : taylor r 
(taylor s f) = taylor (r + s) f
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem taylor_mem_nonZeroDivisors (hp : p ∈ R[X]⁰) : taylor r p ∈ R[X]⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have : x = taylor (r - r) x := by simp
  rwa [this, sub_eq_add_neg, ← taylor_taylor, ← taylor_mul,
    LinearMap.map_eq_zero_iff _ (taylor_injective _), mul_right_mem_nonZeroDivisors_eq_zero_iff hp,
    LinearMap.map_eq_zero_iff _ (taylor_injective _)] at hx

/-- The Laurent expansion of rational functions about a value.
Auxiliary definition, usage when over integral domains should prefer `RatFunc.laurent`. -/
/-
**RatFunc.laurentAux** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：laurentAux : R⟮X⟯ ->+* R⟮X⟯
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.taylor_mem_nonZeroDivisors`：taylor_mem_nonZeroDivisors (hp : p i
n R[X]⁰) : taylor r p in R[X]⁰

--- 原说明 ---
The Laurent expansion of rational functions about a value.
Auxiliary definition, usage when over integral domains should prefer `RatFunc.la
urent`.
-/
def laurentAux : R⟮X⟯ →+* R⟮X⟯ :=
  RatFunc.mapRingHom
    ( { toFun := taylor r
        map_add' := map_add (taylor r)
        map_mul' := taylor_mul _
        map_zero' := map_zero (taylor r)
        map_one' := taylor_one r } : R[X] →+* R[X])
    (taylor_mem_nonZeroDivisors _)
/-
**RatFunc.laurentAux_ofFractionRing_mk** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：laurentAux_ofFractionRing_mk (q : R[X]⁰) : laurentAux r (ofFractionRing (L
ocalization.mk p q)) = ofFractionRing (.mk (taylor r p) ⟨taylor r q, taylor_mem_
nonZeroDivisors r q q.prop⟩)
参数：q : R[X]⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.map_apply_ofFractionRing_mk`：map_apply_ofFractionRing_mk [Monoid
HomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ <= S[X]⁰.comap φ) (n : R[X]) (d : R[X]
⁰) : map φ hφ (ofFraction…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RatFunc.taylor_mem_nonZeroDivisors`：taylor_mem_nonZeroDivisors (hp : p i
n R[X]⁰) : taylor r p in R[X]⁰
-/
theorem laurentAux_ofFractionRing_mk (q : R[X]⁰) :
    laurentAux r (ofFractionRing (Localization.mk p q)) =
      ofFractionRing (.mk (taylor r p) ⟨taylor r q, taylor_mem_nonZeroDivisors r q q.prop⟩) :=
  map_apply_ofFractionRing_mk _ _ _ _

variable [IsDomain R]
/-
**RatFunc.laurentAux_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：laurentAux_div : laurentAux r (algebraMap _ _ p / algebraMap _ _ q) = alge
braMap _ _ (taylor r p) / algebraMap _ _ (taylor r q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.map_apply_div`：map_apply_div {R F : Type*} [CommRing R] [IsDomai
n R] [FunLike F K[X] R[X]] [MonoidWithZeroHomClass F K[X] R[X]] (φ : F) (hφ : K[
X]⁰ <= R[X]…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RatFunc.taylor_mem_nonZeroDivisors`：taylor_mem_nonZeroDivisors (hp : p i
n R[X]⁰) : taylor r p in R[X]⁰
-/
theorem laurentAux_div :
    laurentAux r (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q) :=
  -- Porting note: added `by exact taylor_mem_nonZeroDivisors r`
  map_apply_div _ (by exact taylor_mem_nonZeroDivisors r) _ _

@[simp]
/-
**RatFunc.laurentAux_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：laurentAux_algebraMap : laurentAux r (algebraMap _ _ p) = algebraMap _ _ (
taylor r p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.mk_one`：mk_one (x : K[X]) : RatFunc.mk x 1 = algebraMap _ _ x
· 使用定理 `RatFunc.mk_eq_div`：mk_eq_div (p q : K[X]) : RatFunc.mk p q = algebraMap 
_ _ p / algebraMap _ _ q
· 使用定理 `RatFunc.laurentAux_div`：laurentAux_div : laurentAux r (algebraMap _ _ p 
/ algebraMap _ _ q) = algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q)
· 使用定理 `Polynomial.taylor_one`：taylor_one : taylor r (1 : R[X]) = C 1
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
-/
theorem laurentAux_algebraMap : laurentAux r (algebraMap _ _ p) = algebraMap _ _ (taylor r p) := by
  rw [← mk_one, ← mk_one, mk_eq_div, laurentAux_div, mk_eq_div, taylor_one, map_one, map_one]

/-- The Laurent expansion of rational functions about a value. -/
/-
**RatFunc.laurent** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：laurent : R⟮X⟯ ->ₐ[R] R⟮X⟯
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.taylor_mem_nonZeroDivisors`：taylor_mem_nonZeroDivisors (hp : p i
n R[X]⁰) : taylor r p in R[X]⁰

--- 原说明 ---
The Laurent expansion of rational functions about a value.
-/
def laurent : R⟮X⟯ →ₐ[R] R⟮X⟯ :=
  RatFunc.mapAlgHom (.ofLinearMap (taylor r) (taylor_one _) (taylor_mul _))
    (taylor_mem_nonZeroDivisors _)
/-
**RatFunc.laurent_div** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：laurent_div : laurent r (algebraMap _ _ p / algebraMap _ _ q) = algebraMap
 _ _ (taylor r p) / algebraMap _ _ (taylor r q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.laurentAux_div`：laurentAux_div : laurentAux r (algebraMap _ _ p 
/ algebraMap _ _ q) = algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q)
-/
theorem laurent_div :
    laurent r (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q) :=
  laurentAux_div r p q

@[simp]
/-
**RatFunc.laurent_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：laurent_algebraMap : laurent r (algebraMap _ _ p) = algebraMap _ _ (taylor
 r p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.laurentAux_algebraMap`：laurentAux_algebraMap : laurentAux r (alg
ebraMap _ _ p) = algebraMap _ _ (taylor r p)
-/
theorem laurent_algebraMap : laurent r (algebraMap _ _ p) = algebraMap _ _ (taylor r p) :=
  laurentAux_algebraMap _ _

@[simp]
/-
**RatFunc.laurent_X** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：laurent_X : laurent r X = X + C r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.algebraMap_X`：algebraMap_X : algebraMap K[X] K⟮X⟯ Polynomial.X =
 X
· 使用定理 `RatFunc.laurent_algebraMap`：laurent_algebraMap : laurent r (algebraMap _
 _ p) = algebraMap _ _ (taylor r p)
· 使用定理 `Polynomial.taylor_X`：taylor_X : taylor r X = X + C r
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RatFunc.algebraMap_C`：algebraMap_C (a : K) : algebraMap K[X] K⟮X⟯ (Polyn
omial.C a) = C a
-/
theorem laurent_X : laurent r X = X + C r := by
  rw [← algebraMap_X, laurent_algebraMap, taylor_X, map_add, algebraMap_C]

@[simp]
/-
**RatFunc.laurent_C** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：laurent_C (x : R) : laurent r (C x) = C x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.algebraMap_C`：algebraMap_C (a : K) : algebraMap K[X] K⟮X⟯ (Polyn
omial.C a) = C a
· 使用定理 `RatFunc.laurent_algebraMap`：laurent_algebraMap : laurent r (algebraMap _
 _ p) = algebraMap _ _ (taylor r p)
· 使用定理 `Polynomial.taylor_C`：taylor_C (x : R) : taylor r (C x) = C x
-/
theorem laurent_C (x : R) : laurent r (C x) = C x := by
  rw [← algebraMap_C, laurent_algebraMap, taylor_C]

@[simp]
/-
**RatFunc.laurent_at_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：laurent_at_zero : laurent 0 f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.induction_on`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDom
ain K] {P : RatFunc K → Prop} (x : RatFunc K),   (∀ (p q : Polynomial K),       
q ≠ 0 → P …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RatFunc.laurent_algebraMap`：laurent_algebraMap : laurent r (algebraMap _
 _ p) = algebraMap _ _ (taylor r p)
· 使用定理 `Polynomial.taylor_zero'`：taylor_zero' : taylor (0 : R) = LinearMap.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem laurent_at_zero : laurent 0 f = f := by induction f using RatFunc.induction_on; simp
/-
**RatFunc.laurent_laurent** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：laurent_laurent : laurent r (laurent s f) = laurent (r + s) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.induction_on`：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDom
ain K] {P : RatFunc K → Prop} (x : RatFunc K),   (∀ (p q : Polynomial K),       
q ≠ 0 → P …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RatFunc.laurent_div`：laurent_div : laurent r (algebraMap _ _ p / algebra
Map _ _ q) = algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.taylor_taylor`：taylor_taylor (f : R[X]) (r s : R) : taylor r 
(taylor s f) = taylor (r + s) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem laurent_laurent : laurent r (laurent s f) = laurent (r + s) f := by
  induction f using RatFunc.induction_on
  simp_rw [laurent_div, taylor_taylor]
/-
**RatFunc.laurent_injective** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：laurent_injective : Function.Injective (laurent r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RatFunc.laurent_laurent`：laurent_laurent : laurent r (laurent s f) = lau
rent (r + s) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `RatFunc.laurent_at_zero`：laurent_at_zero : laurent 0 f = f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem laurent_injective : Function.Injective (laurent r) := fun _ _ h => by
  simpa [laurent_laurent] using congr_arg (laurent (-r)) h

end

end RatFunc

