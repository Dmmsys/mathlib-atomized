/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Multivariate Fourier series

In this file we define the Fourier series of an L² function on the `d`-dimensional unit circle, and
show that it converges to the function in the L² norm. We also prove uniform convergence of the
Fourier series if `f` is continuous and the sequence of its Fourier coefficients is summable.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate ENNReal

open Set Algebra Submodule MeasureTheory

-- some instances for unit circle

/-- In this file we normalise the measure on `ℝ / ℤ` to have total volume 1. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The measure on `ℝ / ℤ` is a Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The measure on `ℝ / ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

section Monomials

variable (n : d → ℤ)

/-- Exponential monomials in `d` variables. -/
/-
**UnitAddTorus.mFourier** 是 Mathlib 中的一个定义，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourier : C(UnitAddTorus d, Complex) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Exponential monomials in `d` variables.
-/
def mFourier : C(UnitAddTorus d, ℂ) where
  toFun x := ∏ i : d, fourier (n i) (x i)
  continuous_toFun := by fun_prop

variable {n} {x : UnitAddTorus d}
/-
**UnitAddTorus.mFourier_neg** 是 Mathlib 中的一个引理，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourier_neg : mFourier (-n) x = conj (mFourier n x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `fourier_neg`：fourier_neg {n : Int} {x : AddCircle T} : fourier (-n) x = 
conj (fourier n x)
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mFourier_neg : mFourier (-n) x = conj (mFourier n x) := by
  simp only [mFourier, Pi.neg_apply, fourier_neg, ContinuousMap.coe_mk, map_prod]
/-
**UnitAddTorus.mFourier_add** 是 Mathlib 中的一个引理，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourier_add {m : d -> Int} : mFourier (m + n) x = mFourier m x * mFourier
 n x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `fourier_add`：fourier_add {m n : Int} {x : AddCircle T} : fourier (m + n)
 x = fourier m x * fourier n x
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mFourier_add {m : d → ℤ} : mFourier (m + n) x = mFourier m x * mFourier n x := by
  simp only [mFourier, Pi.add_apply, fourier_add, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]
/-
**UnitAddTorus.mFourier_zero** 是 Mathlib 中的一个引理，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourier_zero : mFourier (0 : d -> Int) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `fourier_zero`：fourier_zero {x : AddCircle T} : fourier 0 x = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mFourier_zero : mFourier (0 : d → ℤ) = 1 := by
  ext x
  simp only [mFourier, Pi.zero_apply, fourier_zero, Finset.prod_const_one, ContinuousMap.coe_mk,
    ContinuousMap.one_apply]
/-
**UnitAddTorus.mFourier_norm** 是 Mathlib 中的一个引理，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourier_norm : ‖mFourier n‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMap.norm_le`：norm_le {C : Real} (C0 : (0 : Real) <= C) : ‖f‖ <
= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `norm_prod`：norm_prod (s : Finset β) (f : β -> α) : ‖∏ b in s, f b‖ = ∏ b
 in s, ‖f b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Circle.norm_coe`：norm_coe (z : Circle) : ‖(z : Complex)‖ = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `fourier_eval_zero`：fourier_eval_zero (n : Int) : fourier n (0 : AddCircl
e T) = 1
· 使用定理 `CStarRing.norm_one`：norm_one [Nontrivial E] : ‖(1 : E)‖ = 1
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousMap.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
-/
lemma mFourier_norm : ‖mFourier n‖ = 1 := by
  apply le_antisymm
  · refine (ContinuousMap.norm_le _ zero_le_one).mpr fun i ↦ ?_
    simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
      Finset.prod_const_one, le_rfl]
  · refine (le_of_eq ?_).trans ((mFourier n).norm_coe_le_norm fun _ ↦ 0)
    simp only [mFourier, ContinuousMap.coe_mk, fourier_eval_zero, Finset.prod_const_one,
      CStarRing.norm_one]
/-
**UnitAddTorus.mFourier_single** 是 Mathlib 中的一个引理，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourier_single [DecidableEq d] (z : d -> AddCircle (1 : Real)) (i : d) : 
mFourier (Pi.single i 1) z = fourier 1 (z i)
参数：z : d -> AddCircle (1 : Real)；i : d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_mul_prod_compl`：prod_mul_prod_compl [Fintype ι] [DecidableEq
 ι] (s : Finset ι) (f : ι -> M) : (∏ i in s, f i) * ∏ i in sᶜ, f i = ∏ i, f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
· 使用定理 `fourier_zero`：fourier_zero {x : AddCircle T} : fourier 0 x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
lemma mFourier_single [DecidableEq d] (z : d → AddCircle (1 : ℝ)) (i : d) :
    mFourier (Pi.single i 1) z = fourier 1 (z i) := by
  simp_rw [mFourier, ContinuousMap.coe_mk]
  have := Finset.prod_mul_prod_compl {i} (fun j ↦ fourier ((Pi.single i (1 : ℤ) : d → ℤ) j) (z j))
  rw [Finset.prod_singleton, Finset.prod_congr rfl (fun j hj ↦ ?_)] at this
  · rw [← this, Finset.prod_const_one, mul_one, Pi.single_eq_same]
  · rw [Finset.mem_compl, Finset.mem_singleton] at hj
    simp only [Pi.single_eq_of_ne hj, fourier_zero]

end Monomials

section Algebra

/-- The star subalgebra of `C(UnitAddTorus d, ℂ)` generated by `mFourier n` for `n ∈ ℤᵈ`. -/
/-
**UnitAddTorus.mFourierSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourierSubalgebra (d : Type*) [Fintype d] : StarSubalgebra Complex C(Unit
AddTorus d, Complex) where toSubalgebra
参数：d : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ

--- 原说明 ---
The star subalgebra of `C(UnitAddTorus d, ℂ)` generated by `mFourier n` for `n ∈
 ℤᵈ`.
-/
def mFourierSubalgebra (d : Type*) [Fintype d] : StarSubalgebra ℂ C(UnitAddTorus d, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range mFourier)
  star_mem' := by
    change Algebra.adjoin ℂ (range mFourier) ≤ star (Algebra.adjoin ℂ (range mFourier))
    refine adjoin_le ?_
    rintro _ ⟨n, rfl⟩
    refine subset_adjoin ⟨-n, ?_⟩
    ext1 x
    simp only [mFourier_neg, starRingEnd_apply, ContinuousMap.star_apply]

/-- The star subalgebra of `C(UnitAddTorus d, ℂ)` generated by `mFourier n` for `n ∈ ℤᵈ` is in fact
the linear span of these functions. -/
/-
**UnitAddTorus.mFourierSubalgebra_coe** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourierSubalgebra_coe : (mFourierSubalgebra d).toSubalgebra.toSubmodule =
 span Complex (range mFourier)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_eq_span_of_subset`：adjoin_eq_span_of_subset {s : Set A} (
hs : ↑(Submonoid.closure s) subseteq (span R s : Set A)) : Subalgebra.toSubmodul
e (adjoin R s) = span …
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `fourier_zero`：fourier_zero {x : AddCircle T} : fourier 0 x = 1
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `fourier_add'`：fourier_add' {m n : Int} {x : AddCircle T} : toCircle ((m 
+ n) • x :) = fourier m x * fourier n x
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s

--- 原说明 ---
The star subalgebra of `C(UnitAddTorus d, ℂ)` generated by `mFourier n` for `n ∈
 ℤᵈ` is in fact
the linear span of these functions.
-/
theorem mFourierSubalgebra_coe :
    (mFourierSubalgebra d).toSubalgebra.toSubmodule = span ℂ (range mFourier) := by
  apply adjoin_eq_span_of_subset
  refine .trans (fun x ↦ Submonoid.closure_induction (fun _ ↦ id) ⟨0, ?_⟩ ?_) subset_span
  · ext z
    simp only [mFourier, Pi.zero_apply, fourier_zero, Finset.prod_const, one_pow,
      ContinuousMap.coe_mk, ContinuousMap.one_apply]
  · rintro _ _ _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext z
    simp only [mFourier, Pi.add_apply, fourier_apply, fourier_add', Finset.prod_mul_distrib,
      ContinuousMap.coe_mk, ContinuousMap.mul_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- The subalgebra of `C(UnitAddTorus d, ℂ)` generated by `mFourier n` for `n ∈ ℤᵈ` separates
points. -/
/-
**UnitAddTorus.mFourierSubalgebra_separatesPoints** 是 Mathlib 中的一个定理，位于命名空间 `Uni
tAddTorus`。
形式化陈述：mFourierSubalgebra_separatesPoints : (mFourierSubalgebra d).SeparatesPoint
s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用引理 `UnitAddTorus.mFourier_single`：mFourier_single [DecidableEq d] (z : d -> 
AddCircle (1 : Real)) (i : d) : mFourier (Pi.single i 1) z = fourier 1 (z i)
· 使用定理 `fourier_one`：fourier_one {x : AddCircle T} : fourier 1 x = toCircle x
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `AddCircle.injective_toCircle`：injective_toCircle (hT : T != 0) : Functio
n.Injective (@toCircle T)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The subalgebra of `C(UnitAddTorus d, ℂ)` generated by `mFourier n` for `n ∈ ℤᵈ` 
separates
points.
-/
theorem mFourierSubalgebra_separatesPoints : (mFourierSubalgebra d).SeparatesPoints := by
  classical
  intro x y hxy
  rw [Ne, funext_iff, not_forall] at hxy
  obtain ⟨i, hi⟩ := hxy
  refine ⟨_, ⟨mFourier (Pi.single i 1), subset_adjoin ⟨Pi.single i 1, rfl⟩, rfl⟩, ?_⟩
  dsimp only
  rw [mFourier_single, mFourier_single, fourier_one, fourier_one, Ne, Subtype.coe_inj]
  contrapose hi
  exact AddCircle.injective_toCircle one_ne_zero hi

/-- The subalgebra of `C(UnitAddTorus d, ℂ)` generated by `mFourier n` for `n : d → ℤ` is dense. -/
/-
**UnitAddTorus.mFourierSubalgebra_closure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Unit
AddTorus`。
形式化陈述：mFourierSubalgebra_closure_eq_top : (mFourierSubalgebra d).topologicalClos
ure = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoint
s`：ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (A 
: StarSubalgebra 𝕜 C(X, 𝕜)) (hA : A.SeparatesPoints) : A.topolo…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `UnitAddTorus.mFourierSubalgebra_separatesPoints`：mFourierSubalgebra_sepa
ratesPoints : (mFourierSubalgebra d).SeparatesPoints

--- 原说明 ---
The subalgebra of `C(UnitAddTorus d, ℂ)` generated by `mFourier n` for `n : d → 
ℤ` is dense.
-/
theorem mFourierSubalgebra_closure_eq_top : (mFourierSubalgebra d).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    mFourierSubalgebra_separatesPoints

/-- The linear span of the monomials `mFourier n` is dense in `C(UnitAddTorus d, ℂ)`. -/
/-
**UnitAddTorus.span_mFourier_closure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTo
rus`。
形式化陈述：span_mFourier_closure_eq_top : (span Complex (range <| mFourier (d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMap.instContinuousConstSMul`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {R : Type u_3} {M : Type u_5} [inst_1 : TopologicalSpace M]   [inst_
2 : SMul R M] [inst_3 : Con…
· 使用定理 `ContinuousMap.instContinuousAddOfLocallyCompactSpace`：∀ {α : Type u_1} {
β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Locally
CompactSpace α]   [inst_3 : Add β] [inst_4…
· 使用定理 `QuotientAddGroup.instLocallyCompactSpace`：∀ {G : Type u_1} [inst : Topol
ogicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G] [LocallyCompact
Space G]   (N : AddSubgroup G)…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UnitAddTorus.mFourierSubalgebra_coe`：mFourierSubalgebra_coe : (mFourierS
ubalgebra d).toSubalgebra.toSubmodule = span Complex (range mFourier)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`：∀ {α : Type u_
1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Loc
allyCompactSpace α]   [inst_3 : NonUnitalRing …
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMap.instNormedStarGroup`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace α] [inst_1 : SeminormedAddCommGroup β]   [inst_2 : StarAddMo
noid β] [inst_3 : Norme…
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `UnitAddTorus.mFourierSubalgebra_closure_eq_top`：mFourierSubalgebra_closu
re_eq_top : (mFourierSubalgebra d).topologicalClosure = ⊤

--- 原说明 ---
The linear span of the monomials `mFourier n` is dense in `C(UnitAddTorus d, ℂ)`
.
-/
theorem span_mFourier_closure_eq_top :
    (span ℂ (range <| mFourier (d := d))).topologicalClosure = ⊤ := by
  rw [← mFourierSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    mFourierSubalgebra_closure_eq_top

end Algebra

section Integral

variable (a : d → ℝ) {ι : Type*} (b : ι → ℝ)

/-- The measurable equivalence between `UnitAddTorus` and a product of `Ioc` intervals. -/
/-
**UnitAddTorus.measurableEquivPiIoc** 是 Mathlib 中的一个定义，位于命名空间 `UnitAddTorus`。
形式化陈述：measurableEquivPiIoc : UnitAddTorus ι ≃ᵐ {x : ι -> Real // forall i, x i i
n Ioc (b i) (b i + 1)}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measurable equivalence between `UnitAddTorus` and a product of `Ioc` interva
ls.
-/
def measurableEquivPiIoc : UnitAddTorus ι ≃ᵐ {x : ι → ℝ // ∀ i, x i ∈ Ioc (b i) (b i + 1)} :=
  (MeasurableEquiv.piCongrRight fun i => AddCircle.measurableEquivIoc 1 (b i)).trans <|
  MeasurableEquiv.subtypePiEquivPi.symm
/-
**UnitAddTorus.coe_measurableEquivPiIoc** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus`
。
形式化陈述：coe_measurableEquivPiIoc : ⇑(measurableEquivPiIoc b) = fun x => ⟨fun i => 
(AddCircle.equivIoc 1 (b i) (x i)).1, fun i => (AddCircle.equivIoc 1 (b i) (x i)
).2⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_measurableEquivPiIoc :
    ⇑(measurableEquivPiIoc b) = fun x =>
      ⟨fun i => (AddCircle.equivIoc 1 (b i) (x i)).1,
      fun i => (AddCircle.equivIoc 1 (b i) (x i)).2⟩ := rfl

@[simp]
/-
**UnitAddTorus.coe_measurableEquivPiIoc_apply** 是 Mathlib 中的一个定理，位于命名空间 `UnitAdd
Torus`。
形式化陈述：coe_measurableEquivPiIoc_apply (x : UnitAddTorus ι) : (measurableEquivPiIo
c b) x = ⟨fun i => (AddCircle.equivIoc 1 (b i) (x i)).1, fun i => (AddCircle.equ
ivIoc 1 (b i) (x i)).2⟩
参数：x : UnitAddTorus ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_measurableEquivPiIoc_apply (x : UnitAddTorus ι) :
    (measurableEquivPiIoc b) x = ⟨fun i => (AddCircle.equivIoc 1 (b i) (x i)).1,
      fun i => (AddCircle.equivIoc 1 (b i) (x i)).2⟩ := rfl
/-
**UnitAddTorus.coe_symm_measurableEquivPiIoc** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddT
orus`。
形式化陈述：coe_symm_measurableEquivPiIoc : ⇑(measurableEquivPiIoc b).symm = fun x i =
> x.1 i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_measurableEquivPiIoc :
    ⇑(measurableEquivPiIoc b).symm = fun x i => x.1 i := rfl

@[simp]
/-
**UnitAddTorus.coe_symm_measurableEquivPiIoc_apply** 是 Mathlib 中的一个定理，位于命名空间 `Un
itAddTorus`。
形式化陈述：coe_symm_measurableEquivPiIoc_apply (y : {x : ι -> Real // forall i, x i i
n Ioc (b i) (b i + 1)}) : (measurableEquivPiIoc b).symm y = fun i => (y.1 i : Un
itAddCircle)
参数：y : {x : ι -> Real // forall i, x i in Ioc (b i) (b i + 1)}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_measurableEquivPiIoc_apply (y : {x : ι → ℝ // ∀ i, x i ∈ Ioc (b i) (b i + 1)}) :
    (measurableEquivPiIoc b).symm y = fun i => (y.1 i : UnitAddCircle) := rfl

/-- The equivalence `measurableEquivPiIoc` is measure preserving. -/
/-
**UnitAddTorus.measurePreserving_equivPiIoc** 是 Mathlib 中的一个引理，位于命名空间 `UnitAddTo
rus`。
形式化陈述：measurePreserving_equivPiIoc : MeasurePreserving (measurableEquivPiIoc a) 
volume (Measure.comap Subtype.val volume)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `AddCircle.measurable_mk'`：∀ {a : ℝ}, Measurable QuotientAddGroup.mk
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MeasureTheory.Measure.restrict_pi_pi`：restrict_pi_pi (s : (i : ι) -> Set
 (α i)) : (Measure.pi μ).restrict (Set.univ.pi fun i => s i) = .pi (fun i => (μ 
i).restrict (s i))
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The equivalence `measurableEquivPiIoc` is measure preserving.
-/
lemma measurePreserving_equivPiIoc :
    MeasurePreserving (measurableEquivPiIoc a) volume (Measure.comap Subtype.val volume) := by
  refine (⟨(measurableEquivPiIoc a).symm.measurable, symm ?_⟩ :
    MeasurePreserving (measurableEquivPiIoc a).symm _ _).symm
  have := Measure.map_map (μ := volume.comap Subtype.val) (measurable_pi_lambda
    (fun (x : d → ℝ) => (fun i => x i : UnitAddTorus d))
    (fun i => AddCircle.measurable_mk'.comp (measurable_pi_apply i)))
    measurable_subtype_coe (α := {x : d → ℝ // ∀ i, x i ∈ Ioc (a i) (a i + 1)})
  simp only [Function.comp_def] at this
  simp_rw [coe_symm_measurableEquivPiIoc, ← this]
  convert! (measurePreserving_pi _ _ (fun i => AddCircle.measurePreserving_mk 1 (a i))).map_eq.symm
  · simp [volume, AddCircle.haarAddCircle]
  · convert!
    (map_comap_subtype_coe (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc (a := a i))) volume)
    convert! (Measure.restrict_pi_pi (fun i => volume) (fun i => Ioc (a i) (a i + 1))).symm
    grind
/-
**UnitAddTorus.lintegral_preimage** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus`。
形式化陈述：lintegral_preimage (f : UnitAddTorus d -> Real>=0∞) (a : d -> Real) : ∫⁻ x
 : UnitAddTorus d, f x = ∫⁻ (x : d -> Real) in {x : d -> Real | forall i, x i in
 Ioc (a i) (a i + 1)}, f (fun i => x i)
参数：f : UnitAddTorus d -> Real>=0∞；a : d -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用引理 `UnitAddTorus.measurePreserving_equivPiIoc`：measurePreserving_equivPiIoc 
: MeasurePreserving (measurableEquivPiIoc a) volume (Measure.comap Subtype.val v
olume)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_subtype_comap`：lintegral_subtype_comap {s : Set 
α} (hs : MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ x : s, f x ∂(μ.comap (↑)) = ∫
⁻ x in s, f x ∂μ
· 使用定理 `MeasurableSet.univ_pi'`：MeasurableSet.univ_pi' [Countable δ] {t : forall
 i : δ, Set (X i)} (ht : forall i, MeasurableSet (t i)) : MeasurableSet {f : for
all i : δ, X…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.lintegral_map_equiv`：lintegral_map_equiv (f : β -> Real>=0
∞) (g : α ≃ᵐ β) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ
-/
theorem lintegral_preimage (f : UnitAddTorus d → ℝ≥0∞) (a : d → ℝ) :
    ∫⁻ x : UnitAddTorus d, f x =
    ∫⁻ (x : d → ℝ) in {x : d → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)}, f (fun i => x i) := by
  convert! lintegral_map_equiv (μ := volume.comap Subtype.val) f (measurableEquivPiIoc a).symm
  · exact (measurePreserving_equivPiIoc a).symm.map_eq.symm
  · rw [← lintegral_subtype_comap (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc))]
    rfl
/-
**UnitAddTorus.integral_preimage** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus`。
形式化陈述：integral_preimage {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] 
(f : UnitAddTorus d -> E) (a : d -> Real) : ∫ x : UnitAddTorus d, f x = ∫ (x : d
 -> Real) in {x : d -> Real | forall i, x i in Ioc (a i) (a i + 1)}, f (fun i =>
 x i)
参数：f : UnitAddTorus d -> E；a : d -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用引理 `UnitAddTorus.measurePreserving_equivPiIoc`：measurePreserving_equivPiIoc 
: MeasurePreserving (measurableEquivPiIoc a) volume (Measure.comap Subtype.val v
olume)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_subtype_comap`：integral_subtype_comap {α} [Measur
ableSpace α] {μ : Measure α} {s : Set α} (hs : MeasurableSet s) (f : α -> G) : ∫
 x : s, f (x : α) ∂(Measur…
· 使用定理 `MeasurableSet.univ_pi'`：MeasurableSet.univ_pi' [Countable δ] {t : forall
 i : δ, Set (X i)} (ht : forall i, MeasurableSet (t i)) : MeasurableSet {f : for
all i : δ, X…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
-/
theorem integral_preimage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus d → E) (a : d → ℝ) :
    ∫ x : UnitAddTorus d, f x =
    ∫ (x : d → ℝ) in {x : d → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)}, f (fun i => x i) := by
  convert! integral_map_equiv (μ := volume.comap Subtype.val) (measurableEquivPiIoc a).symm f
  · exact (measurePreserving_equivPiIoc a).symm.map_eq.symm
  · rw [← integral_subtype_comap (MeasurableSet.univ_pi' (fun i => measurableSet_Ioc))]
    rfl

end Integral

section Lp

/-- The family of monomials `mFourier n`, parametrized by `n : ℤᵈ` and considered as
elements of the `Lp` space of functions `UnitAddTorus d → ℂ`. -/
/-
**UnitAddTorus.mFourierLp** 是 Mathlib 中的一个缩写定义，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourierLp (p : Real>=0∞) [Fact (1 <= p)] (n : d -> Int) : Lp Complex p (v
olume : Measure (UnitAddTorus d))
参数：p : Real>=0∞；1 <= p；n : d -> Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of monomials `mFourier n`, parametrized by `n : ℤᵈ` and considered as
elements of the `Lp` space of functions `UnitAddTorus d → ℂ`.
-/
abbrev mFourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : d → ℤ) :
    Lp ℂ p (volume : Measure (UnitAddTorus d)) :=
  ContinuousMap.toLp (E := ℂ) p volume ℂ (mFourier n)
/-
**UnitAddTorus.coeFn_mFourierLp** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus`。
形式化陈述：coeFn_mFourierLp (p : Real>=0∞) [Fact (1 <= p)] (n : d -> Int) : mFourierL
p p n =ᵐ[volume] mFourier n
参数：p : Real>=0∞；1 <= p；n : d -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.coeFn_toLp`：coeFn_toLp (f : C(α, E)) : toLp (E
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `QuotientAddGroup.instSecondCountableTopology`：∀ {G : Type u_1} [inst : T
opologicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G] (N : AddSub
group G)   [SecondCountableTopolog…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureForallVolume`：∀ {ι : Type u_1} 
[inst : Fintype ι] {α : ι → Type u_4} [inst_1 : (i : ι) → MeasureTheory.MeasureS
pace (α i)]   [∀ (i : ι), MeasureTheory.IsF…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
（共 32 条，此处仅展示前 30 条）
-/
theorem coeFn_mFourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : d → ℤ) :
    mFourierLp p n =ᵐ[volume] mFourier n :=
  ContinuousMap.coeFn_toLp volume (mFourier n)

/-- For each `1 ≤ p < ∞`, the linear span of the monomials `mFourier n` is dense in the `Lᵖ` space
of functions on `UnitAddTorus d`. -/
/-
**UnitAddTorus.span_mFourierLp_closure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `UnitAdd
Torus`。
形式化陈述：span_mFourierLp_closure_eq_top {p : Real>=0∞} [Fact (1 <= p)] (hp : p != ∞
) : (span Complex (range (@mFourierLp d _ p _))).topologicalClosure = ⊤
参数：1 <= p；hp : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.topologicalClosure.congr_simp`：∀ {R : Type u} {M : Type v} [in
st : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMonoid M]   [ins
t_3 : _root_.Module R M] [ins…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `DenseRange.topologicalClosure_map_submodule`：∀ {R₁ : Type u_1} {R₂ : Typ
e u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type 
u_4}   [inst_2 : TopologicalSpace…
· 使用定理 `ContinuousMap.instContinuousSMul`：∀ {α : Type u_1} [inst : TopologicalSp
ace α] {R : Type u_3} {M : Type u_5} [inst_1 : TopologicalSpace M]   [inst_2 : T
opologicalSpace R] [in…
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousMap.instContinuousAddOfLocallyCompactSpace`：∀ {α : Type u_1} {
β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Locally
CompactSpace α]   [inst_3 : Add β] [inst_4…
· 使用定理 `QuotientAddGroup.instLocallyCompactSpace`：∀ {G : Type u_1} [inst : Topol
ogicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G] [LocallyCompact
Space G]   (N : AddSubgroup G)…
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
For each `1 ≤ p < ∞`, the linear span of the monomials `mFourier n` is dense in 
the `Lᵖ` space
of functions on `UnitAddTorus d`.
-/
theorem span_mFourierLp_closure_eq_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (span ℂ (range (@mFourierLp d _ p _))).topologicalClosure = ⊤ := by
  simpa only [map_span, ContinuousLinearMap.coe_coe, ← range_comp, Function.comp_def] using
    (ContinuousMap.toLp_denseRange ℂ volume ℂ hp).topologicalClosure_map_submodule
      span_mFourier_closure_eq_top

/-- The monomials `mFourierLp 2 n` are an orthonormal set in `L²`. -/
/-
**UnitAddTorus.orthonormal_mFourier** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus`。
形式化陈述：orthonormal_mFourier : Orthonormal Complex (mFourierLp (d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.ContinuousMap.inner_toLp`：∀ {α : Type u_1} {𝕜 : Type u_2} 
[inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [inst_2 : BorelSpace α]
   [inst_3 : RCLike 𝕜] (μ : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用引理 `UnitAddTorus.mFourier_zero`：mFourier_zero : mFourier (0 : d -> Int) = 1
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `MeasureTheory.Measure.instIsProbabilityMeasureForallVolume`：∀ {ι : Type 
u_1} [inst : Fintype ι] {α : ι → Type u_4} [inst_1 : (i : ι) → MeasureTheory.Mea
sureSpace (α i)]   [∀ (i : ι), MeasureTheory.IsP…
· 使用定理 `instIsProbabilityMeasureUnitAddCircleVolume`：MeasureTheory.IsProbability
Measure MeasureTheory.volume
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `UnitAddTorus.mFourier.eq_1`：∀ {d : Type u_1} [inst : Fintype d] (n : d →
 ℤ),   UnitAddTorus.mFourier n = { toFun := fun x => ∏ i, (fourier (n i)) (x i),
 continuous_toFu…
· 使用定理 `ContinuousMap.coe_mk`：coe_mk (f : X -> Y) (h : Continuous f) : ⇑(⟨f, h⟩ 
: C(X, Y)) = f
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
The monomials `mFourierLp 2 n` are an orthonormal set in `L²`.
-/
theorem orthonormal_mFourier : Orthonormal ℂ (mFourierLp (d := d) 2) := by
  rw [orthonormal_iff_ite]
  intro m n
  simp only [ContinuousMap.inner_toLp, ← mFourier_neg, ← mFourier_add]
  split_ifs with h
  · simpa only [h, add_neg_cancel, mFourier_zero, probReal_univ, one_smul] using!
      integral_const (α := UnitAddTorus d) (μ := volume) (1 : ℂ)
  rw [mFourier, ContinuousMap.coe_mk, MeasureTheory.integral_fintype_prod_volume_eq_prod]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa only [eq_false_intro hi, if_false, ContinuousMap.inner_toLp, ← fourier_neg,
    ← fourier_add] using! (orthonormal_iff_ite.mp <| orthonormal_fourier) (m i) (n i)

end Lp

section fourierCoeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `n`-th Fourier coefficient of a function `UnitAddTorus d → E`, for `E` a complete normed
`ℂ`-vector space, defined as the integral over `UnitAddTorus d` of `mFourier (-n) t • f t`. -/
/-
**UnitAddTorus.mFourierCoeff** 是 Mathlib 中的一个定义，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourierCoeff (f : UnitAddTorus d -> E) (n : d -> Int) : E
参数：f : UnitAddTorus d -> E；n : d -> Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th Fourier coefficient of a function `UnitAddTorus d → E`, for `E` a com
plete normed
`ℂ`-vector space, defined as the integral over `UnitAddTorus d` of `mFourier (-n
) t • f t`.
-/
def mFourierCoeff (f : UnitAddTorus d → E) (n : d → ℤ) : E := ∫ t, mFourier (-n) t • f t

/-- The Fourier coefficients of a function on `UnitAddTorus d` can be computed as integrals
over `∏ i, (aᵢ, aᵢ + 1]`, for any `a : d → ℝ`. -/
/-
**UnitAddTorus.mFourierCoeff_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus
`。
形式化陈述：mFourierCoeff_eq_integral (f : UnitAddTorus d -> E) (n : d -> Int) (a : d 
-> Real) : mFourierCoeff f n = ∫ (x : d -> Real) in {x : d -> Real | forall i, x
 i in Ioc (a i) (a i + 1)}, mFourier (-n) (fun i => x i) • f (fun i => x i)
参数：f : UnitAddTorus d -> E；n : d -> Int；a : d -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnitAddTorus.integral_preimage`：integral_preimage {E : Type*} [NormedAdd
CommGroup E] [NormedSpace Real E] (f : UnitAddTorus d -> E) (a : d -> Real) : ∫ 
x : UnitAddTorus d, …

--- 原说明 ---
The Fourier coefficients of a function on `UnitAddTorus d` can be computed as in
tegrals
over `∏ i, (aᵢ, aᵢ + 1]`, for any `a : d → ℝ`.
-/
theorem mFourierCoeff_eq_integral (f : UnitAddTorus d → E) (n : d → ℤ) (a : d → ℝ) :
    mFourierCoeff f n =
    ∫ (x : d → ℝ) in {x : d → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)},
    mFourier (-n) (fun i => x i) • f (fun i => x i) :=
  integral_preimage (fun x => (mFourier (-n)) x • f x) a

end fourierCoeff

section FourierL2

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-- We define `mFourierBasis` to be a `ℤᵈ`-indexed Hilbert basis for the `L²` space of functions
on `UnitAddTorus d`, which by definition is an isometric isomorphism from `L²(UnitAddTorus d)`
to `ℓ²(ℤᵈ, ℂ)`. -/
/-
**UnitAddTorus.mFourierBasis** 是 Mathlib 中的一个定义，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourierBasis : HilbertBasis (d -> Int) Complex L²(UnitAddTorus d)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `UnitAddTorus.orthonormal_mFourier`：orthonormal_mFourier : Orthonormal Co
mplex (mFourierLp (d

--- 原说明 ---
We define `mFourierBasis` to be a `ℤᵈ`-indexed Hilbert basis for the `L²` space 
of functions
on `UnitAddTorus d`, which by definition is an isometric isomorphism from `L²(Un
itAddTorus d)`
to `ℓ²(ℤᵈ, ℂ)`.
-/
def mFourierBasis : HilbertBasis (d → ℤ) ℂ L²(UnitAddTorus d) :=
  HilbertBasis.mk orthonormal_mFourier (span_mFourierLp_closure_eq_top (by simp)).ge

/-- The elements of the Hilbert basis `mFourierBasis` are the functions `mFourierLp 2`, i.e. the
monomials `mFourier n` on `UnitAddTorus d` considered as elements of `L²`. -/
@[simp]
/-
**UnitAddTorus.coe_mFourierBasis** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus`。
形式化陈述：coe_mFourierBasis : ⇑(mFourierBasis (d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HilbertBasis.coe_mk`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {
E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E]
 [inst_3 …
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `UnitAddTorus.orthonormal_mFourier`：orthonormal_mFourier : Orthonormal Co
mplex (mFourierLp (d

--- 原说明 ---
The elements of the Hilbert basis `mFourierBasis` are the functions `mFourierLp 
2`, i.e. the
monomials `mFourier n` on `UnitAddTorus d` considered as elements of `L²`.
-/
theorem coe_mFourierBasis : ⇑(mFourierBasis (d := d)) = mFourierLp 2 := HilbertBasis.coe_mk _ _

/-- Under the isometric isomorphism `mFourierBasis` from `L²(UnitAddTorus d)` to `ℓ²(ℤᵈ, ℂ)`,
the `i`-th coefficient is `mFourierCoeff f i`. -/
/-
**UnitAddTorus.mFourierBasis_repr** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourierBasis_repr (f : L²(UnitAddTorus d)) (i : d -> Int) : mFourierBasis
.repr f i = mFourierCoeff f i
参数：f : L²(UnitAddTorus d)；i : d -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HilbertBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] (b : Hil…
· 使用定理 `MeasureTheory.L2.inner_def`：inner_def (f g : α ->₂[μ] E) : ⟪f, g⟫ = ∫ a 
: α, ⟪f a, g a⟫ ∂μ
· 使用定理 `UnitAddTorus.coe_mFourierBasis`：coe_mFourierBasis : ⇑(mFourierBasis (d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `UnitAddTorus.coeFn_mFourierLp`：coeFn_mFourierLp (p : Real>=0∞) [Fact (1 
<= p)] (n : d -> Int) : mFourierLp p n =ᵐ[volume] mFourier n
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `UnitAddTorus.mFourier_neg`：mFourier_neg : mFourier (-n) x = conj (mFouri
er n x)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b

--- 原说明 ---
Under the isometric isomorphism `mFourierBasis` from `L²(UnitAddTorus d)` to `ℓ²
(ℤᵈ, ℂ)`,
the `i`-th coefficient is `mFourierCoeff f i`.
-/
theorem mFourierBasis_repr (f : L²(UnitAddTorus d)) (i : d → ℤ) :
    mFourierBasis.repr f i = mFourierCoeff f i := by
  trans ∫ t, conj (mFourierLp 2 i t) * f t
  · rw [mFourierBasis.repr_apply_apply f i, MeasureTheory.L2.inner_def, coe_mFourierBasis]
    simp only [RCLike.inner_apply, mul_comm]
  · apply integral_congr_ae
    filter_upwards [coeFn_mFourierLp 2 i] with _ ht
    rw [ht, ← mFourier_neg, smul_eq_mul]

/-- The Fourier series of an `L2` function `f` sums to `f` in the `L²` norm. -/
/-
**UnitAddTorus.hasSum_mFourier_series_L2** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus
`。
形式化陈述：hasSum_mFourier_series_L2 (f : L²(UnitAddTorus d)) : HasSum (fun i => mFou
rierCoeff f i • mFourierLp 2 i) f
参数：f : L²(UnitAddTorus d)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `UnitAddTorus.mFourierBasis_repr`：mFourierBasis_repr (f : L²(UnitAddTorus
 d)) (i : d -> Int) : mFourierBasis.repr f i = mFourierCoeff f i
· 使用定理 `HilbertBasis.hasSum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace
 𝕜 E] (b : Hil…

--- 原说明 ---
The Fourier series of an `L2` function `f` sums to `f` in the `L²` norm.
-/
theorem hasSum_mFourier_series_L2 (f : L²(UnitAddTorus d)) :
    HasSum (fun i ↦ mFourierCoeff f i • mFourierLp 2 i) f := by
  simpa [← coe_mFourierBasis, mFourierBasis_repr] using mFourierBasis.hasSum_repr f

/-- **Parseval's identity** for inner products: for `L²` functions `f, g` on `UnitAddTorus d`, the
inner product of the Fourier coefficients of `f` and `g` is the inner product of `f` and `g`. -/
/-
**UnitAddTorus.hasSum_prod_mFourierCoeff** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus
`。
形式化陈述：hasSum_prod_mFourierCoeff (f g : L²(UnitAddTorus d)) : HasSum (fun i => co
nj (mFourierCoeff f i) * (mFourierCoeff g i)) (∫ t, conj (f t) * g t)
参数：f g : L²(UnitAddTorus d)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `HilbertBasis.hasSum_inner_mul_inner`：∀ {ι : Type u_1} {𝕜 : Type u_2} [in
st : RCLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerP
roductSpace 𝕜 E] (b : Hil…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HilbertBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] (b : Hil…
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Parseval's identity** for inner products: for `L²` functions `f, g` on `UnitAd
dTorus d`, the
inner product of the Fourier coefficients of `f` and `g` is the inner product of
 `f` and `g`.
-/
theorem hasSum_prod_mFourierCoeff (f g : L²(UnitAddTorus d)) :
    HasSum (fun i ↦ conj (mFourierCoeff f i) * (mFourierCoeff g i)) (∫ t, conj (f t) * g t) := by
  simp_rw [mul_comm (conj _)]
  refine HasSum.congr_fun (mFourierBasis.hasSum_inner_mul_inner f g) (fun n ↦ ?_)
  simp only [← mFourierBasis_repr, HilbertBasis.repr_apply_apply, inner_conj_symm,
    mul_comm (inner ℂ f _)]

/-- **Parseval's identity** for norms: for an `L²` function `f` on `UnitAddTorus d`, the sum of the
squared norms of the Fourier coefficients equals the `L²` norm of `f`. -/
/-
**UnitAddTorus.hasSum_sq_mFourierCoeff** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus`。
形式化陈述：hasSum_sq_mFourierCoeff (f : L²(UnitAddTorus d)) : HasSum (fun i => ‖mFour
ierCoeff f i‖ ^ 2) (∫ t, ‖f t‖ ^ 2)
参数：f : L²(UnitAddTorus d)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inner_self_eq_norm_sq`：inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^
 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `integral_re`：integral_re {f : X -> 𝕜} (hf : Integrable f μ) : ∫ x, RCLik
e.re (f x) ∂μ = RCLike.re (∫ x, f x ∂μ)
· 使用定理 `MeasureTheory.L2.integrable_inner`：integrable_inner (f g : α ->₂[μ] E) :
 Integrable (fun x : α => ⟪f x, g x⟫) μ
· 使用定理 `RCLike.hasSum_re`：∀ {α : Type u_1} (𝕜 : Type u_2) [inst : RCLike 𝕜] {L :
 SummationFilter α} {f : α → 𝕜} {x : 𝕜},   HasSum f x L → HasSum (fun x => RCLik
e.re (…
· 使用定理 `UnitAddTorus.hasSum_prod_mFourierCoeff`：hasSum_prod_mFourierCoeff (f g :
 L²(UnitAddTorus d)) : HasSum (fun i => conj (mFourierCoeff f i) * (mFourierCoef
f g i)) (∫ t, conj (f t) * g…

--- 原说明 ---
**Parseval's identity** for norms: for an `L²` function `f` on `UnitAddTorus d`,
 the sum of the
squared norms of the Fourier coefficients equals the `L²` norm of `f`.
-/
theorem hasSum_sq_mFourierCoeff (f : L²(UnitAddTorus d)) :
    HasSum (fun i ↦ ‖mFourierCoeff f i‖ ^ 2) (∫ t, ‖f t‖ ^ 2) := by
  simpa only [← RCLike.inner_apply', inner_self_eq_norm_sq, ← integral_re
    (L2.integrable_inner f f)] using RCLike.hasSum_re ℂ (hasSum_prod_mFourierCoeff f f)

end FourierL2

section Convergence

variable (f : C(UnitAddTorus d, ℂ))

/-
**UnitAddTorus.mFourierCoeff_toLp** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddTorus`。
形式化陈述：mFourierCoeff_toLp (n : d -> Int) : mFourierCoeff (f.toLp 2 volume Complex
) n = mFourierCoeff f n
参数：n : d -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `QuotientAddGroup.instSecondCountableTopology`：∀ {G : Type u_1} [inst : T
opologicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G] (N : AddSub
group G)   [SecondCountableTopolog…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
（共 44 条，此处仅展示前 30 条）
-/
theorem mFourierCoeff_toLp (n : d → ℤ) :
    mFourierCoeff (f.toLp 2 volume ℂ) n = mFourierCoeff f n :=
  integral_congr_ae (ae_eq_rfl.mul <| f.coeFn_toAEEqFun _)

variable {f}

/-- If the sequence of Fourier coefficients of `f` is summable, then the Fourier series converges
uniformly to `f`. -/
/-
**UnitAddTorus.hasSum_mFourier_series_of_summable** 是 Mathlib 中的一个定理，位于命名空间 `Uni
tAddTorus`。
形式化陈述：hasSum_mFourier_series_of_summable (h : Summable (mFourierCoeff f)) : HasS
um (fun i => mFourierCoeff f i • mFourier i) f
参数：h : Summable (mFourierCoeff f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `QuotientAddGroup.instSecondCountableTopology`：∀ {G : Type u_1} [inst : T
opologicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G] (N : AddSub
group G)   [SecondCountableTopolog…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
If the sequence of Fourier coefficients of `f` is summable, then the Fourier ser
ies converges
uniformly to `f`.
-/
theorem hasSum_mFourier_series_of_summable (h : Summable (mFourierCoeff f)) :
    HasSum (fun i ↦ mFourierCoeff f i • mFourier i) f := by
  have sum_L2 := hasSum_mFourier_series_L2 (ContinuousMap.toLp 2 volume ℂ f)
  simp only [mFourierCoeff_toLp] at sum_L2
  refine ContinuousMap.hasSum_of_hasSum_Lp (.of_norm ?_) sum_L2
  simpa only [norm_smul, mFourier_norm, mul_one] using h.norm

/-- If the sequence of Fourier coefficients of `f` is summable, then the Fourier series of `f`
converges everywhere pointwise to `f`. -/
/-
**UnitAddTorus.hasSum_mFourier_series_apply_of_summable** 是 Mathlib 中的一个定理，位于命名空
间 `UnitAddTorus`。
形式化陈述：hasSum_mFourier_series_apply_of_summable (h : Summable (mFourierCoeff f)) 
(x : UnitAddTorus d) : HasSum (fun i => mFourierCoeff f i • mFourier i x) (f x)
参数：h : Summable (mFourierCoeff f)；x : UnitAddTorus d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u
_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂]
 [inst_2 : AddCo…
· 使用定理 `UnitAddTorus.hasSum_mFourier_series_of_summable`：hasSum_mFourier_series_
of_summable (h : Summable (mFourierCoeff f)) : HasSum (fun i => mFourierCoeff f 
i • mFourier i) f

--- 原说明 ---
If the sequence of Fourier coefficients of `f` is summable, then the Fourier ser
ies of `f`
converges everywhere pointwise to `f`.
-/
theorem hasSum_mFourier_series_apply_of_summable (h : Summable (mFourierCoeff f))
    (x : UnitAddTorus d) : HasSum (fun i ↦ mFourierCoeff f i • mFourier i x) (f x) := by
  simpa only [map_smul] using! (ContinuousMap.evalCLM ℂ x).hasSum
    (hasSum_mFourier_series_of_summable h)

end Convergence

end UnitAddTorus

