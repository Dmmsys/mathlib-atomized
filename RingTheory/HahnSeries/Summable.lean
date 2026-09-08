/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Ring.Action.Rat
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Summable families of Hahn Series

We introduce a notion of formal summability for families of Hahn series, and define a formal sum
function. This theory is applied to characterize invertible Hahn series whose coefficients are in a
commutative domain.

## Main Definitions
* `HahnSeries.SummableFamily` is a family of Hahn series such that the union of the supports
  is partially well-ordered and only finitely many are nonzero at any given coefficient. Note that
  this is different from `Summable` in the valuation topology, because there are topologically
  summable families that do not satisfy the axioms of `HahnSeries.SummableFamily`, and formally
  summable families whose sums do not converge topologically.
* `HahnSeries.SummableFamily.hsum` is the formal sum of a summable family.
* `HahnSeries.SummableFamily.lsum` is the formal sum bundled as a `LinearMap`.
* `HahnSeries.SummableFamily.smul` is the summable family given by pointwise scalar multiplication
  of component Hahn series.
* `HahnSeries.SummableFamily.mul` is the summable family given by pointwise multiplication.
* `HahnSeries.SummableFamily.powers` is the summable family given by non-negative powers of a
  Hahn series, if the series has strictly positive order. If the series has non-positive order, then
  the summable family takes the junk value of zero.

## Main results
* `HahnSeries.isUnit_iff`: If `R` is a commutative domain, and `Γ` is a linearly ordered additive
  commutative group, then a Hahn series is a unit if and only if its leading term is a unit in `R`.
* `HahnSeries.SummableFamily.hsum_smul`:   `smul` is compatible with `hsum`.
* `HahnSeries.SummableFamily.hsum_mul`: `mul` is compatible with `hsum`.  That is, the product of
  sums is equal to the sum of pointwise products.

## TODO
* Summable Pi families

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section


open Finset Function

open scoped Pointwise

noncomputable section

variable {Γ Γ' R V α β : Type*}

namespace HahnSeries

section

/-- A family of Hahn series whose formal coefficient-wise sum is a Hahn series.  For each
coefficient of the sum to be well-defined, we require that only finitely many series are nonzero at
any given coefficient.  For the formal sum to be a Hahn series, we require that the union of the
supports of the constituent series is partially well-ordered. -/
/-
**HahnSeries.SummableFamily** 是 Mathlib 中的一个归纳类型，位于命名空间 `HahnSeries`。
形式化陈述：(Γ : Type u_8) → (R : Type u_9) → [PartialOrder Γ] → [AddCommMonoid R] → T
ype u_7 → Type (max (max u_7 u_8) u_9)
参数：max u_7 u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of Hahn series whose formal coefficient-wise sum is a Hahn series.  For
 each
coefficient of the sum to be well-defined, we require that only finitely many se
ries are nonzero at
any given coefficient.  For the formal sum to be a Hahn series, we require that 
the union of the
supports of the constituent series is partially well-ordered.
-/
structure SummableFamily (Γ R) [PartialOrder Γ] [AddCommMonoid R] (α : Type*) where
  /-- A parametrized family of Hahn series. -/
  toFun : α → R⟦Γ⟧
  isPWO_iUnion_support' : Set.IsPWO (⋃ a : α, (toFun a).support)
  finite_co_support' : ∀ g : Γ, { a | (toFun a).coeff g ≠ 0 }.Finite

end

namespace SummableFamily

section AddCommMonoid

variable [PartialOrder Γ] [AddCommMonoid R]

/-
**HahnSeries.SummableFamily.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries.SummableFamil
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (SummableFamily Γ R α) α R⟦Γ⟧ where
  coe := toFun
  coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

@[simp]
/-
**HahnSeries.SummableFamily.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summabl
eFamily`。
形式化陈述：coe_mk (toFun : α -> R⟦Γ⟧) (h1 h2) : (⟨toFun, h1, h2⟩ : SummableFamily Γ R
 α) = toFun
参数：toFun : α -> R⟦Γ⟧；h1 h2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (toFun : α → R⟦Γ⟧) (h1 h2) :
    (⟨toFun, h1, h2⟩ : SummableFamily Γ R α) = toFun :=
  rfl
/-
**HahnSeries.SummableFamily.isPWO_iUnion_support** 是 Mathlib 中的一个定理，位于命名空间 `Hahn
Series.SummableFamily`。
形式化陈述：isPWO_iUnion_support (s : SummableFamily Γ R α) : Set.IsPWO (⋃ a : α, (s a
).support)
参数：s : SummableFamily Γ R α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.isPWO_iUnion_support'`：∀ {Γ : Type u_8} {R : T
ype u_9} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {α : Type u_7}   (se
lf : HahnSeries.SummableFamily Γ R α)…
-/
theorem isPWO_iUnion_support (s : SummableFamily Γ R α) : Set.IsPWO (⋃ a : α, (s a).support) :=
  s.isPWO_iUnion_support'
/-
**HahnSeries.SummableFamily.finite_co_support** 是 Mathlib 中的一个定理，位于命名空间 `HahnSer
ies.SummableFamily`。
形式化陈述：finite_co_support (s : SummableFamily Γ R α) (g : Γ) : (fun a => (s a).coe
ff g).HasFiniteSupport
参数：s : SummableFamily Γ R α；g : Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.finite_co_support'`：∀ {Γ : Type u_8} {R : Type
 u_9} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {α : Type u_7}   (self 
: HahnSeries.SummableFamily Γ R α)…
-/
theorem finite_co_support (s : SummableFamily Γ R α) (g : Γ) :
    (fun a => (s a).coeff g).HasFiniteSupport :=
  s.finite_co_support' g
/-
**HahnSeries.SummableFamily.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.
SummableFamily`。
形式化陈述：coe_injective : @Function.Injective (SummableFamily Γ R α) (α -> R⟦Γ⟧) (⇑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : @Function.Injective (SummableFamily Γ R α) (α → R⟦Γ⟧) (⇑) :=
  DFunLike.coe_injective

@[ext]
/-
**HahnSeries.SummableFamily.ext** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.SummableFa
mily`。
形式化陈述：ext {s t : SummableFamily Γ R α} (h : forall a : α, s a = t a) : s = t
参数：h : forall a : α, s a = t a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {s t : SummableFamily Γ R α} (h : ∀ a : α, s a = t a) : s = t :=
  DFunLike.ext s t h
/-
**HahnSeries.SummableFamily.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries.SummableFamil
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (SummableFamily Γ R α) :=
  ⟨fun x y =>
    { toFun := x + y
      isPWO_iUnion_support' :=
        (x.isPWO_iUnion_support.union y.isPWO_iUnion_support).mono
          (by
            rw [← Set.iUnion_union_distrib]
            exact Set.iUnion_mono fun a => support_add_subset ..)
      finite_co_support' := fun g =>
        ((x.finite_co_support g).union (y.finite_co_support g)).subset
          (by
            intro a ha
            change (x a).coeff g + (y a).coeff g ≠ 0 at ha
            rw [Set.mem_union, Function.mem_support, Function.mem_support]
            contrapose! ha
            rw [ha.1, ha.2, add_zero]) }⟩
/-
**HahnSeries.SummableFamily.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries.SummableFamil
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (SummableFamily Γ R α) :=
  ⟨⟨0, by simp, by simp⟩⟩
/-
**HahnSeries.SummableFamily.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries.SummableFamil
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SummableFamily Γ R α) :=
  ⟨0⟩

@[simp]
/-
**HahnSeries.SummableFamily.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summab
leFamily`。
形式化陈述：coe_add (s t : SummableFamily Γ R α) : ⇑(s + t) = s + t
参数：s t : SummableFamily Γ R α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (s t : SummableFamily Γ R α) : ⇑(s + t) = s + t :=
  rfl
/-
**HahnSeries.SummableFamily.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summ
ableFamily`。
形式化陈述：add_apply {s t : SummableFamily Γ R α} {a : α} : (s + t) a = s a + t a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply {s t : SummableFamily Γ R α} {a : α} : (s + t) a = s a + t a :=
  rfl

@[simp]
/-
**HahnSeries.SummableFamily.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summa
bleFamily`。
形式化陈述：coe_zero : ((0 : SummableFamily Γ R α) : α -> R⟦Γ⟧) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : SummableFamily Γ R α) : α → R⟦Γ⟧) = 0 :=
  rfl
/-
**HahnSeries.SummableFamily.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Sum
mableFamily`。
形式化陈述：zero_apply {a : α} : (0 : SummableFamily Γ R α) a = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply {a : α} : (0 : SummableFamily Γ R α) a = 0 :=
  rfl


section SMul

variable {M} [SMulZeroClass M R]

/-
**HahnSeries.SummableFamily.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries.SummableFamil
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul M (SummableFamily Γ R β) :=
  ⟨fun r t =>
    { toFun := r • t
      isPWO_iUnion_support' := t.isPWO_iUnion_support.mono (Set.iUnion_mono fun i =>
        Pi.smul_apply r t i ▸ Function.support_const_smul_subset r _)
      finite_co_support' := by
        intro g
        refine (t.finite_co_support g).subset ?_
        intro i hi
        simp only [Pi.smul_apply, coeff_smul, ne_eq, Set.mem_ofPred_eq] at hi
        simp only [Function.mem_support, ne_eq]
        exact right_ne_zero_of_smul hi } ⟩

@[simp]
/-
**HahnSeries.SummableFamily.coe_smul'** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summ
ableFamily`。
形式化陈述：coe_smul' (m : M) (s : SummableFamily Γ R α) : ⇑(m • s) = m • s
参数：m : M；s : SummableFamily Γ R α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul' (m : M) (s : SummableFamily Γ R α) : ⇑(m • s) = m • s :=
  rfl
/-
**HahnSeries.SummableFamily.smul_apply'** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Su
mmableFamily`。
形式化陈述：smul_apply' (m : M) (s : SummableFamily Γ R α) (a : α) : (m • s) a = m • s
 a
参数：m : M；s : SummableFamily Γ R α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply' (m : M) (s : SummableFamily Γ R α) (a : α) : (m • s) a = m • s a :=
  rfl

end SMul

/-
**HahnSeries.SummableFamily.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries.SummableFamil
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (SummableFamily Γ R α) := fast_instance%
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add (fun _ _ => coe_smul' _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient function of a summable family, as a finsupp on the parameter type. -/
@[simps]
/-
**HahnSeries.SummableFamily.coeff** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.Summable
Family`。
形式化陈述：coeff (s : SummableFamily Γ R α) (g : Γ) : α ->₀ R where support
参数：s : SummableFamily Γ R α；g : Γ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.finite_co_support`：finite_co_support (s : Summ
ableFamily Γ R α) (g : Γ) : (fun a => (s a).coeff g).HasFiniteSupport

--- 原说明 ---
The coefficient function of a summable family, as a finsupp on the parameter typ
e.
-/
def coeff (s : SummableFamily Γ R α) (g : Γ) : α →₀ R where
  support := (s.finite_co_support g).toFinset
  toFun a := (s a).coeff g
  mem_support_toFun a := by simp

@[simp]
/-
**HahnSeries.SummableFamily.coeff_def** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summ
ableFamily`。
形式化陈述：coeff_def (s : SummableFamily Γ R α) (a : α) (g : Γ) : s.coeff g a = (s a)
.coeff g
参数：s : SummableFamily Γ R α；a : α；g : Γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_def (s : SummableFamily Γ R α) (a : α) (g : Γ) : s.coeff g a = (s a).coeff g :=
  rfl

/-- The infinite sum of a `SummableFamily` of Hahn series. -/
/-
**HahnSeries.SummableFamily.hsum** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.SummableF
amily`。
形式化陈述：hsum (s : SummableFamily Γ R α) : R⟦Γ⟧ where coeff g
参数：s : SummableFamily Γ R α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infinite sum of a `SummableFamily` of Hahn series.
-/
def hsum (s : SummableFamily Γ R α) : R⟦Γ⟧ where
  coeff g := ∑ᶠ i, (s i).coeff g
  isPWO_support' :=
    s.isPWO_iUnion_support.mono fun g => by
      contrapose
      rw [Set.mem_iUnion, not_exists, Function.mem_support, Classical.not_not]
      simp_rw [mem_support, Classical.not_not]
      intro h
      rw [finsum_congr h, finsum_zero]

@[simp]
/-
**HahnSeries.SummableFamily.coeff_hsum** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Sum
mableFamily`。
形式化陈述：coeff_hsum {s : SummableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s 
i).coeff g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_hsum {s : SummableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g :=
  rfl

@[simp]
/-
**HahnSeries.SummableFamily.hsum_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summ
ableFamily`。
形式化陈述：hsum_zero : (0 : SummableFamily Γ R α).hsum = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_zero`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M], ∑
ᶠ (x : α), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hsum_zero : (0 : SummableFamily Γ R α).hsum = 0 := by
  ext
  simp
/-
**HahnSeries.SummableFamily.support_hsum_subset** 是 Mathlib 中的一个定理，位于命名空间 `HahnS
eries.SummableFamily`。
形式化陈述：support_hsum_subset {s : SummableFamily Γ R α} : s.hsum.support subseteq ⋃
 a : α, (s a).support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.finite_co_support`：finite_co_support (s : Summ
ableFamily Γ R α) (g : Γ) : (fun a => (s a).coeff g).HasFiniteSupport
· 使用定理 `Finset.exists_ne_zero_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, ∑ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f
 a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `HahnSeries.SummableFamily.coeff_hsum`：coeff_hsum {s : SummableFamily Γ R
 α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g
· 使用定理 `HahnSeries.mem_support`：mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support 
↔ x.coeff a != 0
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem support_hsum_subset {s : SummableFamily Γ R α} : s.hsum.support ⊆ ⋃ a : α, (s a).support :=
  fun g hg => by
  rw [mem_support, coeff_hsum, finsum_eq_sum _ (s.finite_co_support _)] at hg
  obtain ⟨a, _, h2⟩ := exists_ne_zero_of_sum_ne_zero hg
  rw [Set.mem_iUnion]
  exact ⟨a, h2⟩

@[simp]
/-
**HahnSeries.SummableFamily.hsum_add** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summa
bleFamily`。
形式化陈述：hsum_add {s t : SummableFamily Γ R α} : (s + t).hsum = s.hsum + t.hsum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finsum_add_distrib`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoi
d M] {f g : α → M},   Function.HasFiniteSupport f →     Function.HasFiniteSuppor
t g → ∑ᶠ…
· 使用定理 `HahnSeries.SummableFamily.finite_co_support`：finite_co_support (s : Summ
ableFamily Γ R α) (g : Γ) : (fun a => (s a).coeff g).HasFiniteSupport
-/
theorem hsum_add {s t : SummableFamily Γ R α} : (s + t).hsum = s.hsum + t.hsum := by
  ext g
  simp only [coeff_hsum, coeff_add, add_apply]
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)

set_option backward.isDefEq.respectTransparency false in
/-
**HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset** 是 Mathlib 中的一个定理，位于命名空
间 `HahnSeries.SummableFamily`。
形式化陈述：coeff_hsum_eq_sum_of_subset {s : SummableFamily Γ R α} {g : Γ} {t : Finset
 α} (h : { a | (s a).coeff g != 0 } subseteq t) : s.hsum.coeff g = ∑ i in t, (s 
i).coeff g
参数：h : { a | (s a).coeff g != 0 } subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.finite_co_support`：finite_co_support (s : Summ
ableFamily Γ R α) (g : Γ) : (fun a => (s a).coeff g).HasFiniteSupport
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.toFinset_subset`：toFinset_subset {t : Finset α} : hs.toFinset
 subseteq t ↔ s subseteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coeff_hsum_eq_sum_of_subset {s : SummableFamily Γ R α} {g : Γ} {t : Finset α}
    (h : { a | (s a).coeff g ≠ 0 } ⊆ t) : s.hsum.coeff g = ∑ i ∈ t, (s i).coeff g := by
  simp only [coeff_hsum, finsum_eq_sum _ (s.finite_co_support _)]
  exact sum_subset (Set.Finite.toFinset_subset.mpr h) (by simp)
/-
**HahnSeries.SummableFamily.coeff_hsum_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `HahnSer
ies.SummableFamily`。
形式化陈述：coeff_hsum_eq_sum {s : SummableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ 
i in (s.coeff g).support, (s i).coeff g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.SummableFamily.finite_co_support`：finite_co_support (s : Summ
ableFamily Γ R α) (g : Γ) : (fun a => (s a).coeff g).HasFiniteSupport
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `HahnSeries.SummableFamily.coeff_support`：∀ {Γ : Type u_1} {R : Type u_3}
 {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R]   (s : HahnSe
ries.SummableFamily Γ R α) (g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_hsum_eq_sum {s : SummableFamily Γ R α} {g : Γ} :
    s.hsum.coeff g = ∑ i ∈ (s.coeff g).support, (s i).coeff g := by
  simp only [coeff_hsum, finsum_eq_sum _ (s.finite_co_support _), coeff_support]

/-- The summable family made of a single Hahn series. -/
@[simps]
/-
**HahnSeries.SummableFamily.single** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.Summabl
eFamily`。
形式化陈述：single {ι} [DecidableEq ι] (i : ι) (x : R⟦Γ⟧) : SummableFamily Γ R ι where
 toFun
参数：i : ι；x : R⟦Γ⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The summable family made of a single Hahn series.
-/
def single {ι} [DecidableEq ι] (i : ι) (x : R⟦Γ⟧) : SummableFamily Γ R ι where
  toFun := Pi.single i x
  isPWO_iUnion_support' := by
    have : (Pi.single (M := fun _ ↦ R⟦Γ⟧) i x i).support.IsPWO := by simp
    refine this.mono <| Set.iUnion_subset fun a => ?_
    obtain rfl | ha := eq_or_ne a i
    · rfl
    · simp [ha]
  finite_co_support' g := (Set.finite_singleton i).subset fun j => by
    obtain rfl | ha := eq_or_ne j i <;> simp [*]

@[simp]
/-
**HahnSeries.SummableFamily.hsum_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Su
mmableFamily`。
形式化陈述：hsum_single {ι} [DecidableEq ι] (i : ι) (x : R⟦Γ⟧) : (single i x).hsum = x
参数：i : ι；x : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.coeff_hsum`：coeff_hsum {s : SummableFamily Γ R
 α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.SummableFamily.single_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {ι : Type u_7}   [inst_2 : De
cidableEq ι] (i : ι) (x : Ha…
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
theorem hsum_single {ι} [DecidableEq ι] (i : ι) (x : R⟦Γ⟧) : (single i x).hsum = x := by
  ext g
  rw [coeff_hsum, finsum_eq_single _ i, single_toFun, Pi.single_eq_same]
  simp +contextual

/-- The summable family made of a constant Hahn series. -/
@[simps]
/-
**HahnSeries.SummableFamily.const** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.Summable
Family`。
形式化陈述：const (ι) [Finite ι] (x : R⟦Γ⟧) : SummableFamily Γ R ι where toFun _
参数：ι；x : R⟦Γ⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The summable family made of a constant Hahn series.
-/
def const (ι) [Finite ι] (x : R⟦Γ⟧) : SummableFamily Γ R ι where
  toFun _ := x
  isPWO_iUnion_support' := by
    cases isEmpty_or_nonempty ι
    · simp
    · exact Eq.mpr (congrArg (fun s ↦ s.IsPWO) (Set.iUnion_const x.support)) x.isPWO_support
  finite_co_support' g := Set.toFinite {a | ((fun _ ↦ x) a).coeff g ≠ 0}

@[simp]
/-
**HahnSeries.SummableFamily.hsum_unique** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Su
mmableFamily`。
形式化陈述：hsum_unique {ι} [Unique ι] (x : SummableFamily Γ R ι) : x.hsum = x default
参数：x : SummableFamily Γ R ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_unique`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M] 
[inst_1 : Unique α] (f : α → M), ∑ᶠ (i : α), f i = f default
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hsum_unique {ι} [Unique ι] (x : SummableFamily Γ R ι) : x.hsum = x default := by
  ext g
  simp only [coeff_hsum, finsum_unique]

/-- A summable family induced by an equivalence of the parametrizing type. -/
@[simps]
/-
**HahnSeries.SummableFamily.Equiv** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.Summable
Family`。
形式化陈述：Equiv (e : α ≃ β) (s : SummableFamily Γ R α) : SummableFamily Γ R β where 
toFun b
参数：e : α ≃ β；s : SummableFamily Γ R α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A summable family induced by an equivalence of the parametrizing type.
-/
def Equiv (e : α ≃ β) (s : SummableFamily Γ R α) : SummableFamily Γ R β where
  toFun b := s (e.symm b)
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono s.isPWO_iUnion_support fun g => ?_
    simp only [Set.mem_iUnion, mem_support, ne_eq, forall_exists_index]
    exact fun b hg => Exists.intro (e.symm b) hg
  finite_co_support' g :=
    (Equiv.set_finite_iff e.subtypeEquivOfSubtype').mp <| s.finite_co_support' g

@[simp]
/-
**HahnSeries.SummableFamily.hsum_equiv** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Sum
mableFamily`。
形式化陈述：hsum_equiv (e : α ≃ β) (s : SummableFamily Γ R α) : (Equiv e s).hsum = s.h
sum
参数：e : α ≃ β；s : SummableFamily Γ R α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.Equiv_toFun`：∀ {Γ : Type u_1} {R : Type u_3} {
α : Type u_5} {β : Type u_6} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] 
  (e : α ≃ β) (s : HahnSeri…
· 使用定理 `finsum_eq_of_bijective`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [
inst : AddCommMonoid M] {f : α → M} {g : β → M} (e : α → β),   Function.Bijectiv
e e → (∀ (x …
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem hsum_equiv (e : α ≃ β) (s : SummableFamily Γ R α) : (Equiv e s).hsum = s.hsum := by
  ext g
  simp only [coeff_hsum, Equiv_toFun]
  exact finsum_eq_of_bijective e.symm (Equiv.bijective e.symm) fun x => rfl

/-- The summable family given by multiplying every series in a summable family by a scalar. -/
@[simps]
/-
**HahnSeries.SummableFamily.smulFamily** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.Sum
mableFamily`。
形式化陈述：smulFamily [AddCommMonoid V] [SMulWithZero R V] (f : α -> R) (s : Summable
Family Γ V α) : SummableFamily Γ V α where toFun a
参数：f : α -> R；s : SummableFamily Γ V α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The summable family given by multiplying every series in a summable family by a 
scalar.
-/
def smulFamily [AddCommMonoid V] [SMulWithZero R V] (f : α → R) (s : SummableFamily Γ V α) :
    SummableFamily Γ V α where
  toFun a := (f a) • s a
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono s.isPWO_iUnion_support fun g hg => ?_
    simp_all only [Set.mem_iUnion, mem_support, coeff_smul, ne_eq]
    obtain ⟨i, hi⟩ := hg
    exact Exists.intro i <| right_ne_zero_of_smul hi
  finite_co_support' g := by
    refine Set.Finite.subset (s.finite_co_support g) fun i hi => ?_
    simp_all only [coeff_smul, ne_eq, Set.mem_ofPred_eq, Function.mem_support]
    exact right_ne_zero_of_smul hi
/-
**HahnSeries.SummableFamily.hsum_smulFamily** 是 Mathlib 中的一个定理，位于命名空间 `HahnSerie
s.SummableFamily`。
形式化陈述：hsum_smulFamily [AddCommMonoid V] [SMulWithZero R V] (f : α -> R) (s : Sum
mableFamily Γ V α) (g : Γ) : (smulFamily f s).hsum.coeff g = ∑ᶠ i, (f i) • ((s i
).coeff g)
参数：f : α -> R；s : SummableFamily Γ V α；g : Γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hsum_smulFamily [AddCommMonoid V] [SMulWithZero R V] (f : α → R)
    (s : SummableFamily Γ V α) (g : Γ) :
    (smulFamily f s).hsum.coeff g = ∑ᶠ i, (f i) • ((s i).coeff g) :=
  rfl
/-
**HahnSeries.SummableFamily.le_hsum_support_mem** 是 Mathlib 中的一个定理，位于命名空间 `HahnS
eries.SummableFamily`。
形式化陈述：le_hsum_support_mem {s : SummableFamily Γ R α} {g g' : Γ} (hg : forall b :
 α, forall g' in (s b).support, g <= g') (hg' : g' in s.hsum.support) : g <= g'
参数：hg : forall b : α, forall g' in (s b).support, g <= g'；hg' : g' in s.hsum.sup
port。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_ne_zero_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, ∑ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f
 a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.coeff_hsum_eq_sum`：coeff_hsum_eq_sum {s : Summ
ableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ i in (s.coeff g).support, (s i).c
oeff g
· 使用定理 `HahnSeries.mem_support`：mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support 
↔ x.coeff a != 0
-/
theorem le_hsum_support_mem {s : SummableFamily Γ R α} {g g' : Γ}
    (hg : ∀ b : α, ∀ g' ∈ (s b).support, g ≤ g') (hg' : g' ∈ s.hsum.support) : g ≤ g' := by
  rw [mem_support, coeff_hsum_eq_sum] at hg'
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg'
  exact hg i g' hi
/-
**HahnSeries.SummableFamily.hsum_orderTop_of_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnS
eries.SummableFamily`。
形式化陈述：hsum_orderTop_of_le {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (
s a).orderTop) (hg : forall b : α, forall g' in (s b).support, g <= g') (hna : f
orall b : α, b != a -> (s b).coeff g = 0) : s.hsum.orderTop = g
参数：ha : g = (s a).orderTop；hg : forall b : α, forall g' in (s b).support, g <= g
'；hna : forall b : α, b != a -> (s b).coeff g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.orderTop_eq_of_le`：orderTop_eq_of_le {x : R⟦Γ⟧} {g : Γ} (hg :
 g in x.support) (hx : forall g' in x.support, g <= g') : orderTop x = g
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.coeff_hsum`：coeff_hsum {s : SummableFamily Γ R
 α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `HahnSeries.coeff_orderTop_ne`：coeff_orderTop_ne {x : R⟦Γ⟧} {g : Γ} (hg :
 x.orderTop = g) : x.coeff g != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.SummableFamily.le_hsum_support_mem`：le_hsum_support_mem {s : 
SummableFamily Γ R α} {g g' : Γ} (hg : forall b : α, forall g' in (s b).support,
 g <= g') (hg' : g' in s.hsum.suppo…
-/
theorem hsum_orderTop_of_le {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop)
    (hg : ∀ b : α, ∀ g' ∈ (s b).support, g ≤ g') (hna : ∀ b : α, b ≠ a → (s b).coeff g = 0) :
    s.hsum.orderTop = g :=
  orderTop_eq_of_le (ne_of_eq_of_ne (by rw [coeff_hsum, finsum_eq_single (fun i ↦ (s i).coeff g) a
    hna]) (coeff_orderTop_ne ha.symm)) fun _ hg' => le_hsum_support_mem hg hg'
/-
**HahnSeries.SummableFamily.hsum_leadingCoeff_of_le** 是 Mathlib 中的一个定理，位于命名空间 `H
ahnSeries.SummableFamily`。
形式化陈述：hsum_leadingCoeff_of_le {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g
 = (s a).orderTop) (hg : forall b : α, forall g' in (s b).support, g <= g') (hna
 : forall b : α, b != a -> (s b).coeff g = 0) : s.hsum.leadingCoeff = (s a).coef
f g
参数：ha : g = (s a).orderTop；hg : forall b : α, forall g' in (s b).support, g <= g
'；hna : forall b : α, b != a -> (s b).coeff g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.hsum_orderTop_of_le`：hsum_orderTop_of_le {s : 
SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop) (hg : forall b :
 α, forall g' in (s b).support, g <…
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.orderTop.eq_1`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Partia
lOrder Γ] [inst_1 : Zero R] (x : HahnSeries Γ R),   x.orderTop = if h : x = 0 th
en ⊤ else ↑(⋯.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `HahnSeries.orderTop_ne_top`：orderTop_ne_top : orderTop x != ⊤ ↔ x != 0
· 使用定理 `HahnSeries.leadingCoeff_of_ne_zero`：leadingCoeff_of_ne_zero {x : R⟦Γ⟧} (
hx : x != 0) : x.leadingCoeff = x.coeff (x.orderTop.untop <| orderTop_ne_top.2 h
x)
· 使用定理 `HahnSeries.support_nonempty_iff`：∀ {Γ : Type u_1} {R : Type u_3} [inst :
 PartialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R},   x.support.Nonempty ↔ 
x ≠ 0
· 使用定理 `HahnSeries.untop_orderTop_of_ne_zero`：untop_orderTop_of_ne_zero {x : R⟦Γ
⟧} (hx : x != 0) : WithTop.untop x.orderTop (orderTop_ne_top.2 hx) = x.isWF_supp
ort.min (support_nonempty_…
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
-/
theorem hsum_leadingCoeff_of_le {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop)
    (hg : ∀ b : α, ∀ g' ∈ (s b).support, g ≤ g') (hna : ∀ b : α, b ≠ a → (s b).coeff g = 0) :
    s.hsum.leadingCoeff = (s a).coeff g := by
  have := hsum_orderTop_of_le ha hg hna
  rw [orderTop] at this
  have hs : s.hsum ≠ 0 := by
    by_contra h
    simp [h] at this
  simp only [hs, ↓reduceDIte, WithTop.coe_eq_coe] at this
  simp only [leadingCoeff_of_ne_zero hs, coeff_hsum, untop_orderTop_of_ne_zero hs, this]
  rw [finsum_eq_single (fun i ↦ (s i).coeff g) a hna]

end AddCommMonoid

section AddCommGroup

variable [PartialOrder Γ] [AddCommGroup R] {s t : SummableFamily Γ R α} {a : α}

/-
**HahnSeries.SummableFamily.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries.SummableFamil
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (SummableFamily Γ R α) where
  neg s :=
    { toFun := fun a => -s a
      isPWO_iUnion_support' := by
        simp_rw [support_neg]
        exact s.isPWO_iUnion_support
      finite_co_support' := fun g => by
        simp only [coeff_neg', Pi.neg_apply, Ne, neg_eq_zero]
        exact s.finite_co_support g }

@[simp]
/-
**HahnSeries.SummableFamily.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summab
leFamily`。
形式化陈述：coe_neg (s : SummableFamily Γ R α) : ⇑(-s) = -s
参数：s : SummableFamily Γ R α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (s : SummableFamily Γ R α) : ⇑(-s) = -s :=
  rfl
/-
**HahnSeries.SummableFamily.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summ
ableFamily`。
形式化陈述：neg_apply : (-s) a = -s a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply : (-s) a = -s a :=
  rfl
/-
**HahnSeries.SummableFamily.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries.SummableFamil
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (SummableFamily Γ R α) where
  sub s s' :=
    { toFun := s - s'
      isPWO_iUnion_support' := by
        simp_rw [sub_eq_add_neg]
        exact (s + -s').isPWO_iUnion_support
      finite_co_support' g := by
        simp_rw [sub_eq_add_neg]
        exact (s + -s').finite_co_support' _ }

@[simp]
/-
**HahnSeries.SummableFamily.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summab
leFamily`。
形式化陈述：coe_sub (s t : SummableFamily Γ R α) : ⇑(s - t) = s - t
参数：s t : SummableFamily Γ R α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (s t : SummableFamily Γ R α) : ⇑(s - t) = s - t :=
  rfl
/-
**HahnSeries.SummableFamily.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summ
ableFamily`。
形式化陈述：sub_apply : (s - t) a = s a - t a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply : (s - t) a = s a - t a :=
  rfl
/-
**HahnSeries.SummableFamily.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries.SummableFamil
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (SummableFamily Γ R α) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_smul' _ _) (fun _ _ => coe_smul' _ _)

end AddCommGroup

section SMul

variable [PartialOrder Γ] [PartialOrder Γ'] [AddCommMonoid V]

variable [AddCommMonoid R] [SMulWithZero R V]

/-
**HahnSeries.SummableFamily.smul_support_subset_prod** 是 Mathlib 中的一个定理，位于命名空间 `
HahnSeries.SummableFamily`。
形式化陈述：smul_support_subset_prod (s : SummableFamily Γ R α) (t : SummableFamily Γ'
 V β) (gh : Γ × Γ') : (Function.support fun (i : α × β) => (s i.1).coeff gh.1 • 
(t i.2).coeff gh.2) subseteq ((s.finite_co_support' gh.1).prod (t.finite_co_supp
ort' gh.2)).toFinset
参数：s : SummableFamily Γ R α；t : SummableFamily Γ' V β；gh : Γ × Γ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
, s.Finite → t.Finite → (s ×ˢ t).Finite
· 使用定理 `HahnSeries.SummableFamily.finite_co_support'`：∀ {Γ : Type u_8} {R : Type
 u_9} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {α : Type u_7}   (self 
: HahnSeries.SummableFamily Γ R α)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用引理 `left_ne_zero_of_smul`：left_ne_zero_of_smul : a • b != 0 -> a != 0
· 使用引理 `right_ne_zero_of_smul`：right_ne_zero_of_smul {a : M} {b : A} : a • b != 
0 -> b != 0
-/
theorem smul_support_subset_prod (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (gh : Γ × Γ') :
    (Function.support fun (i : α × β) ↦ (s i.1).coeff gh.1 • (t i.2).coeff gh.2) ⊆
    ((s.finite_co_support' gh.1).prod (t.finite_co_support' gh.2)).toFinset := by
  intro _ hab
  simp_all only [Function.mem_support, ne_eq, Set.Finite.coe_toFinset, Set.mem_prod,
    Set.mem_ofPred_eq]
  exact ⟨left_ne_zero_of_smul hab, right_ne_zero_of_smul hab⟩
/-
**HahnSeries.SummableFamily.hasFiniteSupport_smul** 是 Mathlib 中的一个定理，位于命名空间 `Hah
nSeries.SummableFamily`。
形式化陈述：hasFiniteSupport_smul (s : SummableFamily Γ R α) (t : SummableFamily Γ' V 
β) (gh : Γ × Γ') : (fun (i : α × β) => (s i.1).coeff gh.1 • (t i.2).coeff gh.2).
HasFiniteSupport
参数：s : SummableFamily Γ R α；t : SummableFamily Γ' V β；gh : Γ × Γ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
, s.Finite → t.Finite → (s ×ˢ t).Finite
· 使用定理 `HahnSeries.SummableFamily.finite_co_support'`：∀ {Γ : Type u_8} {R : Type
 u_9} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {α : Type u_7}   (self 
: HahnSeries.SummableFamily Γ R α)…
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `HahnSeries.SummableFamily.smul_support_subset_prod`：smul_support_subset_
prod (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (gh : Γ × Γ') : (Fun
ction.support fun (i : α × β) => (s i.1)…
-/
theorem hasFiniteSupport_smul (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (gh : Γ × Γ') :
    (fun (i : α × β) ↦ (s i.1).coeff gh.1 • (t i.2).coeff gh.2).HasFiniteSupport :=
  Set.Finite.subset (Set.toFinite ((s.finite_co_support' gh.1).prod
    (t.finite_co_support' gh.2)).toFinset) (smul_support_subset_prod s t gh)

@[deprecated (since := "2026-03-03")] alias smul_support_finite := hasFiniteSupport_smul

variable [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ']

open HahnModule

set_option backward.isDefEq.respectTransparency false in
/-
**HahnSeries.SummableFamily.isPWO_iUnion_support_prod_smul** 是 Mathlib 中的一个定理，位于
命名空间 `HahnSeries.SummableFamily`。
形式化陈述：isPWO_iUnion_support_prod_smul {s : α -> R⟦Γ⟧} {t : β -> V⟦Γ'⟧} (hs : (⋃ a
, (s a).support).IsPWO) (ht : (⋃ b, (t b).support).IsPWO) : (⋃ (a : α × β), ((fu
n a => (of R).symm ((s a.1) • (of R) (t a.2))) a).support).IsPWO
参数：hs : (⋃ a, (s a).support).IsPWO；ht : (⋃ b, (t b).support).IsPWO。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.mono`：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α}, t.Is
PWO → s ⊆ t → s.IsPWO
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.IsPWO.vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : Preorder G] [ins
t_1 : Preorder P] [inst_2 : VAdd G P] [IsOrderedVAdd G P]   {s : Set G} {t : Set
 P},…
· 使用定理 `IsOrderedCancelVAdd.toIsOrderedVAdd`：∀ {G : Type u_3} {P : Type u_4} {in
st : LE G} {inst_1 : LE P} {inst_2 : VAdd G P} [self : IsOrderedCancelVAdd G P],
   IsOrderedVAdd G P
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.mem_support`：mem_support (x : R⟦Γ⟧) (a : Γ) : a in x.support 
↔ x.coeff a != 0
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `HahnModule.coeff_smul`：coeff_smul (x : R⟦Γ⟧) (y : HahnModule Γ' R V) (a 
: Γ') : ((of R).symm <| x • y).coeff a = ∑ ij in VAddAntidiagonal a (Set.VAddAnt
idiagonal.f…
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `Finset.support_vaddAntidiagonal_subset_vadd`：∀ {G : Type u_1} {P : Type 
u_2} [inst : VAdd G P] {s : Set G} {t : Set P}   (hst : ∀ (a : P), (s.vaddAntidi
agonal t a).Finite), {a | (Finset…
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.vadd_subset_vadd`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] 
{s₁ s₂ : Set α} {t₁ t₂ : Set β},   s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ +ᵥ t₁ ⊆ s₂ +ᵥ t₂
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
-/
theorem isPWO_iUnion_support_prod_smul {s : α → R⟦Γ⟧} {t : β → V⟦Γ'⟧}
    (hs : (⋃ a, (s a).support).IsPWO) (ht : (⋃ b, (t b).support).IsPWO) :
    (⋃ (a : α × β), ((fun a ↦ (of R).symm
      ((s a.1) • (of R) (t a.2))) a).support).IsPWO := by
  apply (hs.vadd ht).mono
  have hsupp : ∀ ab : α × β, support ((fun ab ↦ (of R).symm (s ab.1 • (of R) (t ab.2))) ab) ⊆
      (s ab.1).support +ᵥ (t ab.2).support := by
    intro ab
    refine Set.Subset.trans (fun x hx => ?_) (support_vaddAntidiagonal_subset_vadd fun a ↦
      Set.VAddAntidiagonal.finite_of_isPWO (s ab.1).isPWO_support (t ab.2).isPWO_support a)
    simp only [Set.mem_ofPred_eq]
    contrapose! hx
    rw [mem_support, not_not, HahnModule.coeff_smul, hx, sum_empty]
  refine Set.Subset.trans (Set.iUnion_mono fun a => (hsupp a)) ?_
  simp_all only [Set.iUnion_subset_iff, Prod.forall]
  exact fun a b => Set.vadd_subset_vadd (Set.subset_iUnion_of_subset a fun x y ↦ y)
    (Set.subset_iUnion_of_subset b fun x y ↦ y)
/-
**HahnSeries.SummableFamily.finite_co_support_prod_smul** 是 Mathlib 中的一个定理，位于命名空
间 `HahnSeries.SummableFamily`。
形式化陈述：finite_co_support_prod_smul (s : SummableFamily Γ R α) (t : SummableFamily
 Γ' V β) (g : Γ') : Finite {(ab : α × β) | ((fun (ab : α × β) => (of R).symm (s 
ab.1 • (of R) (t ab.2))) ab).coeff g != 0}
参数：s : SummableFamily Γ R α；t : SummableFamily Γ' V β；g : Γ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `HahnSeries.SummableFamily.isPWO_iUnion_support`：isPWO_iUnion_support (s 
: SummableFamily Γ R α) : Set.IsPWO (⋃ a : α, (s a).support)
· 使用定理 `Set.Finite.biUnion'`：∀ {α : Type u} {ι : Type u_1} {s : Set ι},   s.Fini
te →     ∀ {t : (i : ι) → i ∈ s → Set α}, (∀ (i : ι) (hi : i ∈ s), (t i hi).Fini
te) → (⋃ …
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `HahnSeries.SummableFamily.hasFiniteSupport_smul`：hasFiniteSupport_smul (
s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (gh : Γ × Γ') : (fun (i : 
α × β) => (s i.1).coeff gh.1 • (t i.2…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.exists_ne_zero_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, ∑ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f
 a ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用引理 `left_ne_zero_of_smul`：left_ne_zero_of_smul : a • b != 0 -> a != 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `right_ne_zero_of_smul`：right_ne_zero_of_smul {a : M} {b : A} : a • b != 
0 -> b != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_vaddAntidiagonal`：∀ {G : Type u_1} {P : Type u_2} [inst : VAd
d G P] {s : Set G} {t : Set P} (a : P) (h : (s.vaddAntidiagonal t a).Finite)   {
x : G × P}, x ∈ F…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem finite_co_support_prod_smul (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (g : Γ') :
    Finite {(ab : α × β) |
      ((fun (ab : α × β) ↦ (of R).symm (s ab.1 • (of R) (t ab.2))) ab).coeff g ≠ 0} := by
  apply ((VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO s.isPWO_iUnion_support
    t.isPWO_iUnion_support g)).finite_toSet.biUnion'
    (fun gh _ => hasFiniteSupport_smul s t gh)).subset _
  exact fun ab hab => by
    simp only [ne_eq, Set.mem_ofPred_eq] at hab
    obtain ⟨ij, hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    simp only [mem_coe, mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq,
      Function.mem_support, exists_prop, Prod.exists]
    exact ⟨ij.1, ij.2, ⟨⟨ab.1, left_ne_zero_of_smul hij.2⟩, ⟨ab.2, right_ne_zero_of_smul hij.2⟩,
      ((mem_vaddAntidiagonal _ _).mp hij.1).2.2⟩, hij.2⟩

/-- An elementwise scalar multiplication of one summable family on another. -/
@[simps]
/-
**HahnSeries.SummableFamily.smul** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.SummableF
amily`。
形式化陈述：smul (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) : SummableFami
ly Γ' V (α × β) where toFun ab
参数：s : SummableFamily Γ R α；t : SummableFamily Γ' V β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `HahnSeries.SummableFamily.finite_co_support_prod_smul`：finite_co_support
_prod_smul (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ') : Fin
ite {(ab : α × β) | ((fun (ab : α × β) => (…

--- 原说明 ---
An elementwise scalar multiplication of one summable family on another.
-/
def smul (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) : SummableFamily Γ' V (α × β) where
  toFun ab := (of R).symm (s (ab.1) • ((of R) (t (ab.2))))
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_prod_smul s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod_smul s t g
/-
**HahnSeries.SummableFamily.sum_vAddAntidiagonal_eq** 是 Mathlib 中的一个定理，位于命名空间 `H
ahnSeries.SummableFamily`。
形式化陈述：sum_vAddAntidiagonal_eq (s : SummableFamily Γ R α) (t : SummableFamily Γ' 
V β) (g : Γ') (a : α × β) : ∑ x in VAddAntidiagonal g (Set.VAddAntidiagonal.fini
te_of_isPWO (s a.1).isPWO_support' (t a.2).isPWO_support' g), (s a.1).coeff x.1 
• (t a.2).coeff x.2 = ∑ x in VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_
isPWO s.isPWO_iUnion_support' t.isPWO_iUnion_support' g), (s a.1).coeff x.1 • (t
 a.2).coeff x.2
参数：s : SummableFamily Γ R α；t : SummableFamily Γ' V β；g : Γ'；a : α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `HahnSeries.isPWO_support'`：∀ {Γ : Type u_1} {R : Type u_2} [inst : Parti
alOrder Γ] [inst_1 : Zero R] (self : HahnSeries Γ R),   (Function.support self.c
oeff).IsPWO
· 使用定理 `HahnSeries.SummableFamily.isPWO_iUnion_support'`：∀ {Γ : Type u_8} {R : T
ype u_9} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {α : Type u_7}   (se
lf : HahnSeries.SummableFamily Γ R α)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `trivial`：True
· 使用引理 `smul_eq_zero_of_left`：smul_eq_zero_of_left (h : a = 0) (b : A) : a • b =
 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem sum_vAddAntidiagonal_eq (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ')
    (a : α × β) :
    ∑ x ∈ VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO (s a.1).isPWO_support'
      (t a.2).isPWO_support' g), (s a.1).coeff x.1 • (t a.2).coeff x.2 =
    ∑ x ∈ VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO s.isPWO_iUnion_support'
      t.isPWO_iUnion_support' g), (s a.1).coeff x.1 • (t a.2).coeff x.2 := by
  refine sum_subset (fun gh hgh => ?_) fun gh hgh h => ?_
  · simp_all only [mem_vaddAntidiagonal, Function.mem_support, Set.mem_iUnion, mem_support]
    exact ⟨Exists.intro a.1 hgh.1, Exists.intro a.2 hgh.2.1, trivial⟩
  · by_cases hs : (s a.1).coeff gh.1 = 0
    · exact smul_eq_zero_of_left hs ((t a.2).coeff gh.2)
    · simp_all

set_option backward.isDefEq.respectTransparency false in
/-
**HahnSeries.SummableFamily.coeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Sum
mableFamily`。
形式化陈述：coeff_smul {R} {V} [Semiring R] [AddCommMonoid V] [Module R V] (s : Summab
leFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ') : (smul s t).hsum.coeff g =
 ∑ gh in VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO s.isPWO_iUnion
_support t.isPWO_iUnion_support g), (s.hsum.coeff gh.1) • (t.hsum.coeff gh.2)
参数：s : SummableFamily Γ R α；t : SummableFamily Γ' V β；g : Γ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `HahnSeries.SummableFamily.isPWO_iUnion_support`：isPWO_iUnion_support (s 
: SummableFamily Γ R α) : Set.IsPWO (⋃ a : α, (s a).support)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.coeff_hsum`：coeff_hsum {s : SummableFamily Γ R
 α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.SummableFamily.smul_toFun`：∀ {Γ : Type u_1} {Γ' : Type u_2} {
R : Type u_3} {V : Type u_4} {α : Type u_5} {β : Type u_6} [inst : PartialOrder 
Γ]   [inst_1 : PartialOrde…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.VAddAntidiagonal.congr_simp`：∀ {G : Type u_1} {P : Type u_2} [ins
t : VAdd G P] {s s_1 : Set G} (e_s : s = s_1) {t t_1 : Set P} (e_t : t = t_1)   
(a a_1 : P) (e_a : a = a…
· 使用定理 `HahnSeries.SummableFamily.coeff_hsum_eq_sum`：coeff_hsum_eq_sum {s : Summ
ableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ i in (s.coeff g).support, (s i).c
oeff g
· 使用定理 `HahnSeries.SummableFamily.isPWO_iUnion_support'`：∀ {Γ : Type u_8} {R : T
ype u_9} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {α : Type u_7}   (se
lf : HahnSeries.SummableFamily Γ R α)…
· 使用定理 `HahnSeries.isPWO_support'`：∀ {Γ : Type u_1} {R : Type u_2} [inst : Parti
alOrder Γ] [inst_1 : Zero R] (self : HahnSeries Γ R),   (Function.support self.c
oeff).IsPWO
· 使用定理 `HahnSeries.SummableFamily.sum_vAddAntidiagonal_eq`：sum_vAddAntidiagonal_
eq (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ') (a : α × β) :
 ∑ x in VAddAntidiagonal g (Set.VAddAnt…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sum_finsum_comm`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst : 
AddCommMonoid M] (s : Finset α) (f : α → β → M),   (∀ a ∈ s, Function.HasFiniteS
uppor…
· 使用定理 `HahnSeries.SummableFamily.hasFiniteSupport_smul`：hasFiniteSupport_smul (
s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (gh : Γ × Γ') : (fun (i : 
α × β) => (s i.1).coeff gh.1 • (t i.2…
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `Finset.sum_product_right'`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5
} [inst : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ → α → β),   ∑ x 
∈ s ×ˢ t, f x.1…
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Set.Finite.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
, s.Finite → t.Finite → (s ×ˢ t).Finite
· 使用定理 `HahnSeries.SummableFamily.finite_co_support'`：∀ {Γ : Type u_8} {R : Type
 u_9} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {α : Type u_7}   (self 
: HahnSeries.SummableFamily Γ R α)…
· 使用定理 `HahnSeries.SummableFamily.smul_support_subset_prod`：smul_support_subset_
prod (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (gh : Γ × Γ') : (Fun
ction.support fun (i : α × β) => (s i.1)…
· 使用定理 `HahnSeries.SummableFamily.finite_co_support`：finite_co_support (s : Summ
ableFamily Γ R α) (g : Γ) : (fun a => (s a).coeff g).HasFiniteSupport
（共 36 条，此处仅展示前 30 条）
-/
theorem coeff_smul {R} {V} [Semiring R] [AddCommMonoid V] [Module R V]
    (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ') :
    (smul s t).hsum.coeff g =
    ∑ gh ∈ VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO s.isPWO_iUnion_support
      t.isPWO_iUnion_support g), (s.hsum.coeff gh.1) • (t.hsum.coeff gh.2) := by
  rw [coeff_hsum]
  simp only [coeff_hsum_eq_sum, smul_toFun, HahnModule.coeff_smul, Equiv.symm_apply_apply]
  simp_rw [sum_vAddAntidiagonal_eq, Finset.smul_sum, Finset.sum_smul]
  rw [← sum_finsum_comm _ _ <| fun gh _ => hasFiniteSupport_smul s t gh]
  refine sum_congr rfl fun gh _ => ?_
  rw [finsum_eq_sum _ (hasFiniteSupport_smul s t gh), ← sum_product_right']
  refine sum_subset (fun ab hab => ?_) (fun ab _ hab => by simp_all)
  have hsupp := smul_support_subset_prod s t gh
  simp_all only [mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq, Set.Finite.mem_toFinset,
    Function.mem_support, Set.Finite.coe_toFinset, support_subset_iff, Set.mem_prod,
    Set.mem_ofPred_eq, Prod.forall, coeff_support, mem_product]
  exact hsupp ab.1 ab.2 hab

set_option backward.isDefEq.respectTransparency false in
/-
**HahnSeries.SummableFamily.smul_hsum** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summ
ableFamily`。
形式化陈述：smul_hsum {R} {V} [Semiring R] [AddCommMonoid V] [Module R V] (s : Summabl
eFamily Γ R α) (t : SummableFamily Γ' V β) : (smul s t).hsum = (of R).symm (s.hs
um • (of R) (t.hsum))
参数：s : SummableFamily Γ R α；t : SummableFamily Γ' V β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.VAddAntidiagonal.finite_of_isPWO`：∀ {G : Type u_1} {P : Type u_2} {s
 : Set G} {t : Set P} [inst : PartialOrder G] [inst_1 : PartialOrder P]   [inst_
2 : VAdd G P] [IsOrderedCa…
· 使用定理 `HahnSeries.SummableFamily.isPWO_iUnion_support`：isPWO_iUnion_support (s 
: SummableFamily Γ R α) : Set.IsPWO (⋃ a : α, (s a).support)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.coeff_smul`：coeff_smul {R} {V} [Semiring R] [A
ddCommMonoid V] [Module R V] (s : SummableFamily Γ R α) (t : SummableFamily Γ' V
 β) (g : Γ') : (smul s t).…
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `HahnModule.coeff_smul`：coeff_smul (x : R⟦Γ⟧) (y : HahnModule Γ' R V) (a 
: Γ') : ((of R).symm <| x • y).coeff a = ∑ ij in VAddAntidiagonal a (Set.VAddAnt
idiagonal.f…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_of_injOn`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [ins
t : AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e 
: ι → κ),…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.exists_ne_zero_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, ∑ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f
 a ≠ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HahnSeries.SummableFamily.coeff_hsum_eq_sum`：coeff_hsum_eq_sum {s : Summ
ableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ i in (s.coeff g).support, (s i).c
oeff g
· 使用定理 `HahnSeries.SummableFamily.finite_co_support`：finite_co_support (s : Summ
ableFamily Γ R α) (g : Γ) : (fun a => (s a).coeff g).HasFiniteSupport
· 使用定理 `HahnSeries.SummableFamily.coeff_support`：∀ {Γ : Type u_1} {R : Type u_3}
 {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R]   (s : HahnSe
ries.SummableFamily Γ R α) (g…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `finsum_zero`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M], ∑
ᶠ (x : α), 0 = 0
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用引理 `smul_eq_zero_of_left`：smul_eq_zero_of_left (h : a = 0) (b : A) : a • b =
 0
（共 37 条，此处仅展示前 30 条）
-/
theorem smul_hsum {R} {V} [Semiring R] [AddCommMonoid V] [Module R V]
    (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) :
    (smul s t).hsum = (of R).symm (s.hsum • (of R) (t.hsum)) := by
  ext g
  rw [coeff_smul s t g, HahnModule.coeff_smul, Equiv.symm_apply_apply]
  refine Eq.symm (sum_of_injOn (fun a ↦ a) (fun _ _ _ _ h ↦ h) (fun _ hgh => ?_)
    (fun gh _ hgh => ?_) fun _ _ => by simp)
  · simp_all only [mem_coe, mem_vaddAntidiagonal, mem_support, ne_eq, Set.mem_iUnion, and_true]
    constructor
    · rw [coeff_hsum_eq_sum] at hgh
      have h' := Finset.exists_ne_zero_of_sum_ne_zero hgh.1
      simpa using h'
    · by_contra hi
      simp_all
  · simp only [Set.image_id', mem_coe, mem_vaddAntidiagonal, mem_support, ne_eq, not_and] at hgh
    by_cases h : s.hsum.coeff gh.1 = 0
    · exact smul_eq_zero_of_left h (t.hsum.coeff gh.2)
    · simp_all
/-
**HahnSeries.SummableFamily.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries.SummableFamil
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R⟦Γ⟧ (SummableFamily Γ' V β) where
  smul x t := Equiv (Equiv.punitProd β) <| smul (const Unit x) t
/-
**HahnSeries.SummableFamily.smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summab
leFamily`。
形式化陈述：smul_eq {x : R⟦Γ⟧} {t : SummableFamily Γ' V β} : x • t = Equiv (Equiv.puni
tProd β) (smul (const Unit x) t)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_eq {x : R⟦Γ⟧} {t : SummableFamily Γ' V β} :
    x • t = Equiv (Equiv.punitProd β) (smul (const Unit x) t) :=
  rfl

@[simp]
/-
**HahnSeries.SummableFamily.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Sum
mableFamily`。
形式化陈述：smul_apply {x : R⟦Γ⟧} {s : SummableFamily Γ' V α} {a : α} : (x • s) a = (o
f R).symm (x • of R (s a))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply {x : R⟦Γ⟧} {s : SummableFamily Γ' V α} {a : α} :
    (x • s) a = (of R).symm (x • of R (s a)) :=
  rfl

@[simp]
/-
**HahnSeries.SummableFamily.hsum_smul_module** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeri
es.SummableFamily`。
形式化陈述：hsum_smul_module {R} {V} [Semiring R] [AddCommMonoid V] [Module R V] {x : 
R⟦Γ⟧} {s : SummableFamily Γ' V α} : (x • s).hsum = (of R).symm (x • of R s.hsum)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.smul_eq`：smul_eq {x : R⟦Γ⟧} {t : SummableFamil
y Γ' V β} : x • t = Equiv (Equiv.punitProd β) (smul (const Unit x) t)
· 使用定理 `HahnSeries.SummableFamily.hsum_equiv`：hsum_equiv (e : α ≃ β) (s : Summab
leFamily Γ R α) : (Equiv e s).hsum = s.hsum
· 使用定理 `HahnSeries.SummableFamily.smul_hsum`：smul_hsum {R} {V} [Semiring R] [Add
CommMonoid V] [Module R V] (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β
) : (smul s t).hsum = (of…
· 使用定理 `HahnSeries.SummableFamily.hsum_unique`：hsum_unique {ι} [Unique ι] (x : S
ummableFamily Γ R ι) : x.hsum = x default
· 使用定理 `HahnSeries.SummableFamily.const_toFun`：∀ {Γ : Type u_1} {R : Type u_3} [
inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] (ι : Type u_7) [inst_2 : Finit
e ι]   (x : HahnSeries Γ R)…
-/
theorem hsum_smul_module {R} {V} [Semiring R] [AddCommMonoid V] [Module R V] {x : R⟦Γ⟧}
    {s : SummableFamily Γ' V α} :
    (x • s).hsum = (of R).symm (x • of R s.hsum) := by
  rw [smul_eq, hsum_equiv, smul_hsum, hsum_unique, const_toFun]

end SMul

section Semiring

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [PartialOrder Γ'] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [Semiring R]

/-
**HahnSeries.SummableFamily.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries.SummableFamil
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid V] [Module R V] : Module R⟦Γ⟧ (SummableFamily Γ' V α) where
  smul_zero _ := ext fun _ => by simp
  zero_smul _ := ext fun _ => by simp
  one_smul _ := ext fun _ => by rw [smul_apply, HahnModule.one_smul', Equiv.symm_apply_apply]
  add_smul _ _ _ := ext fun _ => by simp [add_smul]
  smul_add _ _ _ := ext fun _ => by simp
  mul_smul _ _ _ := ext fun _ => by simp [HahnModule.instModule.mul_smul]
/-
**HahnSeries.SummableFamily.hsum_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summ
ableFamily`。
形式化陈述：hsum_smul {x : R⟦Γ⟧} {s : SummableFamily Γ R α} : (x • s).hsum = x * s.hsu
m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.hsum_smul_module`：hsum_smul_module {R} {V} [Se
miring R] [AddCommMonoid V] [Module R V] {x : R⟦Γ⟧} {s : SummableFamily Γ' V α} 
: (x • s).hsum = (of R).symm (x …
· 使用定理 `HahnSeries.of_symm_smul_of_eq_mul`：of_symm_smul_of_eq_mul [NonUnitalNonA
ssocSemiring R] {x y : R⟦Γ⟧} : (HahnModule.of R).symm (x • HahnModule.of R y) = 
x * y
-/
theorem hsum_smul {x : R⟦Γ⟧} {s : SummableFamily Γ R α} :
    (x • s).hsum = x * s.hsum := by
  rw [hsum_smul_module, of_symm_smul_of_eq_mul]

/-- The summation of a `summable_family` as a `LinearMap`. -/
@[simps]
/-
**HahnSeries.SummableFamily.lsum** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.SummableF
amily`。
形式化陈述：lsum : SummableFamily Γ R α ->ₗ[R⟦Γ⟧] R⟦Γ⟧ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.hsum_smul`：hsum_smul {x : R⟦Γ⟧} {s : SummableF
amily Γ R α} : (x • s).hsum = x * s.hsum

--- 原说明 ---
The summation of a `summable_family` as a `LinearMap`.
-/
def lsum : SummableFamily Γ R α →ₗ[R⟦Γ⟧] R⟦Γ⟧ where
  toFun := hsum
  map_add' _ _ := hsum_add
  map_smul' _ _ := hsum_smul

@[simp]
/-
**HahnSeries.SummableFamily.hsum_sub** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summa
bleFamily`。
形式化陈述：hsum_sub {R : Type*} [Ring R] {s t : SummableFamily Γ R α} : (s - t).hsum 
= s.hsum - t.hsum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.SummableFamily.lsum_apply`：∀ {Γ : Type u_1} {R : Type u_3} {α
 : Type u_5} [inst : AddCommMonoid Γ] [inst_1 : PartialOrder Γ]   [inst_2 : IsOr
deredCancelAddMonoid Γ] [i…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem hsum_sub {R : Type*} [Ring R] {s t : SummableFamily Γ R α} :
    (s - t).hsum = s.hsum - t.hsum := by
  rw [← lsum_apply, map_sub, lsum_apply, lsum_apply]
/-
**HahnSeries.SummableFamily.isPWO_iUnion_support_prod_mul** 是 Mathlib 中的一个定理，位于命
名空间 `HahnSeries.SummableFamily`。
形式化陈述：isPWO_iUnion_support_prod_mul {s : α -> R⟦Γ⟧} {t : β -> R⟦Γ⟧} (hs : (⋃ a, 
(s a).support).IsPWO) (ht : (⋃ b, (t b).support).IsPWO) : (⋃ (a : α × β), ((fun 
a => ((s a.1) * (t a.2))) a).support).IsPWO
参数：hs : (⋃ a, (s a).support).IsPWO；ht : (⋃ b, (t b).support).IsPWO。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.isPWO_iUnion_support_prod_smul`：isPWO_iUnion_s
upport_prod_smul {s : α -> R⟦Γ⟧} {t : β -> V⟦Γ'⟧} (hs : (⋃ a, (s a).support).IsP
WO) (ht : (⋃ b, (t b).support).IsPWO) : (⋃ (a …
-/
theorem isPWO_iUnion_support_prod_mul {s : α → R⟦Γ⟧} {t : β → R⟦Γ⟧}
    (hs : (⋃ a, (s a).support).IsPWO) (ht : (⋃ b, (t b).support).IsPWO) :
    (⋃ (a : α × β), ((fun a ↦ ((s a.1) * (t a.2))) a).support).IsPWO :=
  isPWO_iUnion_support_prod_smul hs ht
/-
**HahnSeries.SummableFamily.finite_co_support_prod_mul** 是 Mathlib 中的一个定理，位于命名空间
 `HahnSeries.SummableFamily`。
形式化陈述：finite_co_support_prod_mul (s : SummableFamily Γ R α) (t : SummableFamily 
Γ R β) (g : Γ) : Finite {(a : α × β) | ((fun (a : α × β) => (s a.1 * t a.2)) a).
coeff g != 0}
参数：s : SummableFamily Γ R α；t : SummableFamily Γ R β；g : Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.finite_co_support_prod_smul`：finite_co_support
_prod_smul (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ') : Fin
ite {(ab : α × β) | ((fun (ab : α × β) => (…
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
-/
theorem finite_co_support_prod_mul (s : SummableFamily Γ R α)
    (t : SummableFamily Γ R β) (g : Γ) :
    Finite {(a : α × β) | ((fun (a : α × β) ↦ (s a.1 * t a.2)) a).coeff g ≠ 0} :=
  finite_co_support_prod_smul s t g

/-- A summable family given by pointwise multiplication of a pair of summable families. -/
@[simps]
/-
**HahnSeries.SummableFamily.mul** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.SummableFa
mily`。
形式化陈述：mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) : (SummableFamil
y Γ R (α × β)) where toFun a
参数：s : SummableFamily Γ R α；t : SummableFamily Γ R β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.finite_co_support_prod_mul`：finite_co_support_
prod_mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) (g : Γ) : Finite 
{(a : α × β) | ((fun (a : α × β) => (s a.1…

--- 原说明 ---
A summable family given by pointwise multiplication of a pair of summable famili
es.
-/
def mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    (SummableFamily Γ R (α × β)) where
  toFun a := s (a.1) * t (a.2)
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_prod_mul s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod_mul s t g
/-
**HahnSeries.SummableFamily.mul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Su
mmableFamily`。
形式化陈述：mul_eq_smul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) : mul s 
t = smul s t
参数：s : SummableFamily Γ R α；t : SummableFamily Γ R β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_eq_smul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    mul s t = smul s t :=
  rfl
/-
**HahnSeries.SummableFamily.coeff_hsum_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries
.SummableFamily`。
形式化陈述：coeff_hsum_mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) (g : 
Γ) : (mul s t).hsum.coeff g = ∑ gh in antidiagonal s.isPWO_iUnion_support t.isPW
O_iUnion_support g, (s.hsum.coeff gh.1) * (t.hsum.coeff gh.2)
参数：s : SummableFamily Γ R α；t : SummableFamily Γ R β；g : Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.isPWO_iUnion_support`：isPWO_iUnion_support (s 
: SummableFamily Γ R α) : Set.IsPWO (⋃ a : α, (s a).support)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `HahnSeries.SummableFamily.coeff_smul`：coeff_smul {R} {V} [Semiring R] [A
ddCommMonoid V] [Module R V] (s : SummableFamily Γ R α) (t : SummableFamily Γ' V
 β) (g : Γ') : (smul s t).…
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
-/
theorem coeff_hsum_mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) (g : Γ) :
    (mul s t).hsum.coeff g = ∑ gh ∈ antidiagonal s.isPWO_iUnion_support
      t.isPWO_iUnion_support g, (s.hsum.coeff gh.1) * (t.hsum.coeff gh.2) := by
  simp_rw [← smul_eq_mul, mul_eq_smul]
  exact coeff_smul s t g
/-
**HahnSeries.SummableFamily.hsum_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Summa
bleFamily`。
形式化陈述：hsum_mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) : (mul s t)
.hsum = s.hsum * t.hsum
参数：s : SummableFamily Γ R α；t : SummableFamily Γ R β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
· 使用定理 `HahnSeries.SummableFamily.mul_eq_smul`：mul_eq_smul (s : SummableFamily Γ
 R α) (t : SummableFamily Γ R β) : mul s t = smul s t
· 使用定理 `HahnSeries.SummableFamily.smul_hsum`：smul_hsum {R} {V} [Semiring R] [Add
CommMonoid V] [Module R V] (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β
) : (smul s t).hsum = (of…
-/
theorem hsum_mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    (mul s t).hsum = s.hsum * t.hsum := by
  rw [← smul_eq_mul, mul_eq_smul]
  exact smul_hsum s t

end Semiring

section OfFinsupp

variable [PartialOrder Γ] [AddCommMonoid R]

/-- A family with only finitely many nonzero elements is summable. -/
/-
**HahnSeries.SummableFamily.ofFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.Summ
ableFamily`。
形式化陈述：ofFinsupp (f : α ->₀ R⟦Γ⟧) : SummableFamily Γ R α where toFun
参数：f : α ->₀ R⟦Γ⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family with only finitely many nonzero elements is summable.
-/
def ofFinsupp (f : α →₀ R⟦Γ⟧) : SummableFamily Γ R α where
  toFun := f
  isPWO_iUnion_support' := by
    apply (f.support.isPWO_bUnion.2 fun a _ => (f a).isPWO_support).mono
    refine Set.iUnion_subset_iff.2 fun a g hg => ?_
    have haf : a ∈ f.support := by
      rw [Finsupp.mem_support_iff, ← support_nonempty_iff]
      exact ⟨g, hg⟩
    exact Set.mem_biUnion haf hg
  finite_co_support' g := by
    refine f.support.finite_toSet.subset fun a ha => ?_
    simp only [mem_coe, Finsupp.mem_support_iff, Ne]
    contrapose ha
    simp [ha]

@[simp]
/-
**HahnSeries.SummableFamily.coe_ofFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.
SummableFamily`。
形式化陈述：coe_ofFinsupp {f : α ->₀ R⟦Γ⟧} : ⇑(SummableFamily.ofFinsupp f) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofFinsupp {f : α →₀ R⟦Γ⟧} : ⇑(SummableFamily.ofFinsupp f) = f :=
  rfl

@[simp]
/-
**HahnSeries.SummableFamily.hsum_ofFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries
.SummableFamily`。
形式化陈述：hsum_ofFinsupp {f : α ->₀ R⟦Γ⟧} : (ofFinsupp f).hsum = f.sum fun _ => id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HahnSeries.coeff.addMonoidHom_apply`：∀ {Γ : Type u_1} {R : Type u_3} [in
st : PartialOrder Γ] [inst_1 : AddMonoid R] (g : Γ) (f : HahnSeries Γ R),   (Hah
nSeries.coeff.addMonoidHo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem hsum_ofFinsupp {f : α →₀ R⟦Γ⟧} : (ofFinsupp f).hsum = f.sum fun _ => id := by
  ext g
  simp only [coeff_hsum, coe_ofFinsupp, Finsupp.sum]
  simp_rw [← coeff.addMonoidHom_apply, id]
  rw [map_sum, finsum_eq_sum_of_support_subset]
  intro x h
  simp only [mem_coe, Finsupp.mem_support_iff, Ne]
  contrapose h
  simp [h]

end OfFinsupp

section EmbDomain

variable [PartialOrder Γ] [AddCommMonoid R]

open scoped Classical in
/-- A summable family can be reindexed by an embedding without changing its sum. -/
/-
**HahnSeries.SummableFamily.embDomain** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.Summ
ableFamily`。
形式化陈述：embDomain (s : SummableFamily Γ R α) (f : α ↪ β) : SummableFamily Γ R β wh
ere toFun b
参数：s : SummableFamily Γ R α；f : α ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A summable family can be reindexed by an embedding without changing its sum.
-/
def embDomain (s : SummableFamily Γ R α) (f : α ↪ β) : SummableFamily Γ R β where
  toFun b := if h : b ∈ Set.range f then s (Classical.choose h) else 0
  isPWO_iUnion_support' := by
    refine s.isPWO_iUnion_support.mono (Set.iUnion_subset fun b g h => ?_)
    by_cases hb : b ∈ Set.range f
    · rw [dif_pos hb] at h
      exact Set.mem_iUnion.2 ⟨Classical.choose hb, h⟩
    · simp [-Set.mem_range, dif_neg hb] at h
  finite_co_support' g :=
    ((s.finite_co_support g).image f).subset
      (by
        intro b h
        by_cases hb : b ∈ Set.range f
        · simp only [Ne, Set.mem_ofPred_eq, dif_pos hb] at h
          exact ⟨Classical.choose hb, h, Classical.choose_spec hb⟩
        · simp only [Ne, Set.mem_ofPred_eq, dif_neg hb, coeff_zero, not_true_eq_false] at h)

variable (s : SummableFamily Γ R α) (f : α ↪ β) {a : α} {b : β}

open scoped Classical in
/-
**HahnSeries.SummableFamily.embDomain_apply** 是 Mathlib 中的一个定理，位于命名空间 `HahnSerie
s.SummableFamily`。
形式化陈述：embDomain_apply : s.embDomain f b = if h : b in Set.range f then s (Classi
cal.choose h) else 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem embDomain_apply :
    s.embDomain f b = if h : b ∈ Set.range f then s (Classical.choose h) else 0 :=
  rfl

@[simp]
/-
**HahnSeries.SummableFamily.embDomain_image** 是 Mathlib 中的一个定理，位于命名空间 `HahnSerie
s.SummableFamily`。
形式化陈述：embDomain_image : s.embDomain f (f a) = s a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.embDomain_apply`：embDomain_apply : s.embDomain
 f b = if h : b in Set.range f then s (Classical.choose h) else 0
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem embDomain_image : s.embDomain f (f a) = s a := by
  rw [embDomain_apply, dif_pos (Set.mem_range_self a)]
  exact congr rfl (f.injective (Classical.choose_spec (Set.mem_range_self a)))

@[simp]
/-
**HahnSeries.SummableFamily.embDomain_of_notMem_range** 是 Mathlib 中的一个定理，位于命名空间 
`HahnSeries.SummableFamily`。
形式化陈述：embDomain_of_notMem_range (h : b ∉ Set.range f) : s.embDomain f b = 0
参数：h : b ∉ Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.embDomain_apply`：embDomain_apply : s.embDomain
 f b = if h : b in Set.range f then s (Classical.choose h) else 0
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem embDomain_of_notMem_range (h : b ∉ Set.range f) : s.embDomain f b = 0 := by
  rw [embDomain_apply, dif_neg h]

@[deprecated (since := "2026-07-15")] alias embDomain_notin_range := embDomain_of_notMem_range

@[simp]
/-
**HahnSeries.SummableFamily.hsum_embDomain** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries
.SummableFamily`。
形式化陈述：hsum_embDomain : (s.embDomain f).hsum = s.hsum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
· 使用定理 `dite_apply`：dite_apply (f : P -> forall a, σ a) (g : ¬P -> forall a, σ a
) (a : α) : (dite P f g) a = dite P (fun h => f h a) fun h => g h a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `finsum_emb_domain`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst 
: AddCommMonoid M] (f : α ↪ β)   [inst_1 : DecidablePred fun x => x ∈ Set.range 
⇑f] (g …
-/
theorem hsum_embDomain : (s.embDomain f).hsum = s.hsum := by
  classical
  ext g
  simp only [coeff_hsum, embDomain_apply, apply_dite HahnSeries.coeff, dite_apply, coeff_zero]
  exact finsum_emb_domain f fun a => (s a).coeff g

end EmbDomain

section powers

/-
**HahnSeries.SummableFamily.support_pow_subset_closure** 是 Mathlib 中的一个定理，位于命名空间
 `HahnSeries.SummableFamily`。
形式化陈述：support_pow_subset_closure [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCa
ncelAddMonoid Γ] [Semiring R] (x : R⟦Γ⟧) (n : Nat) : support (x ^ n) subseteq Ad
dSubmonoid.closure (support x)
参数：x : R⟦Γ⟧；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
· 使用定理 `AddSubmonoid.zero_mem`：∀ {M : Type u_1} [inst : AddZeroClass M] (S : Add
Submonoid M), 0 ∈ S
· 使用定理 `HahnSeries.support_mul_subset`：support_mul_subset [NonUnitalNonAssocSemi
ring R] {x y : R⟦Γ⟧} : support (x * y) subseteq support x + support y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `AddSubmonoid.add_mem`：∀ {M : Type u_1} [inst : AddZeroClass M] (S : AddS
ubmonoid M) {x y : M}, x ∈ S → y ∈ S → x + y ∈ S
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
-/
theorem support_pow_subset_closure [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [Semiring R] (x : R⟦Γ⟧)
    (n : ℕ) : support (x ^ n) ⊆ AddSubmonoid.closure (support x) := by
  intro g hn
  induction n generalizing g with
  | zero =>
    simp only [pow_zero, mem_support, coeff_one, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    simp only [hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
  | succ n ih =>
    obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (ih hi) (AddSubmonoid.subset_closure hj))
/-
**HahnSeries.SummableFamily.isPWO_iUnion_support_powers** 是 Mathlib 中的一个定理，位于命名空
间 `HahnSeries.SummableFamily`。
形式化陈述：isPWO_iUnion_support_powers [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCa
ncelAddMonoid Γ] [Semiring R] {x : R⟦Γ⟧} (hx : 0 <= x.order) : (⋃ n : Nat, (x ^ 
n).support).IsPWO
参数：hx : 0 <= x.order。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.mono`：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α}, t.Is
PWO → s ⊆ t → s.IsPWO
· 使用定理 `Set.IsPWO.addSubmonoid_closure`：∀ {α : Type u_1} [inst : AddCommMonoid α
] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α] {s : Set α},   (∀ x ∈ s
, 0 ≤ x) → s.IsPWO →…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `HahnSeries.order_le_of_coeff_ne_zero`：order_le_of_coeff_ne_zero {Γ} [Zer
o Γ] [LinearOrder Γ] {x : R⟦Γ⟧} {g : Γ} (h : x.coeff g != 0) : x.order <= g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `HahnSeries.isPWO_support'`：∀ {Γ : Type u_1} {R : Type u_2} [inst : Parti
alOrder Γ] [inst_1 : Zero R] (self : HahnSeries Γ R),   (Function.support self.c
oeff).IsPWO
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `HahnSeries.SummableFamily.support_pow_subset_closure`：support_pow_subset
_closure [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ] [Semiri
ng R] (x : R⟦Γ⟧) (n : Nat) : support (x ^ …
-/
theorem isPWO_iUnion_support_powers [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [Semiring R]
    {x : R⟦Γ⟧} (hx : 0 ≤ x.order) :
    (⋃ n : ℕ, (x ^ n).support).IsPWO :=
  (x.isPWO_support'.addSubmonoid_closure
    fun _ hg => le_trans hx (order_le_of_coeff_ne_zero (Function.mem_support.mp hg))).mono
    (Set.iUnion_subset fun n => support_pow_subset_closure x n)
/-
**HahnSeries.SummableFamily.co_support_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSerie
s.SummableFamily`。
形式化陈述：co_support_zero [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMono
id Γ] [Semiring R] (g : Γ) : {a | ¬((0 : R⟦Γ⟧) ^ a).coeff g = 0} subseteq {0}
参数：g : Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem co_support_zero [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [Semiring R] (g : Γ) :
    {a | ¬((0 : R⟦Γ⟧) ^ a).coeff g = 0} ⊆ {0} := by
  simp only [Set.subset_singleton_iff, Set.mem_ofPred_eq]
  intro n hn
  by_contra h'
  simp_all only [ne_eq, not_false_eq_true, zero_pow, coeff_zero, not_true_eq_false]

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
/-
**HahnSeries.SummableFamily.pow_finite_co_support** 是 Mathlib 中的一个定理，位于命名空间 `Hah
nSeries.SummableFamily`。
形式化陈述：pow_finite_co_support {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (g : Γ) : Set.Finit
e {a | ((fun n => x ^ n) a).coeff g != 0}
参数：hx : 0 < x.orderTop；g : Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.isPWO_iUnion_support_powers`：isPWO_iUnion_supp
ort_powers [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Semir
ing R] {x : R⟦Γ⟧} (hx : 0 <= x.order) : (⋃ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `HahnSeries.zero_le_orderTop_iff`：zero_le_orderTop_iff {x : R⟦Γ⟧} : 0 <= 
x.orderTop ↔ 0 <= x.order
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `HahnSeries.SummableFamily.co_support_zero`：co_support_zero [AddCommMonoi
d Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R] (g : Γ) : {a | ¬
((0 : R⟦Γ⟧) ^ a).coeff g = 0} s…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.WellFoundedOn.induction`：∀ {α : Type u_2} {r : α → α → Prop} {s : Se
t α} {x : α},   s.WellFoundedOn r → x ∈ s → ∀ {P : α → Prop}, (∀ y ∈ s, (∀ z ∈ s
, r z y → P z) → …
· 使用定理 `Set.IsPWO.isWF`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.IsPW
O → s.IsWF
· 使用定理 `HahnSeries.isPWO_support`：isPWO_support (x : R⟦Γ⟧) : x.support.IsPWO
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_antidiagonal`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst
_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α] {s t : Set α}   {hs :
 s.IsPWO} {ht…
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `lt_add_of_pos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : L
T α] [AddRightStrictMono α] (a : α) {b : α}, 0 < b → a < b + a
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
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
（共 46 条，此处仅展示前 30 条）
-/
theorem pow_finite_co_support {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (g : Γ) :
    Set.Finite {a | ((fun n ↦ x ^ n) a).coeff g ≠ 0} := by
  have hpwo : Set.IsPWO (⋃ n, support (x ^ n)) :=
    isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt hx)
  by_cases h0 : x = 0; · exact h0 ▸ Set.Finite.subset (Set.finite_singleton 0) (co_support_zero g)
  by_cases hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  apply hpwo.isWF.induction hg
  intro y ys hy
  refine ((((antidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion
    fun ij hij => hy ij.snd (mem_antidiagonal.1 (mem_coe.1 hij)).2.1 ?_).image Nat.succ).union
      (Set.finite_singleton 0)).subset ?_
  · obtain ⟨hi, _, rfl⟩ := mem_antidiagonal.1 (mem_coe.1 hij)
    exact lt_add_of_pos_left ij.2 <| lt_of_lt_of_le ((zero_lt_orderTop_iff h0).mp hx) <|
      order_le_of_coeff_ne_zero <| Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hn
      refine Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨?_, hi⟩⟩, rfl⟩
      simp only [mem_coe, mem_antidiagonal, mem_support, ne_eq, Set.mem_iUnion]
      exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

/-- A summable family of powers of a Hahn series `x`. If `x` has non-positive `orderTop`, then
return a junk value given by pretending `x = 0`. -/
@[simps]
/-
**HahnSeries.SummableFamily.powers** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries.Summabl
eFamily`。
形式化陈述：powers (x : R⟦Γ⟧) : SummableFamily Γ R Nat where toFun n
参数：x : R⟦Γ⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A summable family of powers of a Hahn series `x`. If `x` has non-positive `order
Top`, then
return a junk value given by pretending `x = 0`.
-/
def powers (x : R⟦Γ⟧) : SummableFamily Γ R ℕ where
  toFun n := (if 0 < x.orderTop then x else 0) ^ n
  isPWO_iUnion_support' := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt h)
    · simp only [h, ↓reduceIte]
      apply isPWO_iUnion_support_powers
      rw [order_zero]
  finite_co_support' g := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact pow_finite_co_support h g
    · simp only [h, ↓reduceIte]
      exact pow_finite_co_support (orderTop_zero (R := R) (Γ := Γ) ▸ WithTop.top_pos) g
/-
**HahnSeries.SummableFamily.powers_of_orderTop_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ha
hnSeries.SummableFamily`。
形式化陈述：powers_of_orderTop_pos {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (n : Nat) : powers
 x n = x ^ n
参数：hx : 0 < x.orderTop；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powers_of_orderTop_pos {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (n : ℕ) :
    powers x n = x ^ n := by
  simp [hx]
/-
**HahnSeries.SummableFamily.powers_of_not_orderTop_pos** 是 Mathlib 中的一个定理，位于命名空间
 `HahnSeries.SummableFamily`。
形式化陈述：powers_of_not_orderTop_pos {x : R⟦Γ⟧} (hx : ¬ 0 < x.orderTop) : powers x =
 .single 0 1
参数：hx : ¬ 0 < x.orderTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.ext`：ext {s t : SummableFamily Γ R α} (h : for
all a : α, s a = t a) : s = t
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `HahnSeries.SummableFamily.mk.congr_simp`：∀ {Γ : Type u_8} {R : Type u_9}
 [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {α : Type u_7}   (toFun toFu
n_1 : α → HahnSeries Γ R) (e_…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
· 使用定理 `HahnSeries.SummableFamily.single_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {ι : Type u_7}   [inst_2 : De
cidableEq ι] (i : ι) (x : Ha…
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
theorem powers_of_not_orderTop_pos {x : R⟦Γ⟧} (hx : ¬ 0 < x.orderTop) :
    powers x = .single 0 1 := by
  ext a
  obtain rfl | ha := eq_or_ne a 0 <;> simp [powers, *]

@[simp]
/-
**HahnSeries.SummableFamily.powers_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Su
mmableFamily`。
形式化陈述：powers_zero : powers (0 : R⟦Γ⟧) = .single 0 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.ext`：ext {s t : SummableFamily Γ R α} (h : for
all a : α, s a = t a) : s = t
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.powers_of_orderTop_pos`：powers_of_orderTop_pos
 {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (n : Nat) : powers x n = x ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
· 使用定理 `HahnSeries.SummableFamily.single_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {ι : Type u_7}   [inst_2 : De
cidableEq ι] (i : ι) (x : Ha…
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
theorem powers_zero : powers (0 : R⟦Γ⟧) = .single 0 1 := by
  ext n
  rw [powers_of_orderTop_pos (by simp)]
  obtain rfl | ha := eq_or_ne n 0 <;> simp [*]

variable {x : R⟦Γ⟧} (hx : 0 < x.orderTop)

include hx in
@[simp]
/-
**HahnSeries.SummableFamily.coe_powers** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries.Sum
mableFamily`。
形式化陈述：coe_powers : ⇑(powers x) = HPow.hPow x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_powers : ⇑(powers x) = HPow.hPow x := by
  ext1 n
  simp [hx]

include hx in
/-
**HahnSeries.SummableFamily.embDomain_succ_smul_powers** 是 Mathlib 中的一个定理，位于命名空间
 `HahnSeries.SummableFamily`。
形式化陈述：embDomain_succ_smul_powers : (x • powers x).embDomain ⟨Nat.succ, Nat.succ_
injective⟩ = powers x - ofFinsupp (Finsupp.single 0 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.ext`：ext {s t : SummableFamily Γ R α} (h : for
all a : α, s a = t a) : s = t
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
· 使用引理 `Nat.succ_injective`：succ_injective : Injective Nat.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.embDomain_of_notMem_range`：embDomain_of_notMem
_range (h : b ∉ Set.range f) : s.embDomain f b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.range_succ`：Set.range Nat.succ = {i | 0 < i}
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `HahnSeries.SummableFamily.coe_powers`：coe_powers : ⇑(powers x) = HPow.hP
ow x
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
（共 36 条，此处仅展示前 30 条）
-/
theorem embDomain_succ_smul_powers :
    (x • powers x).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      powers x - ofFinsupp (Finsupp.single 0 1) := by
  apply SummableFamily.ext
  rintro (_ | n)
  · simp [hx]
  · -- FIXME: smul_eq_mul introduces type confusion between HahnModule and HahnSeries.
    simp [embDomain_apply, of_symm_smul_of_eq_mul, powers_of_orderTop_pos hx, pow_succ',
      -smul_eq_mul]

include hx in
/-
**HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers** 是 Mathlib 中的一个定理，位于命名
空间 `HahnSeries.SummableFamily`。
形式化陈述：one_sub_self_mul_hsum_powers : (1 - x) * (powers x).hsum = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.SummableFamily.hsum_smul`：hsum_smul {x : R⟦Γ⟧} {s : SummableF
amily Γ R α} : (x • s).hsum = x * s.hsum
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HahnSeries.SummableFamily.hsum_sub`：hsum_sub {R : Type*} [Ring R] {s t :
 SummableFamily Γ R α} : (s - t).hsum = s.hsum - t.hsum
· 使用引理 `Nat.succ_injective`：succ_injective : Injective Nat.succ
· 使用定理 `HahnSeries.SummableFamily.hsum_embDomain`：hsum_embDomain : (s.embDomain 
f).hsum = s.hsum
· 使用定理 `HahnSeries.SummableFamily.embDomain_succ_smul_powers`：embDomain_succ_smu
l_powers : (x • powers x).embDomain ⟨Nat.succ, Nat.succ_injective⟩ = powers x - 
ofFinsupp (Finsupp.single 0 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.SummableFamily.hsum_ofFinsupp`：hsum_ofFinsupp {f : α ->₀ R⟦Γ⟧
} : (ofFinsupp f).hsum = f.sum fun _ => id
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers x).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (powers x), one_smul, hsum_sub, ←
    hsum_embDomain (x • powers x) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_powers hx]
  simp

end powers

end SummableFamily

section Inversion

section CommRing

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

/-
**HahnSeries.one_minus_single_neg_mul** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：one_minus_single_neg_mul {x y : R⟦Γ⟧} {r : R} (hr : r * x.leadingCoeff = 1
) (hxy : x = y + single x.order x.leadingCoeff) (oinv : Γ) (hxo : oinv + x.order
 = 0) : 1 - single oinv r * x = -(single oinv r * y)
参数：hr : r * x.leadingCoeff = 1；hxy : x = y + single x.order x.leadingCoeff；oinv 
: Γ；hxo : oinv + x.order = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `HahnSeries.single_mul_single`：single_mul_single {a b : Γ} {r s : R} : si
ngle a r * single b s = single (a + b) (r * s)
· 使用定理 `sub_add_eq_sub_sub_swap`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (
a b c : α), a - (b + c) = a - c - b
· 使用定理 `sub_eq_neg_self`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b =
 -b ↔ a = 0
· 使用定理 `sub_eq_zero_of_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a = b
 → a - b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.single_zero_one`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Zero
 Γ] [inst_1 : PartialOrder Γ] [inst_2 : Zero R] [inst_3 : One R],   (HahnSeries.
single 0) 1 = 1
-/
theorem one_minus_single_neg_mul {x y : R⟦Γ⟧} {r : R} (hr : r * x.leadingCoeff = 1)
    (hxy : x = y + single x.order x.leadingCoeff) (oinv : Γ) (hxo : oinv + x.order = 0) :
    1 - single oinv r * x = -(single oinv r * y) := by
  nth_rw 1 [hxy]
  rw [mul_add, single_mul_single, hr, hxo,
    sub_add_eq_sub_sub_swap, sub_eq_neg_self, sub_eq_zero_of_eq single_zero_one.symm]
/-
**HahnSeries.unit_aux** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：unit_aux (x : R⟦Γ⟧) {r : R} (hr : r * x.leadingCoeff = 1) (oinv : Γ) (hxo 
: oinv + x.order = 0) : 0 < (1 - single oinv r * x).orderTop
参数：x : R⟦Γ⟧；hr : r * x.leadingCoeff = 1；oinv : Γ；hxo : oinv + x.order = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `HahnSeries.single_mul_single`：single_mul_single {a b : Γ} {r s : R} : si
ngle a r * single b s = single (a + b) (r * s)
· 使用定理 `HahnSeries.single_zero_one`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Zero
 Γ] [inst_1 : PartialOrder Γ] [inst_2 : Zero R] [inst_3 : One R],   (HahnSeries.
single 0) 1 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `IsUnit.isRegular`：IsUnit.isRegular (ua : IsUnit a) : IsRegular a
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `HahnSeries.order_single_mul_of_isRegular`：order_single_mul_of_isRegular 
{g : Γ} {r : R} (hr : IsRegular r) {x : R⟦Γ⟧} (hx : x != 0) : (((single g) r) * 
x).order = g + x.order
· 使用定理 `pos_of_lt_add_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftReflectLT α] {a b : α}, a < a + b → 0 < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HahnSeries.order_lt_order_of_eq_add_single`：order_lt_order_of_eq_add_sin
gle {R} {Γ} [LinearOrder Γ] [Zero Γ] [AddCancelCommMonoid R] {x y : R⟦Γ⟧} (hxy :
 x = y + single x.order x.leadin…
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `HahnSeries.one_minus_single_neg_mul`：one_minus_single_neg_mul {x y : R⟦Γ
⟧} {r : R} (hr : r * x.leadingCoeff = 1) (hxy : x = y + single x.order x.leading
Coeff) (oinv : Γ) (hxo : …
· 使用定理 `HahnSeries.orderTop_neg`：orderTop_neg {x : R⟦Γ⟧} : (-x).orderTop = x.ord
erTop
· 使用定理 `HahnSeries.zero_lt_orderTop_of_order`：zero_lt_orderTop_of_order {x : R⟦Γ
⟧} (hx : 0 < x.order) : 0 < x.orderTop
-/
theorem unit_aux (x : R⟦Γ⟧) {r : R} (hr : r * x.leadingCoeff = 1)
    (oinv : Γ) (hxo : oinv + x.order = 0) :
    0 < (1 - single oinv r * x).orderTop := by
  let y := (x - single x.order x.leadingCoeff)
  by_cases hy : y = 0
  · have hrx : (single oinv) r * x = 1 := by
      rw [eq_of_sub_eq_zero hy, single_mul_single, hxo, hr, single_zero_one]
    simp only [hrx, sub_self, orderTop_zero, WithTop.top_pos]
  · have hr' : IsRegular r := IsUnit.isRegular <| .of_mul_eq_one x.leadingCoeff hr
    have hy' : 0 < (single oinv r * y).order := by
      rw [(order_single_mul_of_isRegular hr' hy)]
      refine pos_of_lt_add_right (a := x.order) ?_
      rw [← add_assoc, add_comm x.order, hxo, zero_add]
      exact order_lt_order_of_eq_add_single (sub_add_cancel x _).symm hy
    rw [one_minus_single_neg_mul hr (sub_add_cancel x _).symm _ hxo, orderTop_neg]
    exact zero_lt_orderTop_of_order hy'
/-
**HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder** 是 Mathlib 中的一个定理，位于命名空
间 `HahnSeries`。
形式化陈述：isUnit_of_isUnit_leadingCoeff_AddUnitOrder {x : R⟦Γ⟧} (hx : IsUnit x.leadi
ngCoeff) (hxo : IsAddUnit x.order) : IsUnit x
参数：hx : IsUnit x.leadingCoeff；hxo : IsAddUnit x.order。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers`：one_sub_self_mul
_hsum_powers : (1 - x) * (powers x).hsum = 1
· 使用定理 `HahnSeries.unit_aux`：unit_aux (x : R⟦Γ⟧) {r : R} (hr : r * x.leadingCoef
f = 1) (oinv : Γ) (hxo : oinv + x.order = 0) : 0 < (1 - single oinv r * x).order
Top
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.val_mk`：val_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a
· 使用定理 `AddUnits.neg_add`：∀ {α : Type u} [inst : AddMonoid α] (a : AddUnits α), 
↑(-a) + ↑a = 0
· 使用定理 `isUnit_of_mul_isUnit_right`：isUnit_of_mul_isUnit_right [Monoid M] [IsDed
ekindFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
theorem isUnit_of_isUnit_leadingCoeff_AddUnitOrder {x : R⟦Γ⟧} (hx : IsUnit x.leadingCoeff)
    (hxo : IsAddUnit x.order) : IsUnit x := by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu _ hxo.addUnit.neg_add)
  rw [sub_sub_cancel] at h'
  exact isUnit_of_mul_isUnit_right (.of_mul_eq_one _ h')
/-
**HahnSeries.isUnit_of_orderTop_pos** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：isUnit_of_orderTop_pos {x : R⟦Γ⟧} (h : 0 < (x - 1).orderTop) : IsUnit x
参数：h : 0 < (x - 1).orderTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `isUnit_of_subsingleton`：isUnit_of_subsingleton [Monoid M] [Subsingleton 
M] (a : M) : IsUnit a
· 使用定理 `HahnSeries.instSubsingleton`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Par
tialOrder Γ] [inst_1 : Zero R] [Subsingleton R],   Subsingleton (HahnSeries Γ R)
· 使用定理 `HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder`：isUnit_of_isUnit_
leadingCoeff_AddUnitOrder {x : R⟦Γ⟧} (hx : IsUnit x.leadingCoeff) (hxo : IsAddUn
it x.order) : IsUnit x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `HahnSeries.orderTop_self_sub_one_pos_iff`：orderTop_self_sub_one_pos_iff 
[LinearOrder Γ] [Zero Γ] [NonAssocRing R] [Nontrivial R] (x : R⟦Γ⟧) : 0 < (x - 1
).orderTop ↔ x.orderTop = 0 ∧ …
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `WithTop.coe_eq_zero`：∀ {α : Type u} [inst : Zero α] {a : α}, ↑a = 0 ↔ a 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.order_eq_orderTop_of_ne_zero`：order_eq_orderTop_of_ne_zero (h
x : x != 0) : order x = orderTop x
· 使用定理 `WithTop.top_ne_zero`：∀ {α : Type u} [inst : Zero α], ⊤ ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.orderTop_eq_top`：∀ {Γ : Type u_1} {R : Type u_3} [inst : Part
ialOrder Γ] [inst_1 : Zero R] {x : HahnSeries Γ R}, x.orderTop = ⊤ ↔ x = 0
· 使用定理 `isAddUnit_zero`：∀ {M : Type u_1} [inst : AddMonoid M], IsAddUnit 0
-/
theorem isUnit_of_orderTop_pos {x : R⟦Γ⟧} (h : 0 < (x - 1).orderTop) :
    IsUnit x := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton x
  · refine isUnit_of_isUnit_leadingCoeff_AddUnitOrder ?_ ?_
    · rw [(x.orderTop_self_sub_one_pos_iff.mp h).2]
      exact isUnit_one
    · have := (x.orderTop_self_sub_one_pos_iff.mp h).1
      rw [← order_eq_orderTop_of_ne_zero
        (fun h ↦ WithTop.top_ne_zero (orderTop_eq_top.mpr h ▸ this)), WithTop.coe_eq_zero] at this
      rw [this]
      exact isAddUnit_zero

/-- Make an element of `orderTopSubOnePos` -/
@[simps]
/-
**HahnSeries.toOrderTopSubOnePos** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：toOrderTopSubOnePos {x : R⟦Γ⟧} (h : 0 < (x - 1).orderTop) : orderTopSubOne
Pos Γ R where val
参数：h : 0 < (x - 1).orderTop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.isUnit_of_orderTop_pos`：isUnit_of_orderTop_pos {x : R⟦Γ⟧} (h 
: 0 < (x - 1).orderTop) : IsUnit x

--- 原说明 ---
Make an element of `orderTopSubOnePos`
-/
def toOrderTopSubOnePos {x : R⟦Γ⟧} (h : 0 < (x - 1).orderTop) :
    orderTopSubOnePos Γ R where
  val := ⟨x, (isUnit_of_orderTop_pos h).unit.inv, IsUnit.mul_val_inv (isUnit_of_orderTop_pos h),
    IsUnit.val_inv_mul (isUnit_of_orderTop_pos h)⟩
  property := h

end CommRing

section IsDomain

variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [CommRing R] [IsDomain R]

/-
**HahnSeries.isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：isUnit_iff {x : R⟦Γ⟧} : IsUnit x ↔ IsUnit (x.leadingCoeff)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.coeff_mul_order_add_order`：coeff_mul_order_add_order (x y : R
⟦Γ⟧) : (x * y).coeff (x.order + y.order) = x.leadingCoeff * y.leadingCoeff
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `HahnSeries.order_mul`：order_mul (hx : x != 0) (hy : y != 0) : (x * y).or
der = x.order + y.order
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `left_ne_zero_of_mul_eq_one`：left_ne_zero_of_mul_eq_one (h : a * b = 1) :
 a != 0
· 使用定理 `HahnSeries.instNontrivialOfNonempty`：∀ {Γ : Type u_1} {R : Type u_3} [in
st : PartialOrder Γ] [inst_1 : Zero R] [Nonempty Γ] [Nontrivial R],   Nontrivial
 (HahnSeries Γ R)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `right_ne_zero_of_mul_eq_one`：right_ne_zero_of_mul_eq_one (h : a * b = 1)
 : b != 0
· 使用定理 `HahnSeries.order_one`：order_one [MulZeroOneClass R] : order (1 : R⟦Γ⟧) =
 0
· 使用定理 `HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers`：one_sub_self_mul
_hsum_powers : (1 - x) * (powers x).hsum = 1
· 使用定理 `HahnSeries.unit_aux`：unit_aux (x : R⟦Γ⟧) {r : R} (hr : r * x.leadingCoef
f = 1) (oinv : Γ) (hxo : oinv + x.order = 0) : 0 < (1 - single oinv r * x).order
Top
· 使用定理 `Units.val_mk`：val_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `isUnit_of_mul_isUnit_right`：isUnit_of_mul_isUnit_right [Monoid M] [IsDed
ekindFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
theorem isUnit_iff {x : R⟦Γ⟧} : IsUnit x ↔ IsUnit (x.leadingCoeff) := by
  constructor
  · rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
    refine
      .of_mul_eq_one (i.leadingCoeff)
        ((coeff_mul_order_add_order u i).symm.trans ?_)
    rw [ui, coeff_one, if_pos]
    rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]
  · rintro ⟨⟨u, i, ui, iu⟩, hx⟩
    rw [Units.val_mk] at hx
    rw [hx] at iu
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu _ (neg_add_cancel x.order))
    rw [sub_sub_cancel] at h
    exact isUnit_of_mul_isUnit_right (.of_mul_eq_one _ h)

end IsDomain

section Field

variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]

@[simps -isSimp inv]
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DivInvMonoid R⟦Γ⟧ where
  inv x :=
    single (-x.order) (x.leadingCoeff)⁻¹ *
      (SummableFamily.powers <| 1 - single (-x.order) (x.leadingCoeff)⁻¹ * x).hsum

@[simp]
/-
**HahnSeries.inv_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：inv_single (a : Γ) (r : R) : (single a r)⁻¹ = single (-a) r⁻¹
参数：a : Γ；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `HahnSeries.order_zero`：order_zero : order (0 : R⟦Γ⟧) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `HahnSeries.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R⟦Γ⟧
) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `HahnSeries.SummableFamily.powers.congr_simp`：∀ {Γ : Type u_1} {R : Type 
u_3} [inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancel
AddMonoid Γ]   [inst_3 : CommRing…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.order_single`：order_single (h : r != 0) : (single a r).order 
= a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `HahnSeries.leadingCoeff_of_single`：leadingCoeff_of_single {a : Γ} {r : R
} : leadingCoeff (single a r) = r
· 使用定理 `HahnSeries.single_mul_single`：single_mul_single {a b : Γ} {r s : R} : si
ngle a r * single b s = single (a + b) (r * s)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `HahnSeries.SummableFamily.powers_zero`：powers_zero : powers (0 : R⟦Γ⟧) =
 .single 0 1
· 使用定理 `HahnSeries.SummableFamily.hsum_single`：hsum_single {ι} [DecidableEq ι] (
i : ι) (x : R⟦Γ⟧) : (single i x).hsum = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem inv_single (a : Γ) (r : R) : (single a r)⁻¹ = single (-a) r⁻¹ := by
  obtain rfl | hr := eq_or_ne r 0
  · simp [inv_def]
  · simp [inv_def, hr]

@[simp]
/-
**HahnSeries.single_div_single** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_div_single (a b : Γ) (r s : R) : single a r / single b s = single (
a - b) (r / s)
参数：a b : Γ；r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HahnSeries.inv_single`：inv_single (a : Γ) (r : R) : (single a r)⁻¹ = sin
gle (-a) r⁻¹
· 使用定理 `HahnSeries.single_mul_single`：single_mul_single {a b : Γ} {r s : R} : si
ngle a r * single b s = single (a + b) (r * s)
-/
theorem single_div_single (a b : Γ) (r s : R) :
    single a r / single b s = single (a - b) (r / s) := by
  rw [div_eq_mul_inv, sub_eq_add_neg, div_eq_mul_inv, inv_single, single_mul_single]
/-
**HahnSeries.instField** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
形式化陈述：instField : Field R⟦Γ⟧ where inv_zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instField : Field R⟦Γ⟧ where
  inv_zero := by simp [inv_def]
  mul_inv_cancel x x0 := by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr x0)) _ (neg_add_cancel x.order))
    rw [sub_sub_cancel] at h
    rw [inv_def, ← mul_assoc, mul_comm x, h]
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnqsmul_def q x := by ext; simp [← single_zero_nnratCast, NNRat.smul_def]
  qsmul_def q x := by ext; simp [← single_zero_ratCast, Rat.smul_def]
  nnratCast_def q := by
    simp [← single_zero_nnratCast, ← single_zero_natCast, NNRat.cast_def]
  ratCast_def q := by
    simp [← single_zero_ratCast, ← single_zero_intCast, ← single_zero_natCast, Rat.cast_def]
/-
**HahnSeries.** 是 Mathlib 中的一个示例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (instSMul : SMul NNRat R⟦Γ⟧) = NNRat.smulDivisionSemiring := rfl
/-
**HahnSeries.** 是 Mathlib 中的一个示例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (instSMul : SMul ℚ R⟦Γ⟧) = Rat.smulDivisionRing := rfl
/-
**HahnSeries.single_zero_ofScientific** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：single_zero_ofScientific (m e s) : single (0 : Γ) (OfScientific.ofScientif
ic m e s : R) = OfScientific.ofScientific m e s
参数：m e s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_ofScientific`：cast_ofScientific {K} [DivisionRing K] (m : Nat) 
(s : Bool) (e : Nat) : (OfScientific.ofScientific m s e : Rat) = (OfScientific.o
fScientific…
· 使用定理 `HahnSeries.single_zero_ratCast`：single_zero_ratCast [Zero R] [RatCast R]
 (q : Rat) : single (0 : Γ) (q : R) = q
-/
theorem single_zero_ofScientific (m e s) :
    single (0 : Γ) (OfScientific.ofScientific m e s : R) = OfScientific.ofScientific m e s := by
  simpa using single_zero_ratCast (Γ := Γ) (R := R) (OfScientific.ofScientific m e s)

end Field

end Inversion

end HahnSeries

