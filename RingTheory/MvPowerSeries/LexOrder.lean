/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Data.Finsupp.WellFounded

/-! # LexOrder of multivariate power series

Given an ordering of `σ` such that `WellFoundedGT σ`,
the lexicographic order on `σ →₀ ℕ` is a well ordering,
which can be used to define a natural valuation `lexOrder` on the ring `MvPowerSeries σ R`:
the smallest exponent in the support.

-/

@[expose] public section

namespace MvPowerSeries

variable {σ R : Type*}
variable [Semiring R]

section LexOrder

open Finsupp
variable [LinearOrder σ] [WellFoundedGT σ]

/-- The lex order on multivariate power series. -/
/-
**MvPowerSeries.lexOrder** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：lexOrder (φ : MvPowerSeries σ R) : (WithTop (Lex (σ ->₀ Nat)))
参数：φ : MvPowerSeries σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lex order on multivariate power series.
-/
noncomputable def lexOrder (φ : MvPowerSeries σ R) : (WithTop (Lex (σ →₀ ℕ))) := by
  classical
  exact if h : φ = 0 then ⊤ else by
    have ne : Set.Nonempty (toLex '' φ.support) := (Function.support_nonempty_iff.mpr h).image _
    apply WithTop.some
    apply WellFounded.min _ (toLex '' φ.support) ne
    · exact Finsupp.instLTLex.lt
    · exact wellFounded_lt

set_option backward.isDefEq.respectTransparency false in
/-
**MvPowerSeries.lexOrder_def_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries
`。
形式化陈述：lexOrder_def_of_ne_zero {φ : MvPowerSeries σ R} (hφ : φ != 0) : exists (ne
 : Set.Nonempty (toLex '' φ.support)), lexOrder φ = WithTop.some ((@wellFounded_
lt (Lex (σ ->₀ Nat)) (instLTLex) (Lex.wellFoundedLT)).min (toLex '' φ.support) n
e)
参数：hφ : φ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.support_nonempty_iff`：∀ {ι : Type u_1} {M : Type u_3} [inst : Z
ero M] {f : ι → M}, (Function.support f).Nonempty ↔ f ≠ 0
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `Finsupp.Lex.wellFoundedLT`：∀ {α : Type u_3} {N : Type u_4} [inst : LT α]
 [Std.Trichotomous fun x1 x2 => x1 < x2] [hα : WellFoundedGT α]   [inst_2 : AddM
onoid N] [inst_…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lexOrder_def_of_ne_zero {φ : MvPowerSeries σ R} (hφ : φ ≠ 0) :
    ∃ (ne : Set.Nonempty (toLex '' φ.support)),
      lexOrder φ = WithTop.some ((@wellFounded_lt (Lex (σ →₀ ℕ))
        (instLTLex) (Lex.wellFoundedLT)).min (toLex '' φ.support) ne) := by
  suffices ne : Set.Nonempty (toLex '' φ.support) by
    use ne
    unfold lexOrder
    simp only [dif_neg hφ]
  exact (Function.support_nonempty_iff.mpr hφ).image _

@[simp]
/-
**MvPowerSeries.lexOrder_eq_top_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSe
ries`。
形式化陈述：lexOrder_eq_top_iff_eq_zero (φ : MvPowerSeries σ R) : lexOrder φ = ⊤ ↔ φ =
 0
参数：φ : MvPowerSeries σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem lexOrder_eq_top_iff_eq_zero (φ : MvPowerSeries σ R) :
    lexOrder φ = ⊤ ↔ φ = 0 := by
  unfold lexOrder
  split_ifs with h
  · simp only [h]
  · simp only [h, WithTop.coe_ne_top]
/-
**MvPowerSeries.lexOrder_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] [inst_1 : LinearOrder 
σ] [inst_2 : WellFoundedGT σ],   MvPowerSeries.lexOrder 0 = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
@[simp] theorem lexOrder_zero : lexOrder (0 : MvPowerSeries σ R) = ⊤ := by
  unfold lexOrder
  rw [dif_pos rfl]
/-
**MvPowerSeries.exists_finsupp_eq_lexOrder_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 
`MvPowerSeries`。
形式化陈述：exists_finsupp_eq_lexOrder_of_ne_zero {φ : MvPowerSeries σ R} (hφ : φ != 0
) : exists (d : σ ->₀ Nat), lexOrder φ = toLex d
参数：hφ : φ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_finsupp_eq_lexOrder_of_ne_zero {φ : MvPowerSeries σ R} (hφ : φ ≠ 0) :
    ∃ (d : σ →₀ ℕ), lexOrder φ = toLex d := by
  simp only [ne_eq, ← lexOrder_eq_top_iff_eq_zero, WithTop.ne_top_iff_exists] at hφ
  obtain ⟨p, hp⟩ := hφ
  exact ⟨ofLex p, by simp only [toLex_ofLex, hp]⟩
/-
**MvPowerSeries.coeff_ne_zero_of_lexOrder** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeri
es`。
形式化陈述：coeff_ne_zero_of_lexOrder {φ : MvPowerSeries σ R} {d : σ ->₀ Nat} (h : toL
ex d = lexOrder φ) : coeff d φ != 0
参数：h : toLex d = lexOrder φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `Finsupp.Lex.wellFoundedLT`：∀ {α : Type u_3} {N : Type u_4} [inst : LT α]
 [Std.Trichotomous fun x1 x2 => x1 < x2] [hα : WellFoundedGT α]   [inst_2 : AddM
onoid N] [inst_…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `MvPowerSeries.lexOrder_def_of_ne_zero`：lexOrder_def_of_ne_zero {φ : MvPo
werSeries σ R} (hφ : φ != 0) : exists (ne : Set.Nonempty (toLex '' φ.support)), 
lexOrder φ = WithTop.some (…
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
-/
theorem coeff_ne_zero_of_lexOrder {φ : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (h : toLex d = lexOrder φ) : coeff d φ ≠ 0 := by
  have hφ : φ ≠ 0 := by
    simp only [ne_eq, ← lexOrder_eq_top_iff_eq_zero, ← h, WithTop.coe_ne_top, not_false_eq_true]
  have hφ' := lexOrder_def_of_ne_zero hφ
  rcases hφ' with ⟨ne, hφ'⟩
  simp only [← h, WithTop.coe_eq_coe] at hφ'
  suffices toLex d ∈ toLex '' φ.support by
    simp only [Set.mem_image_equiv, toLex_symm_eq, ofLex_toLex] at this
    apply this
  rw [hφ']
  apply WellFounded.min_mem
/-
**MvPowerSeries.coeff_eq_zero_of_lt_lexOrder** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerS
eries`。
形式化陈述：coeff_eq_zero_of_lt_lexOrder {φ : MvPowerSeries σ R} {d : σ ->₀ Nat} (h : 
toLex d < lexOrder φ) : coeff d φ = 0
参数：h : toLex d < lexOrder φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `Finsupp.Lex.wellFoundedLT`：∀ {α : Type u_3} {N : Type u_4} [inst : LT α]
 [Std.Trichotomous fun x1 x2 => x1 < x2] [hα : WellFoundedGT α]   [inst_2 : AddM
onoid N] [inst_…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `MvPowerSeries.lexOrder_def_of_ne_zero`：lexOrder_def_of_ne_zero {φ : MvPo
werSeries σ R} (hφ : φ != 0) : exists (ne : Set.Nonempty (toLex '' φ.support)), 
lexOrder φ = WithTop.some (…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
-/
theorem coeff_eq_zero_of_lt_lexOrder {φ : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (h : toLex d < lexOrder φ) : coeff d φ = 0 := by
  by_cases hφ : φ = 0
  · simp only [hφ, map_zero]
  · rcases lexOrder_def_of_ne_zero hφ with ⟨ne, hφ'⟩
    rw [hφ', WithTop.coe_lt_coe] at h
    by_contra h'
    exact WellFounded.not_lt_min _ (toLex '' φ.support) (Set.mem_image_equiv.mpr h') h
/-
**MvPowerSeries.lexOrder_le_of_coeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerS
eries`。
形式化陈述：lexOrder_le_of_coeff_ne_zero {φ : MvPowerSeries σ R} {d : σ ->₀ Nat} (h : 
coeff d φ != 0) : lexOrder φ <= toLex d
参数：h : coeff d φ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_lexOrder`：coeff_eq_zero_of_lt_lexOrder
 {φ : MvPowerSeries σ R} {d : σ ->₀ Nat} (h : toLex d < lexOrder φ) : coeff d φ 
= 0
-/
theorem lexOrder_le_of_coeff_ne_zero {φ : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (h : coeff d φ ≠ 0) : lexOrder φ ≤ toLex d := by
  rw [← not_lt]
  intro h'
  exact h (coeff_eq_zero_of_lt_lexOrder h')
/-
**MvPowerSeries.le_lexOrder_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_lexOrder_iff {φ : MvPowerSeries σ R} {w : WithTop (Lex (σ ->₀ Nat))} : 
w <= lexOrder φ ↔ (forall (d : σ ->₀ Nat) (_ : toLex d < w), coeff d φ = 0)
参数：Lex (σ ->₀ Nat)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_lexOrder`：coeff_eq_zero_of_lt_lexOrder
 {φ : MvPowerSeries σ R} {d : σ ->₀ Nat} (h : toLex d < lexOrder φ) : coeff d φ 
= 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MvPowerSeries.lexOrder_eq_top_iff_eq_zero`：lexOrder_eq_top_iff_eq_zero (
φ : MvPowerSeries σ R) : lexOrder φ = ⊤ ↔ φ = 0
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `MvPowerSeries.exists_finsupp_eq_lexOrder_of_ne_zero`：exists_finsupp_eq_l
exOrder_of_ne_zero {φ : MvPowerSeries σ R} (hφ : φ != 0) : exists (d : σ ->₀ Nat
), lexOrder φ = toLex d
· 使用定理 `MvPowerSeries.coeff_ne_zero_of_lexOrder`：coeff_ne_zero_of_lexOrder {φ : 
MvPowerSeries σ R} {d : σ ->₀ Nat} (h : toLex d = lexOrder φ) : coeff d φ != 0
-/
theorem le_lexOrder_iff {φ : MvPowerSeries σ R} {w : WithTop (Lex (σ →₀ ℕ))} :
    w ≤ lexOrder φ ↔ (∀ (d : σ →₀ ℕ) (_ : toLex d < w), coeff d φ = 0) := by
  constructor
  · intro h d hd
    apply coeff_eq_zero_of_lt_lexOrder
    exact lt_of_lt_of_le hd h
  · intro h
    rw [← not_lt]
    intro h'
    have hφ : φ ≠ 0 := by
      rw [ne_eq, ← lexOrder_eq_top_iff_eq_zero]
      exact ne_top_of_lt h'
    obtain ⟨d, hd⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hφ
    refine coeff_ne_zero_of_lexOrder hd.symm (h d ?_)
    rwa [← hd]
/-
**MvPowerSeries.min_lexOrder_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：min_lexOrder_le {φ ψ : MvPowerSeries σ R} : min (lexOrder φ) (lexOrder ψ) 
<= lexOrder (φ + ψ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.le_lexOrder_iff`：le_lexOrder_iff {φ : MvPowerSeries σ R} {
w : WithTop (Lex (σ ->₀ Nat))} : w <= lexOrder φ ↔ (forall (d : σ ->₀ Nat) (_ : 
toLex d < w), coeff…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_lexOrder`：coeff_eq_zero_of_lt_lexOrder
 {φ : MvPowerSeries σ R} {d : σ ->₀ Nat} (h : toLex d < lexOrder φ) : coeff d φ 
= 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem min_lexOrder_le {φ ψ : MvPowerSeries σ R} :
    min (lexOrder φ) (lexOrder ψ) ≤ lexOrder (φ + ψ) := by
  rw [le_lexOrder_iff]
  intro d hd
  simp only [lt_min_iff] at hd
  rw [map_add, coeff_eq_zero_of_lt_lexOrder hd.1, coeff_eq_zero_of_lt_lexOrder hd.2, add_zero]
/-
**MvPowerSeries.coeff_mul_of_add_lexOrder** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeri
es`。
形式化陈述：coeff_mul_of_add_lexOrder {φ ψ : MvPowerSeries σ R} {p q : σ ->₀ Nat} (hp 
: lexOrder φ = toLex p) (hq : lexOrder ψ = toLex q) : coeff (p + q) (φ * ψ) = co
eff p φ * coeff q ψ
参数：hp : lexOrder φ = toLex p；hq : lexOrder ψ = toLex q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `trichotomy_of_add_eq_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Line
arOrder α] {a b c d : α} [AddLeftStrictMono α] [AddRightStrictMono α],   a + b =
 c + d → a = c…
· 使用定理 `Finsupp.Lex.addLeftStrictMono`：∀ {α : Type u_1} {N : Type u_2} [inst : L
inearOrder α] [inst_1 : AddMonoid N] [inst_2 : LinearOrder N]   [AddLeftStrictMo
no N], AddLeftStric…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finsupp.Lex.addRightStrictMono`：∀ {α : Type u_1} {N : Type u_2} [inst : 
LinearOrder α] [inst_1 : AddMonoid N] [inst_2 : LinearOrder N]   [AddRightStrict
Mono N], AddRightStr…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_lexOrder`：coeff_eq_zero_of_lt_lexOrder
 {φ : MvPowerSeries σ R} {d : σ ->₀ Nat} (h : toLex d < lexOrder φ) : coeff d φ 
= 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem coeff_mul_of_add_lexOrder {φ ψ : MvPowerSeries σ R}
    {p q : σ →₀ ℕ} (hp : lexOrder φ = toLex p) (hq : lexOrder ψ = toLex q) :
    coeff (p + q) (φ * ψ) = coeff p φ * coeff q ψ := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem ⟨p, q⟩ (by simp)]
  rintro ⟨u, v⟩ h h'
  simp only [Finset.mem_antidiagonal] at h
  rcases trichotomy_of_add_eq_add (congrArg toLex h) with h'' | h'' | h''
  · exact False.elim (h' (by simp [h''.1, h''.2]))
  · rw [coeff_eq_zero_of_lt_lexOrder (d := u), zero_mul]
    rw [hp]
    norm_cast
  · rw [coeff_eq_zero_of_lt_lexOrder (d := v), mul_zero]
    rw [hq]
    norm_cast
/-
**MvPowerSeries.le_lexOrder_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_lexOrder_mul (φ ψ : MvPowerSeries σ R) : lexOrder φ + lexOrder ψ <= lex
Order (φ * ψ)
参数：φ ψ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.le_lexOrder_iff`：le_lexOrder_iff {φ : MvPowerSeries σ R} {
w : WithTop (Lex (σ ->₀ Nat))} : w <= lexOrder φ ↔ (forall (d : σ ->₀ Nat) (_ : 
toLex d < w), coeff…
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Finsupp.Lex.addLeftMono`：∀ {α : Type u_1} {N : Type u_2} [inst : LinearO
rder α] [inst_1 : AddMonoid N] [inst_2 : LinearOrder N]   [AddLeftStrictMono N],
 AddLeftMono …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finsupp.Lex.addRightMono`：∀ {α : Type u_1} {N : Type u_2} [inst : Linear
Order α] [inst_1 : AddMonoid N] [inst_2 : LinearOrder N]   [AddRightStrictMono N
], AddRightMon…
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
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_lexOrder`：coeff_eq_zero_of_lt_lexOrder
 {φ : MvPowerSeries σ R} {d : σ ->₀ Nat} (h : toLex d < lexOrder φ) : coeff d φ 
= 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem le_lexOrder_mul (φ ψ : MvPowerSeries σ R) :
    lexOrder φ + lexOrder ψ ≤ lexOrder (φ * ψ) := by
  rw [le_lexOrder_iff]
  intro d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨u, v⟩ h
  simp only [Finset.mem_antidiagonal] at h
  simp only
  suffices toLex u < lexOrder φ ∨ toLex v < lexOrder ψ by
    rcases this with (hu | hv)
    · rw [coeff_eq_zero_of_lt_lexOrder hu, zero_mul]
    · rw [coeff_eq_zero_of_lt_lexOrder hv, mul_zero]
  rw [or_iff_not_imp_left, not_lt, ← not_le]
  intro hu hv
  rw [← not_le] at hd
  apply hd
  simp only [← h, toLex_add, WithTop.coe_add, add_le_add hu hv]

alias lexOrder_mul_ge := le_lexOrder_mul
/-
**MvPowerSeries.lexOrder_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：lexOrder_mul [NoZeroDivisors R] (φ ψ : MvPowerSeries σ R) : lexOrder (φ * 
ψ) = lexOrder φ + lexOrder ψ
参数：φ ψ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.lexOrder.congr_simp`：∀ {σ : Type u_1} {R : Type u_2} [inst
 : Semiring R] [inst_1 : LinearOrder σ] [inst_2 : WellFoundedGT σ]   (φ φ_1 : Mv
PowerSeries σ R), φ = φ…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MvPowerSeries.lexOrder_zero`：∀ {σ : Type u_1} {R : Type u_2} [inst : Sem
iring R] [inst_1 : LinearOrder σ] [inst_2 : WellFoundedGT σ],   MvPowerSeries.le
xOrder 0 = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `MvPowerSeries.exists_finsupp_eq_lexOrder_of_ne_zero`：exists_finsupp_eq_l
exOrder_of_ne_zero {φ : MvPowerSeries σ R} (hφ : φ != 0) : exists (d : σ ->₀ Nat
), lexOrder φ = toLex d
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MvPowerSeries.lexOrder_le_of_coeff_ne_zero`：lexOrder_le_of_coeff_ne_zero
 {φ : MvPowerSeries σ R} {d : σ ->₀ Nat} (h : coeff d φ != 0) : lexOrder φ <= to
Lex d
· 使用定理 `MvPowerSeries.coeff_mul_of_add_lexOrder`：coeff_mul_of_add_lexOrder {φ ψ 
: MvPowerSeries σ R} {p q : σ ->₀ Nat} (hp : lexOrder φ = toLex p) (hq : lexOrde
r ψ = toLex q) : coeff (p + q…
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `MvPowerSeries.coeff_ne_zero_of_lexOrder`：coeff_ne_zero_of_lexOrder {φ : 
MvPowerSeries σ R} {d : σ ->₀ Nat} (h : toLex d = lexOrder φ) : coeff d φ != 0
· 使用定理 `MvPowerSeries.lexOrder_mul_ge`：∀ {σ : Type u_1} {R : Type u_2} [inst : S
emiring R] [inst_1 : LinearOrder σ] [inst_2 : WellFoundedGT σ]   (φ ψ : MvPowerS
eries σ R), φ.lexOr…
-/
theorem lexOrder_mul [NoZeroDivisors R] (φ ψ : MvPowerSeries σ R) :
    lexOrder (φ * ψ) = lexOrder φ + lexOrder ψ := by
  obtain rfl | hφ := eq_or_ne φ 0
  · simp
  obtain rfl | hψ := eq_or_ne ψ 0
  · simp
  rcases exists_finsupp_eq_lexOrder_of_ne_zero hφ with ⟨p, hp⟩
  rcases exists_finsupp_eq_lexOrder_of_ne_zero hψ with ⟨q, hq⟩
  apply le_antisymm _ (lexOrder_mul_ge φ ψ)
  rw [hp, hq]
  apply lexOrder_le_of_coeff_ne_zero (d := p + q)
  rw [coeff_mul_of_add_lexOrder hp hq, mul_ne_zero_iff]
  exact ⟨coeff_ne_zero_of_lexOrder hp.symm, coeff_ne_zero_of_lexOrder hq.symm⟩

end LexOrder

end MvPowerSeries

