/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Embedding
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity

/-!
# Rank one valuations

We define rank one valuations.

## Main Definitions
* `RankOne` : A valuation has rank one if it is nontrivial and its image (defined as
  `MonoidWithZeroHom.valueGroup₀ v`) is contained in `ℝ≥0`. Note that this class includes the data
  of an inclusion morphism `MonoidWithZeroHom.valueGroup₀ v → ℝ≥0`.
* `RankOne.restrict_RankOne` is the `RankOne` instance for the restriction of a valuation to its
  image, as defined in

## Tags

valuation, rank one
-/

@[expose] public section

noncomputable section

open Function Multiplicative MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

open scoped NNReal

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

/-- A valuation has rank at most one if its image (defined as `MonoidWithZeroHom.valueGroup₀ v`)
is contained in `ℝ≥0`. Note that this class includes the data
of an inclusion morphism `MonoidWithZeroHom.valueGroup₀ v → ℝ≥0`. -/
/-
**Valuation.RankLeOne** 是 Mathlib 中的一个归纳类型，位于命名空间 `Valuation`。
形式化陈述：{R : Type u_1} →   {Γ₀ : Type u_2} → [inst : Ring R] → [inst_1 : LinearOrd
eredCommGroupWithZero Γ₀] → Valuation R Γ₀ → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valuation has rank at most one if its image (defined as `MonoidWithZeroHom.val
ueGroup₀ v`)
is contained in `ℝ≥0`. Note that this class includes the data
of an inclusion morphism `MonoidWithZeroHom.valueGroup₀ v → ℝ≥0`.
-/
class RankLeOne (v : Valuation R Γ₀) where
  /-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
  hom' (v) : ValueGroup₀ (.ofClass v) →*₀ ℝ≥0
  strictMono' : StrictMono hom'

/-- A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`.
  Note that this class includes the data of an inclusion morphism `Γ₀ → ℝ≥0`. -/
/-
**Valuation.RankOne** 是 Mathlib 中的一个归纳类型，位于命名空间 `Valuation`。
形式化陈述：{R : Type u_1} →   {Γ₀ : Type u_2} → [inst : Ring R] → [inst_1 : LinearOrd
eredCommGroupWithZero Γ₀] → Valuation R Γ₀ → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valuation has rank one if it is nontrivial and its image is contained in `ℝ≥0`
.
  Note that this class includes the data of an inclusion morphism `Γ₀ → ℝ≥0`.
-/
class RankOne (v : Valuation R Γ₀) extends RankLeOne v, Valuation.IsNontrivial v

open WithZero
/-
**Valuation.nonempty_rankOne_iff_mulArchimedean** 是 Mathlib 中的一个引理，位于命名空间 `Valua
tion`。
形式化陈述：nonempty_rankOne_iff_mulArchimedean {v : Valuation R Γ₀} [v.IsNontrivial] 
: Nonempty v.RankOne ↔ MulArchimedean (ValueGroup₀ (.ofClass v))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `MulArchimedean.comap`：MulArchimedean.comap [CommMonoid G] [LinearOrder G
] [CommMonoid M] [PartialOrder M] [MulArchimedean M] (f : G ->* M) (hf : StrictM
ono f) : M…
· 使用定理 `NNReal.instMulArchimedean`：MulArchimedean NNReal
· 使用定理 `Valuation.RankLeOne.strictMono'`：∀ {R : Type u_1} {Γ₀ : Type u_2} {inst 
: Ring R} {inst_1 : LinearOrderedCommGroupWithZero Γ₀} {v : Valuation R Γ₀}   [s
elf : v.RankLeOne], S…
· 使用定理 `Archimedean.exists_orderAddMonoidHom_real_injective`：exists_orderAddMono
idHom_real_injective : exists f : M ->+o Real, Function.Injective f
· 使用定理 `MonoidWithZeroHom.ValueGroup₀.instIsOrderedMonoid`：∀ {A : Type u_1} {B :
 Type u_2} [inst : MonoidWithZero A] [inst_1 : LinearOrderedCommGroupWithZero B]
 {f : A →*₀ B},   IsOrderedMonoid f.Val…
· 使用定理 `OrderAddMonoidHom.instAddMonoidHomClass`：∀ {α : Type u_2} {β : Type u_3}
 [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : AddZeroClass α]   [inst_3 :
 AddZeroClass β], AddMonoidHo…
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `OrderAddMonoidHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Pre
order α] [inst_1 : Preorder β] [inst_2 : AddZeroClass α]   [inst_3 : AddZeroClas
s β] (self : α →+…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Units.mk0.congr_simp`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] (a a_1
 : G₀) (e_a : a = a_1) (ha : a ≠ 0), Units.mk0 a ha = Units.mk0 a_1 ⋯
· 使用定理 `Units.mk0_one`：mk0_one (h
（共 39 条，此处仅展示前 30 条）
-/
lemma nonempty_rankOne_iff_mulArchimedean {v : Valuation R Γ₀} [v.IsNontrivial] :
    Nonempty v.RankOne ↔ MulArchimedean (ValueGroup₀ (.ofClass v)) := by
  constructor
  · intro h
    obtain hv := Nonempty.some h
    exact MulArchimedean.comap hv.hom'.toMonoidHom hv.strictMono'
  · intro _
    obtain ⟨f, hf⟩ :=
      Archimedean.exists_orderAddMonoidHom_real_injective (Additive (ValueGroup₀ (.ofClass v))ˣ)
    let e := AddMonoidHom.toMultiplicativeRight (α := (ValueGroup₀ (.ofClass v))ˣ) (β := ℝ) f
    have he : StrictMono e := by
      simp only [AddMonoidHom.coe_toMultiplicativeRight, AddMonoidHom.coe_coe, e]
      -- toAdd_strictMono is already in an applied form, do defeq abuse instead
      exact StrictMono.comp strictMono_id (f.monotone'.strictMono_of_injective hf)
    let rf : Multiplicative ℝ →* ℝ≥0ˣ := {
      toFun x := Units.mk0 (.mk ((2 : ℝ) ^ (log (M := ℝ) x)) (by positivity)) <| by
        simp only [ne_eq, NNReal.eq_iff, NNReal.coe_mk, NNReal.coe_zero]
        positivity
      map_one' := by ext; simp
      map_mul' _ _ := by ext; simp [Real.rpow_add]
      }
    have H : StrictMono (map' (rf.comp e)) := by
      refine map'_strictMono ?_
      intro a b h
      simpa [← Units.val_lt_val, ← NNReal.coe_lt_coe, rf] using he h
    exact ⟨{
      hom' := withZeroUnitsEquiv.toMonoidWithZeroHom.comp <| (map' (rf.comp e)).comp
        withZeroUnitsEquiv.symm.toMonoidWithZeroHom
      strictMono' := withZeroUnitsEquiv_strictMono.comp <| H.comp
        withZeroUnitsEquiv_symm_strictMono
    }⟩

namespace RankOne

variable (v : Valuation R Γ₀) [hv : RankOne v]

/-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
/-
**Valuation.RankOne.hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Valuation.RankOne`。
形式化陈述：hom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion morphism from `Γ₀` to `ℝ≥0`.
-/
abbrev hom := RankLeOne.hom' v
/-
**Valuation.RankOne.strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.RankOne`。
形式化陈述：strictMono : StrictMono (hom v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.RankLeOne.strictMono'`：∀ {R : Type u_1} {Γ₀ : Type u_2} {inst 
: Ring R} {inst_1 : LinearOrderedCommGroupWithZero Γ₀} {v : Valuation R Γ₀}   [s
elf : v.RankLeOne], S…
-/
lemma strictMono : StrictMono (hom v) := hv.strictMono'
/-
**Valuation.RankOne.nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.RankOne`。
形式化陈述：nontrivial : exists r : R, v r != 0 ∧ v r != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsNontrivial.exists_val_nontrivial`：∀ {R : Type u_3} {Γ₀ : Typ
e u_4} {inst : Ring R} {inst_1 : LinearOrderedCommMonoidWithZero Γ₀} {v : Valuat
ion R Γ₀}   [self : v.IsNontrivial…
· 使用定理 `Valuation.RankOne.toIsNontrivial`：∀ {R : Type u_1} {Γ₀ : Type u_2} {inst
 : Ring R} {inst_1 : LinearOrderedCommGroupWithZero Γ₀} {v : Valuation R Γ₀}   [
self : v.RankOne], v.I…
-/
lemma nontrivial : ∃ r : R, v r ≠ 0 ∧ v r ≠ 1 := IsNontrivial.exists_val_nontrivial

/-- If `v` is a rank one valuation and `x : Γ₀` has image `0` under `RankOne.hom v`, then
  `x = 0`. -/
/-
**Valuation.RankOne.zero_of_hom_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.RankOn
e`。
形式化陈述：zero_of_hom_zero {x : ValueGroup₀ (.ofClass v)} (hx : hom v x = 0) : x = 0
参数：.ofClass v；hx : hom v x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用引理 `Valuation.RankOne.strictMono`：strictMono : StrictMono (hom v)
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…

--- 原说明 ---
If `v` is a rank one valuation and `x : Γ₀` has image `0` under `RankOne.hom v`,
 then
  `x = 0`.
-/
theorem zero_of_hom_zero {x : ValueGroup₀ (.ofClass v)} (hx : hom v x = 0) : x = 0 := by
  refine (eq_of_le_of_not_lt (zero_le (a := x)) fun h_lt ↦ ?_).symm
  have hs := strictMono v h_lt
  rw [map_zero, hx] at hs
  exact hs.false

/-- If `v` is a rank one valuation, then `x : Γ₀` has image `0` under `RankOne.hom v` if and
  only if `x = 0`. -/
/-
**Valuation.RankOne.hom_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.RankOne
`。
形式化陈述：hom_eq_zero_iff {x : ValueGroup₀ (.ofClass v)} : hom v x = 0 ↔ x = 0
参数：.ofClass v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.RankOne.zero_of_hom_zero`：zero_of_hom_zero {x : ValueGroup₀ (.
ofClass v)} (hx : hom v x = 0) : x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…

--- 原说明 ---
If `v` is a rank one valuation, then `x : Γ₀` has image `0` under `RankOne.hom v
` if and
  only if `x = 0`.
-/
theorem hom_eq_zero_iff {x : ValueGroup₀ (.ofClass v)} : hom v x = 0 ↔ x = 0 :=
  ⟨fun h ↦ zero_of_hom_zero v h, fun h ↦ by rw [h, map_zero]⟩

/-- A nontrivial unit of `Γ₀`, given that there exists a rank one `v : Valuation R Γ₀`. -/
/-
**Valuation.RankOne.unit** 是 Mathlib 中的一个定义，位于命名空间 `Valuation.RankOne`。
形式化陈述：unit : Γ₀ˣ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.RankOne.nontrivial`：nontrivial : exists r : R, v r != 0 ∧ v r 
!= 1

--- 原说明 ---
A nontrivial unit of `Γ₀`, given that there exists a rank one `v : Valuation R Γ
₀`.
-/
def unit : Γ₀ˣ :=
  Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1

/-- A proof that `RankOne.unit v ≠ 1`. -/
/-
**Valuation.RankOne.unit_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.RankOne`。
形式化陈述：unit_ne_one : unit v != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Valuation.RankOne.nontrivial`：nontrivial : exists r : R, v r != 0 ∧ v r 
!= 1
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
A proof that `RankOne.unit v ≠ 1`.
-/
theorem unit_ne_one : unit v ≠ 1 := by
  rw [Ne, ← Units.val_inj, Units.val_one]
  exact ((nontrivial v).choose_spec).2
/-
**Valuation.RankOne.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation.RankOne`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNontrivial v where
  exists_val_nontrivial := RankOne.nontrivial v

section Restrict

/-
**Valuation.RankOne.isNontrivial_restrict** 是 Mathlib 中的一个实例，位于命名空间 `Valuation.R
ankOne`。
形式化陈述：isNontrivial_restrict : (v.restrict).IsNontrivial where exists_val_nontriv
ial
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.IsNontrivial.exists_val_nontrivial`：∀ {R : Type u_3} {Γ₀ : Typ
e u_4} {inst : Ring R} {inst_1 : LinearOrderedCommMonoidWithZero Γ₀} {v : Valuat
ion R Γ₀}   [self : v.IsNontrivial…
· 使用定理 `Valuation.RankOne.instIsNontrivial`：∀ {R : Type u_1} {Γ₀ : Type u_2} [in
st : Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)  
 [hv : v.RankOne], v.IsN…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
instance isNontrivial_restrict : (v.restrict).IsNontrivial where
  exists_val_nontrivial := by
    obtain ⟨x, ⟨hx0, hx1⟩⟩ := IsNontrivial.exists_val_nontrivial (v := v)
    exact ⟨x, by simp [hx0], by simpa⟩

variable (K : Type*) [DivisionRing K] (v : Valuation K Γ₀) [RankOne v]
/-
**Valuation.RankOne.restrict_RankOne** 是 Mathlib 中的一个实例，位于命名空间 `Valuation.RankOn
e`。
形式化陈述：restrict_RankOne : RankOne (v.restrict) where hom'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance restrict_RankOne : RankOne (v.restrict) where
  hom' := (RankOne.hom v).comp embedding
  strictMono' := (strictMono v).comp embedding_strictMono

@[simp]
/-
**Valuation.RankOne.restrict_RankOne_hom_eq** 是 Mathlib 中的一个引理，位于命名空间 `Valuation
.RankOne`。
形式化陈述：restrict_RankOne_hom_eq : RankOne.hom v.restrict = (RankOne.hom v).comp em
bedding
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
lemma restrict_RankOne_hom_eq :
  RankOne.hom v.restrict = (RankOne.hom v).comp embedding := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {K} in
/-
**Valuation.RankOne.exists_val_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.RankOne`。
形式化陈述：exists_val_lt {γ : Real>=0} (hγ : γ != 0) : exists x != 0, RankOne.hom v (
v.restrict x) < γ
参数：hγ : γ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `NNReal.exists_lt_of_strictMono`：NNReal.exists_lt_of_strictMono [h : Nont
rivial Γ₀ˣ] {f : Γ₀ ->*₀ Real>=0} (hf : StrictMono f) {r : Real>=0} (hr : 0 < r)
 : exists d : Γ₀ˣ, f…
· 使用定理 `WithZero.instNontrivialUnits`：∀ {α : Type u_1} [inst : Group α] [Nontriv
ial α], Nontrivial (WithZero α)ˣ
· 使用定理 `Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfClassOfIsNont
rivial`：∀ {R : Type u_3} [inst : Ring R] {Γ₀ : Type u_7} [inst_1 : LinearOrdered
CommGroupWithZero Γ₀] {v : Valuation R Γ₀}   [hv : v.IsNontrivial], …
· 使用引理 `Valuation.RankOne.strictMono`：strictMono : StrictMono (hom v)
· 使用定理 `MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective`：∀ {A : Type u_1} {B 
: Type u_2} [inst : GroupWithZero A] [inst_1 : GroupWithZero B] (f : A →*₀ B),  
 Function.Surjective ⇑(MonoidWithZeroHom…
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Valuation.zero_iff`：zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K
} : v x = 0 ↔ x = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`：embedding_restrict₀ (
a : A) : ValueGroup₀.embedding (restrict₀ f a) = f a
-/
theorem exists_val_lt {γ : ℝ≥0} (hγ : γ ≠ 0) : ∃ x ≠ 0, RankOne.hom v (v.restrict x) < γ := by
  have hγ_pos : 0 < γ := pos_iff_ne_zero.mpr hγ
  obtain ⟨x, h⟩ := NNReal.exists_lt_of_strictMono (RankOne.strictMono v.restrict) hγ_pos
  obtain ⟨k, hk⟩ := ValueGroup₀.restrict₀_surjective _ x.val
  refine ⟨k, ?_, ?_⟩
  · simp only [restrict₀_apply, MonoidWithZeroHom.coe_ofClass, restrict_def, map_eq_zero,
      dite_eq_left_iff, coe_ne_zero, imp_false, not_not] at hk
    by_contra h0
    rw [dif_pos (by rw [dif_pos ((zero_iff v).mpr h0)]), eq_comm] at hk
    simp at hk
  · convert! h
    simp only [restrict_RankOne_hom_eq, coe_comp, Function.comp_apply, ← hk]
    congr 1
    exact (embedding_restrict₀ k).symm

end Restrict

end RankOne

namespace RankLeOne

variable {K : Type*} [DivisionRing K] (v : Valuation K Γ₀) [RankLeOne v]

/-- If a valuation has rank at most one and is non trivial,
then it has rank one -/
@[instance_reducible]
/-
**Valuation.RankLeOne.rankOne_of_exists** 是 Mathlib 中的一个定义，位于命名空间 `Valuation.Ran
kLeOne`。
形式化陈述：rankOne_of_exists (H : exists x != 0, v x != 1) : RankOne v where exists_v
al_nontrivial
参数：H : exists x != 0, v x != 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a valuation has rank at most one and is non trivial,
then it has rank one
-/
def rankOne_of_exists (H : ∃ x ≠ 0, v x ≠ 1) : RankOne v where
  exists_val_nontrivial := by
    by_contra! H'
    obtain ⟨x, hx, hx'⟩ := H
    exact hx' (H' x ((ne_zero_iff v).mpr hx))

/-- If a valuation has rank at most one and is non trivial,
then it has rank one -/
@[instance_reducible]
/-
**Valuation.RankLeOne.rankOne_of_nontrivial** 是 Mathlib 中的一个定义，位于命名空间 `Valuation
.RankLeOne`。
形式化陈述：rankOne_of_nontrivial (H : Nontrivial (ValueGroup₀ (.ofClass v))ˣ) : RankO
ne v where exists_val_nontrivial
参数：H : Nontrivial (ValueGroup₀ (.ofClass v))ˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a valuation has rank at most one and is non trivial,
then it has rank one
-/
def rankOne_of_nontrivial (H : Nontrivial (ValueGroup₀ (.ofClass v))ˣ) : RankOne v where
  exists_val_nontrivial := by
    by_contra! H'
    rw [nontrivial_iff_exists_ne 1] at H
    obtain ⟨x, hx⟩ := H
    obtain ⟨k, hk⟩ := ValueGroup₀.restrict₀_surjective _ x.val
    have h0 : v k ≠ 0 := by
      apply_fun embedding at hk
      simp only [embedding_restrict₀, MonoidWithZeroHom.coe_ofClass] at hk
      simp [hk]
    have h1 : v k ≠ 1 := by
      apply_fun embedding at hk
      simp only [embedding_restrict₀, MonoidWithZeroHom.coe_ofClass] at hk
      apply_fun Units.val at hx using
          Units.val_injective (α := (MonoidWithZeroHom.ofClass v).ValueGroup₀)
      intro h
      apply_fun embedding at hx using embedding_injective (f := .ofClass v)
      simp [← hk, h] at hx
    exact h1 (H' k h0)
/-
**Valuation.RankLeOne.exists_val_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.RankLeO
ne`。
形式化陈述：exists_val_lt {K : Type*} [DivisionRing K] (v : Valuation K Γ₀) [RankLeOne
 v] : Subsingleton ((ValueGroup₀ (.ofClass v))ˣ) ∨ forall {γ : Real>=0} (_ : γ !
= 0), exists (x : K), x != 0 ∧ (RankLeOne.hom' v) (v.restrict x) < γ
参数：v : Valuation K Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Valuation.RankOne.exists_val_lt`：exists_val_lt {γ : Real>=0} (hγ : γ != 
0) : exists x != 0, RankOne.hom v (v.restrict x) < γ
-/
theorem exists_val_lt {K : Type*} [DivisionRing K] (v : Valuation K Γ₀) [RankLeOne v] :
    Subsingleton ((ValueGroup₀ (.ofClass v))ˣ) ∨
      ∀ {γ : ℝ≥0} (_ : γ ≠ 0), ∃ (x : K), x ≠ 0 ∧ (RankLeOne.hom' v) (v.restrict x) < γ := by
  simp only [ne_eq, or_iff_not_imp_left, not_subsingleton_iff_nontrivial]
  exact fun H ↦ (rankOne_of_nontrivial v H).exists_val_lt

end RankLeOne

end Valuation

section ValuativeRel

open ValuativeRel

variable {R : Type*} [Ring R] [ValuativeRel R]

/-- A valuative relation has a rank one valuation when it is both nontrivial
and the rank is at most one. -/
@[instance_reducible]
/-
**Valuation.RankOne.ofRankLeOneStruct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Valuation.RankOne.ofRankLeOneStruct [ValuativeRel.IsNontrivial R] (e : Ran
kLeOneStruct R) : Valuation.RankOne (valuation R) where hom'
参数：e : RankLeOneStruct R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valuative relation has a rank one valuation when it is both nontrivial
and the rank is at most one.
-/
def Valuation.RankOne.ofRankLeOneStruct [ValuativeRel.IsNontrivial R] (e : RankLeOneStruct R) :
    Valuation.RankOne (valuation R) where
  hom' := e.emb.comp embedding
  strictMono' := e.strictMono.comp embedding_strictMono
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsNontrivial R] [IsRankLeOne R] :
    Valuation.RankOne (valuation R) :=
  Valuation.RankOne.ofRankLeOneStruct IsRankLeOne.nonempty.some

/-- Convert between the rank one statement on valuative relation's induced valuation. -/
/-
**Valuation.RankOne.rankLeOneStruct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Valuation.RankOne.rankLeOneStruct (e : Valuation.RankOne (valuation R)) : 
RankLeOneStruct R where emb
参数：e : Valuation.RankOne (valuation R)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.instCompatibleValueGroupWithZeroValuation`：∀ {R : Type u_2}
 [inst : Ring R] [inst_1 : ValuativeRel R], (ValuativeRel.valuation R).Compatibl
e

--- 原说明 ---
Convert between the rank one statement on valuative relation's induced valuation
.
-/
def Valuation.RankOne.rankLeOneStruct (e : Valuation.RankOne (valuation R)) :
    RankLeOneStruct R where
  emb := e.hom.comp (ValuativeRel.ValueGroupWithZero.embed (v := valuation R))
  strictMono := e.strictMono.comp (ValueGroupWithZero.embed_strictMono (valuation R))
/-
**ValuativeRel.isRankLeOne_of_rankOne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ValuativeRel.isRankLeOne_of_rankOne [h : (valuation R).RankOne] : IsRankLe
One R
参数：valuation R。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ValuativeRel.isRankLeOne_of_rankOne [h : (valuation R).RankOne] :
    IsRankLeOne R := ⟨⟨h.rankLeOneStruct⟩⟩
/-
**ValuativeRel.isNontrivial_of_rankOne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ValuativeRel.isNontrivial_of_rankOne [h : (valuation R).RankOne] : Valuati
veRel.IsNontrivial R
参数：valuation R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ValuativeRel.isNontrivial_iff_isNontrivial`：isNontrivial_iff_isNontrivia
l {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) [v.Comp
atible] : IsNontrivial R ↔ v.IsN…
· 使用定理 `ValuativeRel.instCompatibleValueGroupWithZeroValuation`：∀ {R : Type u_2}
 [inst : Ring R] [inst_1 : ValuativeRel R], (ValuativeRel.valuation R).Compatibl
e
· 使用定理 `Valuation.RankOne.toIsNontrivial`：∀ {R : Type u_1} {Γ₀ : Type u_2} {inst
 : Ring R} {inst_1 : LinearOrderedCommGroupWithZero Γ₀} {v : Valuation R Γ₀}   [
self : v.RankOne], v.I…
-/
lemma ValuativeRel.isNontrivial_of_rankOne [h : (valuation R).RankOne] :
    ValuativeRel.IsNontrivial R :=
  (isNontrivial_iff_isNontrivial _).mpr h.toIsNontrivial

open WithZero
/-
**ValuativeRel.isRankLeOne_iff_mulArchimedean** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ValuativeRel.isRankLeOne_iff_mulArchimedean : IsRankLeOne R ↔ MulArchimede
an (ValueGroupWithZero R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulArchimedean.comap`：MulArchimedean.comap [CommMonoid G] [LinearOrder G
] [CommMonoid M] [PartialOrder M] [MulArchimedean M] (f : G ->* M) (hf : StrictM
ono f) : M…
· 使用定理 `NNReal.instMulArchimedean`：MulArchimedean NNReal
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`：embedding_strictMono
 : StrictMono (embedding (f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.nonempty_rankOne_iff_mulArchimedean`：nonempty_rankOne_iff_mulA
rchimedean {v : Valuation R Γ₀} [v.IsNontrivial] : Nonempty v.RankOne ↔ MulArchi
medean (ValueGroup₀ (.ofClass v))
· 使用引理 `ValuativeRel.isNontrivial_iff_isNontrivial`：isNontrivial_iff_isNontrivia
l {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) [v.Comp
atible] : IsNontrivial R ↔ v.IsN…
· 使用定理 `ValuativeRel.instCompatibleValueGroupWithZeroValuation`：∀ {R : Type u_2}
 [inst : Ring R] [inst_1 : ValuativeRel R], (ValuativeRel.valuation R).Compatibl
e
· 使用引理 `ValuativeRel.isRankLeOne_of_rankOne`：ValuativeRel.isRankLeOne_of_rankOne
 [h : (valuation R).RankOne] : IsRankLeOne R
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `MonoidWithZeroHom.one_apply_zero`：one_apply_zero {M₀ N₀ : Type*} [MulZer
oOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 0] [Nontrivi
al M₀] [NoZeroDivisors…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a → 
c < b → c < a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
-/
lemma ValuativeRel.isRankLeOne_iff_mulArchimedean :
    IsRankLeOne R ↔ MulArchimedean (ValueGroupWithZero R) := by
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    exact .comap f.toMonoidHom hf
  · intro h
    by_cases H : IsNontrivial R
    · rw [isNontrivial_iff_isNontrivial (valuation R)] at H
      have h' : MulArchimedean (ValueGroup₀ (.ofClass (valuation R))) :=
        MulArchimedean.comap embedding.toMonoidHom embedding_strictMono
      rw [← (valuation R).nonempty_rankOne_iff_mulArchimedean] at h'
      obtain ⟨f⟩ := h'
      exact isRankLeOne_of_rankOne
    · refine ⟨⟨{ emb := 1, strictMono := ?_ }⟩⟩
      intro a b
      contrapose! H
      obtain ⟨H, H'⟩ := H
      rcases eq_or_ne a 0 with rfl | ha
      · simp_all
      rcases eq_or_ne a 1 with rfl | ha'
      · exact ⟨⟨b, (H.trans' zero_lt_one).ne', H.ne'⟩⟩
      · exact ⟨⟨a, ha, ha'⟩⟩
/-
**ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean [MulArchimedean Γ₀] 
(v : Valuation R Γ₀) [v.Compatible] : ValuativeRel.IsRankLeOne R
参数：v : Valuation R Γ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ValuativeRel.isRankLeOne_iff_mulArchimedean`：ValuativeRel.isRankLeOne_if
f_mulArchimedean : IsRankLeOne R ↔ MulArchimedean (ValueGroupWithZero R)
· 使用引理 `MulArchimedean.comap`：MulArchimedean.comap [CommMonoid G] [LinearOrder G
] [CommMonoid M] [PartialOrder M] [MulArchimedean M] (f : G ->* M) (hf : StrictM
ono f) : M…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`：embedding_strictMono
 : StrictMono (embedding (f
· 使用引理 `ValuativeRel.ValueGroupWithZero.embed_strictMono`：embed_strictMono [v.Co
mpatible] : StrictMono (embed v)
-/
lemma ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean [MulArchimedean Γ₀]
    (v : Valuation R Γ₀) [v.Compatible] :
    ValuativeRel.IsRankLeOne R := by
  rw [isRankLeOne_iff_mulArchimedean]
  exact MulArchimedean.comap (embedding.toMonoidHom.comp (ValueGroupWithZero.embed v).toMonoidHom)
    (embedding_strictMono.comp (ValueGroupWithZero.embed_strictMono v))

end ValuativeRel

