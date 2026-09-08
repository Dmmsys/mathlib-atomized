/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Dirichlet theorem on the group of units of a number field

This file is devoted to the proof of Dirichlet unit theorem that states that the group of
units `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number field `K` modulo its torsion
subgroup is a free `ℤ`-module of rank `card (InfinitePlace K) - 1`.

## Main definitions

* `NumberField.Units.rank`: the unit rank of the number field `K`.

* `NumberField.Units.fundSystem`: a fundamental system of units of `K`.

* `NumberField.Units.basisModTorsion`: a `ℤ`-basis of `(𝓞 K)ˣ ⧸ (torsion K)`
  as an additive `ℤ`-module.

## Main results

* `NumberField.Units.rank_modTorsion`: the `ℤ`-rank of `(𝓞 K)ˣ ⧸ (torsion K)` is equal to
  `card (InfinitePlace K) - 1`.

* `NumberField.Units.exist_unique_eq_mul_prod`: **Dirichlet Unit Theorem**. Any unit of `𝓞 K`
  can be written uniquely as the product of a root of unity and powers of the units of the
  fundamental system `fundSystem`.

## Tags
number field, units, Dirichlet unit theorem
-/

@[expose] public section

noncomputable section

open Module NumberField NumberField.InfinitePlace NumberField.Units

variable (K : Type*) [Field K]

namespace NumberField.Units.dirichletUnitTheorem

/-!
### Dirichlet Unit Theorem

We define a group morphism from `(𝓞 K)ˣ` to `logSpace K`, defined as
`{w : InfinitePlace K // w ≠ w₀} → ℝ` where `w₀` is a distinguished (arbitrary) infinite place,
prove that its kernel is the torsion subgroup (see `logEmbedding_eq_zero_iff`) and that its image,
called `unitLattice`, is a full `ℤ`-lattice. It follows that `unitLattice` is a free `ℤ`-module
(see `instModuleFree_unitLattice`) of rank `card (InfinitePlace K) - 1` (see `unitLattice_rank`).
To prove that the `unitLattice` is a full `ℤ`-lattice, we need to prove that it is discrete
(see `unitLattice_inter_ball_finite`) and that it spans the full space over `ℝ`
(see `unitLattice_span_eq_top`); this is the main part of the proof, see the section `span_top`
below for more details.
-/

open Finset

variable {K}

section NumberField

variable [NumberField K]

/-- The distinguished infinite place. -/
/-
**NumberField.Units.dirichletUnitTheorem.w** 是 Mathlib 中的一个定义，位于命名空间 `NumberFiel
d.Units.dirichletUnitTheorem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distinguished infinite place.
-/
def w₀ : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some

variable (K) in
/-- The `logSpace` is defined as `{w : InfinitePlace K // w ≠ w₀} → ℝ` where `w₀` is the
distinguished infinite place. -/
/-
**NumberField.Units.dirichletUnitTheorem.logSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `N
umberField.Units.dirichletUnitTheorem`。
形式化陈述：logSpace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `logSpace` is defined as `{w : InfinitePlace K // w ≠ w₀} → ℝ` where `w₀` is
 the
distinguished infinite place.
-/
abbrev logSpace := {w : InfinitePlace K // w ≠ w₀} → ℝ

variable (K) in
/-- The logarithmic embedding of the units (seen as an `Additive` group). -/
/-
**NumberField.Units.dirichletUnitTheorem._root_.NumberField.Units.logEmbedding**
 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Units.dirichletUnitTheorem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic embedding of the units (seen as an `Additive` group).
-/
def _root_.NumberField.Units.logEmbedding :
    Additive ((𝓞 K)ˣ) →+ logSpace K :=
{ toFun := fun x w ↦ mult w.val * Real.log (w.val ↑x.toMul)
  map_zero' := by simp; rfl
  map_add' := fun _ _ ↦ by simp [Real.log_mul, mul_add]; rfl }

@[simp]
/-
**NumberField.Units.dirichletUnitTheorem.logEmbedding_component** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.Units.dirichletUnitTheorem`。
形式化陈述：logEmbedding_component (x : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w != w₀})
 : (logEmbedding K (Additive.ofMul x)) w = mult w.val * Real.log (w.val x)
参数：x : (𝓞 K)ˣ；w : {w : InfinitePlace K // w != w₀}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem logEmbedding_component (x : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w ≠ w₀}) :
    (logEmbedding K (Additive.ofMul x)) w = mult w.val * Real.log (w.val x) := rfl

open scoped Classical in
/-
**NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component** 是 Mathlib 
中的一个定理，位于命名空间 `NumberField.Units.dirichletUnitTheorem`。
形式化陈述：sum_logEmbedding_component (x : (𝓞 K)ˣ) : ∑ w, logEmbedding K (Additive.of
Mul x) w = -mult (w₀ : InfinitePlace K) * Real.log (w₀ (x : K))
参数：x : (𝓞 K)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.Units.sum_mult_mul_log`：sum_mult_mul_log [NumberField K] (x 
: (𝓞 K)ˣ) : ∑ w : InfinitePlace K, w.mult * Real.log (w x) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Fintype.sum_eq_add_sum_subtype_ne`：∀ {α : Type u_1} {M : Type u_4} [inst
 : Fintype α] [inst_1 : AddCommMonoid M] [inst_2 : DecidableEq α] (f : α → M)   
(a : α), ∑ i, f i = f a…
-/
theorem sum_logEmbedding_component (x : (𝓞 K)ˣ) :
    ∑ w, logEmbedding K (Additive.ofMul x) w =
      -mult (w₀ : InfinitePlace K) * Real.log (w₀ (x : K)) := by
  have h := sum_mult_mul_log x
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, add_comm, add_eq_zero_iff_eq_neg, ← neg_mul] at h
  simpa [logEmbedding_component] using h

end NumberField

/-
**NumberField.Units.dirichletUnitTheorem.mult_log_place_eq_zero** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.Units.dirichletUnitTheorem`。
形式化陈述：mult_log_place_eq_zero {x : (𝓞 K)ˣ} {w : InfinitePlace K} : mult w * Real.
log (w x) = 0 ↔ w x = 1
参数：𝓞 K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `NumberField.InfinitePlace.mult_coe_ne_zero`：mult_coe_ne_zero {w : Infini
tePlace K} : (mult w : Real) != 0
· 使用定理 `Real.log_eq_zero`：log_eq_zero {x : Real} : log x = 0 ↔ x = 0 ∨ x = 1 ∨ x
 = -1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NumberField.Units.pos_at_place`：pos_at_place (x : (𝓞 K)ˣ) (w : InfiniteP
lace K) : 0 < w x
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 48 条，此处仅展示前 30 条）
-/
theorem mult_log_place_eq_zero {x : (𝓞 K)ˣ} {w : InfinitePlace K} :
    mult w * Real.log (w x) = 0 ↔ w x = 1 := by
  rw [mul_eq_zero, or_iff_right, Real.log_eq_zero, or_iff_right, or_iff_left]
  · linarith [(apply_nonneg _ _ : 0 ≤ w x)]
  · exact (Units.pos_at_place _ _).ne'
  · exact mult_coe_ne_zero

variable [NumberField K]
/-
**NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.Units.dirichletUnitTheorem`。
形式化陈述：logEmbedding_eq_zero_iff {x : (𝓞 K)ˣ} : logEmbedding K (Additive.ofMul x) 
= 0 ↔ x in torsion K
参数：𝓞 K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.Units.mem_torsion`：mem_torsion {x : (𝓞 K)ˣ} : x in torsion K
 ↔ forall w : InfinitePlace K, w x = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component`：sum_l
ogEmbedding_component (x : (𝓞 K)ˣ) : ∑ w, logEmbedding K (Additive.ofMul x) w = 
-mult (w₀ : InfinitePlace K) * Real.log (w₀ (x : K))
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.Units.dirichletUnitTheorem.mult_log_place_eq_zero`：mult_log_
place_eq_zero {x : (𝓞 K)ˣ} {w : InfinitePlace K} : mult w * Real.log (w x) = 0 ↔
 w x = 1
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.Units.dirichletUnitTheorem.logEmbedding_component`：logEmbedd
ing_component (x : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w != w₀}) : (logEmbeddin
g K (Additive.ofMul x)) w = mult w.val * Real.log (…
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
-/
theorem logEmbedding_eq_zero_iff {x : (𝓞 K)ˣ} :
    logEmbedding K (Additive.ofMul x) = 0 ↔ x ∈ torsion K := by
  rw [mem_torsion]
  refine ⟨fun h w ↦ ?_, fun h ↦ ?_⟩
  · by_cases hw : w = w₀
    · suffices -mult w₀ * Real.log (w₀ (x : K)) = 0 by
        rw [neg_mul, neg_eq_zero, ← hw] at this
        exact mult_log_place_eq_zero.mp this
      rw [← sum_logEmbedding_component, sum_eq_zero]
      exact fun w _ ↦ congrFun h w
    · exact mult_log_place_eq_zero.mp (congrFun h ⟨w, hw⟩)
  · ext w
    rw [logEmbedding_component, h w.val, Real.log_one, mul_zero, Pi.zero_apply]
/-
**NumberField.Units.dirichletUnitTheorem.logEmbedding_ker** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.Units.dirichletUnitTheorem`。
形式化陈述：logEmbedding_ker : (logEmbedding K).ker = (torsion K).toAddSubgroup
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.mem_ker`：∀ {G : Type u_1} [inst : AddGroup G] {M : Type u_7
} [inst_1 : AddZeroClass M] {f : G →+ M} {x : G}, x ∈ f.ker ↔ f x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ofMul_toMul`：ofMul_toMul (x : Additive α) : ofMul x.toMul = x
· 使用定理 `NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff`：logEmbe
dding_eq_zero_iff {x : (𝓞 K)ˣ} : logEmbedding K (Additive.ofMul x) = 0 ↔ x in to
rsion K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem logEmbedding_ker : (logEmbedding K).ker = (torsion K).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, ← ofMul_toMul x, logEmbedding_eq_zero_iff]
  simp
/-
**NumberField.Units.dirichletUnitTheorem.map_logEmbedding_sup_torsion** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.Units.dirichletUnitTheorem`。
形式化陈述：map_logEmbedding_sup_torsion (s : AddSubgroup (Additive (𝓞 K)ˣ)) : (s ⊔ (t
orsion K).toAddSubgroup).map (logEmbedding K) = s.map (logEmbedding K)
参数：s : AddSubgroup (Additive (𝓞 K)ˣ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.Units.dirichletUnitTheorem.logEmbedding_ker`：logEmbedding_ke
r : (logEmbedding K).ker = (torsion K).toAddSubgroup
· 使用定理 `AddSubgroup.map_eq_map_iff`：∀ {G : Type u_1} [inst : AddGroup G] {N : Ty
pe u_5} [inst_1 : AddGroup N] {f : G →+ N} {H K : AddSubgroup G},   AddSubgroup.
map f H = AddSub…
· 使用定理 `sup_right_idem`：sup_right_idem (a b : α) : a ⊔ b ⊔ b = a ⊔ b
-/
theorem map_logEmbedding_sup_torsion (s : AddSubgroup (Additive (𝓞 K)ˣ)) :
    (s ⊔ (torsion K).toAddSubgroup).map (logEmbedding K) = s.map (logEmbedding K) := by
  rw [← logEmbedding_ker, AddSubgroup.map_eq_map_iff, sup_right_idem]

open scoped Classical in
/-
**NumberField.Units.dirichletUnitTheorem.logEmbedding_component_le** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.Units.dirichletUnitTheorem`。
形式化陈述：logEmbedding_component_le {r : Real} {x : (𝓞 K)ˣ} (hr : 0 <= r) (h : ‖logE
mbedding K x‖ <= r) (w : {w : InfinitePlace K // w != w₀}) : |logEmbedding K (Ad
ditive.ofMul x) w| <= r
参数：𝓞 K；hr : 0 <= r；h : ‖logEmbedding K x‖ <= r；w : {w : InfinitePlace K // w != 
w₀}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem logEmbedding_component_le {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r) (h : ‖logEmbedding K x‖ ≤ r)
    (w : {w : InfinitePlace K // w ≠ w₀}) : |logEmbedding K (Additive.ofMul x) w| ≤ r := by
  lift r to NNReal using hr
  simp_rw [Pi.norm_def, NNReal.coe_le_coe, Finset.sup_le_iff, ← NNReal.coe_le_coe] at h
  exact h w (mem_univ _)

set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-
**NumberField.Units.dirichletUnitTheorem.log_le_of_logEmbedding_le** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.Units.dirichletUnitTheorem`。
形式化陈述：log_le_of_logEmbedding_le {r : Real} {x : (𝓞 K)ˣ} (hr : 0 <= r) (h : ‖logE
mbedding K (Additive.ofMul x)‖ <= r) (w : InfinitePlace K) : |Real.log (w x)| <=
 (Fintype.card (InfinitePlace K)) * r
参数：𝓞 K；hr : 0 <= r；h : ‖logEmbedding K (Additive.ofMul x)‖ <= r；w : InfinitePlac
e K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NumberField.InfinitePlace.mult.eq_1`：∀ {K : Type u_1} [inst : Field K] (
w : NumberField.InfinitePlace K), w.mult = if w.IsReal then 1 else 2
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component`：sum_l
ogEmbedding_component (x : (𝓞 K)ˣ) : ∑ w, logEmbedding K (Additive.ofMul x) w = 
-mult (w₀ : InfinitePlace K) * Real.log (w₀ (x : K))
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
（共 50 条，此处仅展示前 30 条）
-/
theorem log_le_of_logEmbedding_le {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r)
    (h : ‖logEmbedding K (Additive.ofMul x)‖ ≤ r) (w : InfinitePlace K) :
    |Real.log (w x)| ≤ (Fintype.card (InfinitePlace K)) * r := by
  have tool : ∀ x : ℝ, 0 ≤ x → x ≤ mult w * x := fun x hx ↦ by
    nth_rw 1 [← one_mul x]
    refine mul_le_mul ?_ le_rfl hx ?_
    all_goals { rw [mult]; split_ifs <;> norm_num }
  by_cases hw : w = w₀
  · have hyp := congr_arg (‖·‖) (sum_logEmbedding_component x).symm
    replace hyp := (le_of_eq hyp).trans (norm_sum_le _ _)
    simp_rw [norm_mul, norm_neg, Real.norm_eq_abs, Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · rw [← hw]
      exact tool _ (abs_nonneg _)
    · refine (sum_le_card_nsmul univ _ _
        (fun w _ ↦ logEmbedding_component_le hr h w)).trans ?_
      rw [nsmul_eq_mul]
      refine mul_le_mul ?_ le_rfl hr (Fintype.card (InfinitePlace K)).cast_nonneg
      simp
  · have hyp := logEmbedding_component_le hr h ⟨w, hw⟩
    rw [logEmbedding_component, abs_mul, Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · exact tool _ (abs_nonneg _)
    · nth_rw 1 [← one_mul r]
      exact mul_le_mul (Nat.one_le_cast.mpr Fintype.card_pos) (le_of_eq rfl) hr (Nat.cast_nonneg _)

variable (K)

/-- The lattice formed by the image of the logarithmic embedding. -/
/-
**NumberField.Units.dirichletUnitTheorem._root_.NumberField.Units.unitLattice** 
是 Mathlib 中的一个定义，位于命名空间 `NumberField.Units.dirichletUnitTheorem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lattice formed by the image of the logarithmic embedding.
-/
noncomputable def _root_.NumberField.Units.unitLattice :
    Submodule ℤ (logSpace K) :=
  Submodule.map (logEmbedding K).toIntLinearMap ⊤

open scoped Classical in
/-
**NumberField.Units.dirichletUnitTheorem.unitLattice_inter_ball_finite** 是 Mathl
ib 中的一个定理，位于命名空间 `NumberField.Units.dirichletUnitTheorem`。
形式化陈述：unitLattice_inter_ball_finite (r : Real) : ((unitLattice K : Set (logSpace
 K)) inter Metric.closedBall 0 r).Finite
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.closedBall_eq_empty`：closedBall_eq_empty : closedBall x ε = ∅ ↔ ε
 < 0
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `NumberField.Embeddings.finite_of_norm_le`：finite_of_norm_le (B : Real) :
 {x : K | IsIntegral Int x ∧ forall φ : K ->+* A, ‖φ x‖ <= B}.Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `NumberField.Units.coe_injective`：coe_injective : Function.Injective ((↑)
 : (𝓞 K)ˣ -> K)
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.le_iff_le`：le_iff_le (x : K) (r : Real) : (for
all w : InfinitePlace K, w x <= r) ↔ forall φ : K ->+* Complex, ‖φ x‖ <= r
· 使用定理 `Real.log_le_iff_le_exp`：log_le_iff_le_exp (hx : 0 < x) : log x <= y ↔ x 
<= exp y
· 使用定理 `NumberField.InfinitePlace.pos_iff`：pos_iff {w : InfinitePlace K} {x : K}
 : 0 < w x ↔ x != 0
· 使用定理 `NumberField.Units.coe_ne_zero`：coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) != 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `NumberField.Units.dirichletUnitTheorem.log_le_of_logEmbedding_le`：log_le
_of_logEmbedding_le {r : Real} {x : (𝓞 K)ˣ} (hr : 0 <= r) (h : ‖logEmbedding K (
Additive.ofMul x)‖ <= r) (w : InfinitePlace K) : |Real…
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
-/
theorem unitLattice_inter_ball_finite (r : ℝ) :
    ((unitLattice K : Set (logSpace K)) ∩ Metric.closedBall 0 r).Finite := by
  obtain hr | hr := lt_or_ge r 0
  · convert! Set.finite_empty
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact Set.inter_empty _
  · suffices {x : (𝓞 K)ˣ | IsIntegral ℤ (x : K) ∧
        ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ Real.exp ((Fintype.card (InfinitePlace K)) * r)}.Finite by
      refine (Set.Finite.image (logEmbedding K) this).subset ?_
      rintro _ ⟨⟨x, ⟨_, rfl⟩⟩, hx⟩
      refine ⟨x, ⟨x.val.prop, (le_iff_le _ _).mp (fun w ↦ (Real.log_le_iff_le_exp ?_).mp ?_)⟩, rfl⟩
      · exact pos_iff.mpr (coe_ne_zero x)
      · rw [mem_closedBall_zero_iff] at hx
        exact (le_abs_self _).trans (log_le_of_logEmbedding_le hr hx w)
    refine Set.Finite.of_finite_image ?_ (coe_injective K).injOn
    refine (Embeddings.finite_of_norm_le K ℂ
        (Real.exp ((Fintype.card (InfinitePlace K)) * r))).subset ?_
    rintro _ ⟨x, ⟨⟨h_int, h_le⟩, rfl⟩⟩
    exact ⟨h_int, h_le⟩

section span_top

/-!
#### Section `span_top`

In this section, we prove that the span over `ℝ` of the `unitLattice` is equal to the full space.
For this, we construct for each infinite place `w₁ ≠ w₀` a unit `u_w₁` of `K` such that, for all
infinite places `w` such that `w ≠ w₁`, we have `Real.log w (u_w₁) < 0`
(and thus `Real.log w₁ (u_w₁) > 0`). It follows then from a determinant computation
(using `Matrix.det_ne_zero_of_sum_col_lt_diag`) that the image by `logEmbedding` of these units is
a `ℝ`-linearly independent family. The unit `u_w₁` is obtained by constructing a sequence `seq n`
of nonzero algebraic integers that is strictly decreasing at infinite places distinct from `w₁` and
of norm `≤ B`. Since there are finitely many ideals of norm `≤ B`, there exists two term in the
sequence defining the same ideal and their quotient is the desired unit `u_w₁` (see `exists_unit`).
-/

open NumberField.mixedEmbedding NNReal

variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)

set_option backward.isDefEq.respectTransparency false in
include hB in
/-- This result shows that there always exists a next term in the sequence. -/
/-
**NumberField.Units.dirichletUnitTheorem.seq_next** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.Units.dirichletUnitTheorem`。
形式化陈述：seq_next {x : 𝓞 K} (hx : x != 0) : exists y : 𝓞 K, y != 0 ∧ (forall w, w !
= w₁ -> w y < w x) ∧ |Algebra.norm Rat (y : K)| <= B
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `NumberField.RingOfIntegers.coe_ne_zero_iff`：coe_ne_zero_iff {x : 𝓞 K} : 
algebraMap _ K x != 0 ↔ x != 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AbsoluteValue.nonneg`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 : R), 0 ≤…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Nonneg.mk_eq_zero`：mk_eq_zero [Zero α] [Preorder α] {x : α} (hx : 0 <= x
) : (⟨x, hx⟩ : { x : α // 0 <= x }) = 0 ↔ x = 0
· 使用定理 `div_eq_zero_iff`：div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `map_eq_zero`：map_eq_zero : f a = 0 ↔ a = 0
· 使用定理 `NumberField.InfinitePlace.instMonoidWithZeroHomClassReal`：∀ {K : Type u_
1} [inst : Field K], MonoidWithZeroHomClass (NumberField.InfinitePlace K) K ℝ
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.adjust_f`：adjust_f {w₁ : InfinitePlace K} (B 
: Real>=0) (hf : forall w, w != w₁ -> f w != 0) : exists g : InfinitePlace K -> 
Real>=0, (forall w, w != …
· 使用定理 `NumberField.mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt`：exists_
ne_zero_mem_ringOfIntegers_lt (h : minkowskiBound K ↑1 < volume (convexBodyLT K 
f)) : exists a : 𝓞 K, a != 0 ∧ forall w : InfinitePla…
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `NumberField.mixedEmbedding.convexBodyLT_volume`：convexBodyLT_volume : vo
lume (convexBodyLT K f) = (convexBodyLTFactor K) * ∏ w, (f w) ^ (mult w)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
This result shows that there always exists a next term in the sequence.
-/
theorem seq_next {x : 𝓞 K} (hx : x ≠ 0) :
    ∃ y : 𝓞 K, y ≠ 0 ∧
      (∀ w, w ≠ w₁ → w y < w x) ∧
      |Algebra.norm ℚ (y : K)| ≤ B := by
  have hx' := RingOfIntegers.coe_ne_zero_iff.mpr hx
  let f : InfinitePlace K → ℝ≥0 :=
    fun w ↦ ⟨(w x) / 2, div_nonneg (AbsoluteValue.nonneg _ _) (by simp)⟩
  suffices ∀ w, w ≠ w₁ → f w ≠ 0 by
    obtain ⟨g, h_geqf, h_gprod⟩ := adjust_f K B this
    obtain ⟨y, h_ynz, h_yle⟩ := exists_ne_zero_mem_ringOfIntegers_lt K (f := g)
      (by rw [convexBodyLT_volume]; convert! hB; exact congr_arg ((↑) : NNReal → ENNReal) h_gprod)
    refine ⟨y, h_ynz, fun w hw ↦ (h_geqf w hw ▸ h_yle w).trans ?_, ?_⟩
    · rw [← Rat.cast_le (K := ℝ), Rat.cast_natCast]
      calc
        _ = ∏ w : InfinitePlace K, w (algebraMap _ K y) ^ mult w :=
          (prod_eq_abs_norm (algebraMap _ K y)).symm
        _ ≤ ∏ w : InfinitePlace K, (g w : ℝ) ^ mult w := by gcongr with w; exact (h_yle w).le
        _ ≤ (B : ℝ) := by
          simp_rw [← NNReal.coe_pow, ← NNReal.coe_prod]
          exact le_of_eq (congr_arg toReal h_gprod)
    · refine div_lt_self ?_ (by simp)
      exact pos_iff.mpr hx'
  intro _ _
  rw [ne_eq, Nonneg.mk_eq_zero, div_eq_zero_iff, map_eq_zero, not_or]
  exact ⟨hx', by simp⟩

/-- An infinite sequence of nonzero algebraic integers of `K` satisfying the following properties:
• `seq n` is nonzero;
• for `w : InfinitePlace K`, `w ≠ w₁ → w (seq n + 1) < w (seq n)`;
• `∣norm (seq n)∣ ≤ B`. -/
/-
**NumberField.Units.dirichletUnitTheorem.seq** 是 Mathlib 中的一个定义，位于命名空间 `NumberFi
eld.Units.dirichletUnitTheorem`。
形式化陈述：(K : Type u_1) →   [inst : Field K] →     [inst_1 : NumberField K] →      
 NumberField.InfinitePlace K →         {B : ℕ} →           NumberField.mixedEmbe
dding.minkowskiBound K 1 < ↑(NumberField.mixedEmbedding.convexBodyLTFactor K) * 
↑B →             ℕ → { x // x ≠ 0 }
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K

--- 原说明 ---
An infinite sequence of nonzero algebraic integers of `K` satisfying the followi
ng properties:
• `seq n` is nonzero;
• for `w : InfinitePlace K`, `w ≠ w₁ → w (seq n + 1) < w (seq n)`;
• `∣norm (seq n)∣ ≤ B`.
-/
def seq : ℕ → { x : 𝓞 K // x ≠ 0 }
  | 0 => ⟨1, by simp⟩
  | n + 1 =>
    ⟨(seq_next K w₁ hB (seq n).prop).choose, (seq_next K w₁ hB (seq n).prop).choose_spec.1⟩

/-- The terms of the sequence are nonzero. -/
/-
**NumberField.Units.dirichletUnitTheorem.seq_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.Units.dirichletUnitTheorem`。
形式化陈述：seq_ne_zero (n : Nat) : algebraMap (𝓞 K) K (seq K w₁ hB n) != 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `NumberField.RingOfIntegers.coe_ne_zero_iff`：coe_ne_zero_iff {x : 𝓞 K} : 
algebraMap _ K x != 0 ↔ x != 0
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
The terms of the sequence are nonzero.
-/
theorem seq_ne_zero (n : ℕ) : algebraMap (𝓞 K) K (seq K w₁ hB n) ≠ 0 :=
  RingOfIntegers.coe_ne_zero_iff.mpr (seq K w₁ hB n).prop

/-- The sequence is strictly decreasing at infinite places distinct from `w₁`. -/
/-
**NumberField.Units.dirichletUnitTheorem.seq_decreasing** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.Units.dirichletUnitTheorem`。
形式化陈述：seq_decreasing {n m : Nat} (h : n < m) (w : InfinitePlace K) (hw : w != w₁
) : w (algebraMap (𝓞 K) K (seq K w₁ hB m)) < w (algebraMap (𝓞 K) K (seq K w₁ hB 
n))
参数：h : n < m；w : InfinitePlace K；hw : w != w₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Nat.not_succ_le_zero`：∀ (n : ℕ), n.succ ≤ 0 → False
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.Units.dirichletUnitTheorem.seq_next`：seq_next {x : 𝓞 K} (hx 
: x != 0) : exists y : 𝓞 K, y != 0 ∧ (forall w, w != w₁ -> w y < w x) ∧ |Algebra
.norm Rat (y : K)| <= B
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c

--- 原说明 ---
The sequence is strictly decreasing at infinite places distinct from `w₁`.
-/
theorem seq_decreasing {n m : ℕ} (h : n < m) (w : InfinitePlace K) (hw : w ≠ w₁) :
    w (algebraMap (𝓞 K) K (seq K w₁ hB m)) < w (algebraMap (𝓞 K) K (seq K w₁ hB n)) := by
  induction m with
  | zero =>
      exfalso
      exact Nat.not_succ_le_zero n h
  | succ m m_ih =>
      cases eq_or_lt_of_le (Nat.le_of_lt_succ h) with
      | inl hr =>
          rw [hr]
          exact (seq_next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw
      | inr hr =>
          refine lt_trans ?_ (m_ih hr)
          exact (seq_next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw

/-- The terms of the sequence have norm bounded by `B`. -/
/-
**NumberField.Units.dirichletUnitTheorem.seq_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.Units.dirichletUnitTheorem`。
形式化陈述：seq_norm_le (n : Nat) : Int.natAbs (Algebra.norm Int (seq K w₁ hB n : 𝓞 K)
) <= B
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Algebra.coe_norm_int`：Algebra.coe_norm_int : (Algebra.norm Int x : Rat) 
= Algebra.norm Rat (x : K)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `NumberField.Units.dirichletUnitTheorem.seq_next`：seq_next {x : 𝓞 K} (hx 
: x != 0) : exists y : 𝓞 K, y != 0 ∧ (forall w, w != w₁ -> w y < w x) ∧ |Algebra
.norm Rat (y : K)| <= B
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
The terms of the sequence have norm bounded by `B`.
-/
theorem seq_norm_le (n : ℕ) :
    Int.natAbs (Algebra.norm ℤ (seq K w₁ hB n : 𝓞 K)) ≤ B := by
  cases n with
  | zero =>
      have : 1 ≤ B := by
        contrapose! hB
        simp only [Nat.lt_one_iff.mp hB, CharP.cast_eq_zero, mul_zero, zero_le]
      simp only [ne_eq, seq, map_one, Int.natAbs_one, this]
  | succ n =>
      rw [← Nat.cast_le (α := ℚ), Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
      exact (seq_next K w₁ hB (seq K w₁ hB n).prop).choose_spec.2.2

/-- Construct a unit associated to the place `w₁`. The family, for `w₁ ≠ w₀`, formed by the
image by the `logEmbedding` of these units is `ℝ`-linearly independent, see
`unitLattice_span_eq_top`. -/
/-
**NumberField.Units.dirichletUnitTheorem.exists_unit** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.Units.dirichletUnitTheorem`。
形式化陈述：exists_unit (w₁ : InfinitePlace K) : exists u : (𝓞 K)ˣ, forall w : Infinit
ePlace K, w != w₁ -> Real.log (w u) < 0
参数：w₁ : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.exists_nat_mul_gt`：exists_nat_mul_gt (ha : a != 0) (hb : b != ∞)
 : exists n : Nat, b < n * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `NumberField.mixedEmbedding.convexBodyLTFactor_ne_zero`：convexBodyLTFacto
r_ne_zero : convexBodyLTFactor K != 0
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `NumberField.mixedEmbedding.minkowskiBound_lt_top`：minkowskiBound_lt_top 
: minkowskiBound K I < ⊤
· 使用定理 `Set.Finite.exists_lt_map_eq_of_forall_mem`：∀ {α : Type u_2} {β : Type u_
3} [inst : LinearOrder α] {t : Set β} {f : α → β} [Infinite α],   (∀ (a : α), f 
a ∈ t) → t.Finite → ∃ a b, a < …
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.Units.dirichletUnitTheorem.seq_norm_le`：seq_norm_le (n : Nat
) : Int.natAbs (Algebra.norm Int (seq K w₁ hB n : 𝓞 K)) <= B
· 使用定理 `Ideal.finite_setOfPred_absNorm_le`：finite_setOfPred_absNorm_le [CharZero
 S] (n : Nat) : {I : Ideal S | Ideal.absNorm I <= n}.Finite
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
· 使用定理 `NumberField.Units.pos_at_place`：pos_at_place (x : (𝓞 K)ˣ) (w : InfiniteP
lace K) : 0 < w x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Construct a unit associated to the place `w₁`. The family, for `w₁ ≠ w₀`, formed
 by the
image by the `logEmbedding` of these units is `ℝ`-linearly independent, see
`unitLattice_span_eq_top`.
-/
theorem exists_unit (w₁ : InfinitePlace K) :
    ∃ u : (𝓞 K)ˣ, ∀ w : InfinitePlace K, w ≠ w₁ → Real.log (w u) < 0 := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, minkowskiBound K 1 < (convexBodyLTFactor K) * B := by
    conv => congr; ext; rw [mul_comm]
    exact ENNReal.exists_nat_mul_gt (ENNReal.coe_ne_zero.mpr (convexBodyLTFactor_ne_zero K))
      (ne_of_lt (minkowskiBound_lt_top K 1))
  rsuffices ⟨n, m, hnm, h⟩ : ∃ n m, n < m ∧
      (Ideal.span ({ (seq K w₁ hB n : 𝓞 K) }) = Ideal.span ({ (seq K w₁ hB m : 𝓞 K) }))
  · have hu := Ideal.span_singleton_eq_span_singleton.mp h
    refine ⟨hu.choose, fun w hw ↦ Real.log_neg (pos_at_place hu.choose w) ?_⟩
    calc
      _ = w (algebraMap (𝓞 K) K (seq K w₁ hB m) * (algebraMap (𝓞 K) K (seq K w₁ hB n))⁻¹) := by
        rw [← congr_arg (algebraMap (𝓞 K) K) hu.choose_spec, mul_comm, map_mul (algebraMap _ _),
          ← mul_assoc, inv_mul_cancel₀ (seq_ne_zero K w₁ hB n), one_mul]
      _ = w (algebraMap (𝓞 K) K (seq K w₁ hB m)) * w (algebraMap (𝓞 K) K (seq K w₁ hB n))⁻¹ :=
        map_mul _ _ _
      _ < 1 := by
        rw [map_inv₀, mul_inv_lt_iff₀' (pos_iff.mpr (seq_ne_zero K w₁ hB n)), mul_one]
        exact seq_decreasing K w₁ hB hnm w hw
  refine Set.Finite.exists_lt_map_eq_of_forall_mem (t := {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ B})
    (fun n ↦ ?_) (Ideal.finite_setOfPred_absNorm_le B)
  rw [Set.mem_ofPred_eq, Ideal.absNorm_span_singleton]
  exact seq_norm_le K w₁ hB n

set_option backward.isDefEq.respectTransparency.types false in
/-
**NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.Units.dirichletUnitTheorem`。
形式化陈述：unitLattice_span_eq_top : Submodule.span Real (unitLattice K : Set (logSpa
ce K)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.Units.dirichletUnitTheorem.exists_unit`：exists_unit (w₁ : In
finitePlace K) : exists u : (𝓞 K)ˣ, forall w : InfinitePlace K, w != w₁ -> Real.
log (w u) < 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
· 使用定理 `det_ne_zero_of_sum_col_lt_diag`：det_ne_zero_of_sum_col_lt_diag (h : fora
ll k, ∑ i in Finset.univ.erase k, ‖A i k‖ < ‖A k k‖) : A.det != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.coePiBasisFun.toMatrix_eq_transpose`：∀ {ι : Type u_1} {R : 
Type u_5} [inst : CommSemiring R] [inst_1 : Finite ι],   (Pi.basisFun R ι).toMat
rix = Matrix.transpose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `mul_neg_of_pos_of_neg`：mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 
0 < a) (hb : b < 0) : a * b < 0
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `NumberField.InfinitePlace.mult.eq_1`：∀ {K : Type u_1} [inst : Field K] (
w : NumberField.InfinitePlace K), w.mult = if w.IsReal then 1 else 2
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
（共 62 条，此处仅展示前 30 条）
-/
theorem unitLattice_span_eq_top :
    Submodule.span ℝ (unitLattice K : Set (logSpace K)) = ⊤ := by
  classical
  refine le_antisymm le_top ?_
  -- The standard basis
  let B := Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}
  -- The image by log_embedding of the family of units constructed above
  let v := fun w : { w : InfinitePlace K // w ≠ w₀ } ↦
    logEmbedding K (Additive.ofMul (exists_unit K w).choose)
  -- To prove the result, it is enough to prove that the family `v` is linearly independent
  suffices B.det v ≠ 0 by
    rw [← isUnit_iff_ne_zero, ← Basis.is_basis_iff_det] at this
    rw [← this.2]
    refine Submodule.span_monotone fun _ ⟨w, hw⟩ ↦ ⟨(exists_unit K w).choose, trivial, hw⟩
  rw [Basis.det_apply]
  -- We use a specific lemma to prove that this determinant is nonzero
  refine det_ne_zero_of_sum_col_lt_diag (fun w ↦ ?_)
  simp_rw [Real.norm_eq_abs, B, Basis.coePiBasisFun.toMatrix_eq_transpose, Matrix.transpose_apply]
  rw [← sub_pos, sum_congr rfl (fun x hx ↦ abs_of_neg ?_), sum_neg_distrib, sub_neg_eq_add,
    sum_erase_eq_sub (mem_univ _), ← add_comm_sub]
  · refine add_pos_of_nonneg_of_pos ?_ ?_
    · rw [sub_nonneg]
      exact le_abs_self _
    · rw [sum_logEmbedding_component (exists_unit K w).choose]
      refine mul_pos_of_neg_of_neg ?_ ((exists_unit K w).choose_spec _ w.prop.symm)
      rw [mult]; split_ifs <;> norm_num
  · refine mul_neg_of_pos_of_neg ?_ ((exists_unit K w).choose_spec x ?_)
    · rw [mult]; split_ifs <;> norm_num
    · exact Subtype.ext_iff.not.mp (ne_of_mem_erase hx)

end span_top

end dirichletUnitTheorem

section statements

variable [NumberField K]

open dirichletUnitTheorem Module

/-- The unit rank of the number field `K`, it is equal to `card (InfinitePlace K) - 1`. -/
/-
**NumberField.Units.rank** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Units`。
形式化陈述：(K : Type u_1) → [inst : Field K] → [NumberField K] → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit rank of the number field `K`, it is equal to `card (InfinitePlace K) - 
1`.
-/
def rank : ℕ := Fintype.card (InfinitePlace K) - 1
/-
**NumberField.Units.instDiscrete_unitLattice** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K], DiscreteTopolo
gy ↥(NumberField.Units.unitLattice K)
参数：K : Type u_1；NumberField.Units.unitLattice K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `discreteTopology_of_isOpen_singleton_zero`：∀ {G : Type w} [inst : Topolo
gicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G],   IsOpen {0} → 
DiscreteTopology G
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `isOpen_singleton_of_finite_mem_nhds`：isOpen_singleton_of_finite_mem_nhds
 [T1Space X] (x : X) {s : Set X} (hs : s in 𝓝 x) (hsf : s.Finite) : IsOpen ({x} 
: Set X)
· 使用定理 `instT1SpaceForall`：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i : ι) →
 TopologicalSpace (X i)] [∀ (i : ι), T1Space (X i)],   T1Space ((i : ι) → X i)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `NumberField.Units.dirichletUnitTheorem.unitLattice_inter_ball_finite`：un
itLattice_inter_ball_finite (r : Real) : ((unitLattice K : Set (logSpace K)) int
er Metric.closedBall 0 r).Finite
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
instance instDiscrete_unitLattice : DiscreteTopology (unitLattice K) := by
  classical
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ (by simp)
  · refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.val_injective)
    convert! unitLattice_inter_ball_finite K 1
    ext x
    refine ⟨?_, fun ⟨hx1, hx2⟩ ↦ ⟨⟨x, hx1⟩, hx2, rfl⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact ⟨Subtype.mem x, hx⟩

open scoped Classical in
/-
**NumberField.Units.instZLattice_unitLattice** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K], IsZLattice ℝ (
NumberField.Units.unitLattice K)
参数：K : Type u_1；NumberField.Units.unitLattice K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top`：unitLatt
ice_span_eq_top : Submodule.span Real (unitLattice K : Set (logSpace K)) = ⊤
-/
instance instZLattice_unitLattice : IsZLattice ℝ (unitLattice K) where
  span_top := unitLattice_span_eq_top K

set_option backward.isDefEq.respectTransparency false in
/-
**NumberField.Units.finrank_eq_rank** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units
`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],   Module.finra
nk ℝ (NumberField.Units.dirichletUnitTheorem.logSpace K) = NumberField.Units.ran
k K
参数：K : Type u_1；NumberField.Units.dirichletUnitTheorem.logSpace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem finrank_eq_rank :
    finrank ℝ (logSpace K) = Units.rank K := by
  classical
  simp only [finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_ofSubsingleton, rank]

@[simp]
/-
**NumberField.Units.unitLattice_rank** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Unit
s`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],   Module.finra
nk ℤ ↥(NumberField.Units.unitLattice K) = NumberField.Units.rank K
参数：K : Type u_1；NumberField.Units.unitLattice K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.Units.finrank_eq_rank`：∀ (K : Type u_1) [inst : Field K] [in
st_1 : NumberField K],   Module.finrank ℝ (NumberField.Units.dirichletUnitTheore
m.logSpace K) = NumberF…
· 使用定理 `ZLattice.rank`：ZLattice.rank [hs : IsZLattice K L] : finrank Int L = fin
rank K E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
-/
theorem unitLattice_rank :
    finrank ℤ (unitLattice K) = Units.rank K := by
  classical
  rw [← Units.finrank_eq_rank, ZLattice.rank ℝ]

/-- The map obtained by quotienting by the kernel of `logEmbedding`. -/
/-
**NumberField.Units.logEmbeddingQuot** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Unit
s`。
形式化陈述：(K : Type u_1) →   [inst : Field K] →     [inst_1 : NumberField K] →      
 Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K) →+    
     NumberField.Units.dirichletUnitTheorem.logSpace K
参数：NumberField.RingOfIntegers K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map obtained by quotienting by the kernel of `logEmbedding`.
-/
def logEmbeddingQuot :
    Additive ((𝓞 K)ˣ ⧸ (torsion K)) →+ logSpace K :=
  MonoidHom.toAdditiveLeft <|
    (QuotientGroup.kerLift (AddMonoidHom.toMultiplicativeRight (logEmbedding K))).comp
      (QuotientGroup.quotientMulEquivOfEq (by
        ext
        rw [MonoidHom.mem_ker, AddMonoidHom.toMultiplicativeRight_apply_apply, ofAdd_eq_one,
          ← logEmbedding_eq_zero_iff])).toMonoidHom

@[simp]
/-
**NumberField.Units.logEmbeddingQuot_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x : (NumberFie
ld.RingOfIntegers K)ˣ),   (NumberField.Units.logEmbeddingQuot K) (Additive.ofMul
 ↑x) = (NumberField.Units.logEmbedding K) (Additive.ofMul x)
参数：K : Type u_1；x : (NumberField.RingOfIntegers K)ˣ；NumberField.Units.logEmbeddi
ngQuot K；Additive.ofMul ↑x；NumberField.Units.logEmbedding K；Additive.ofMul x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
-/
theorem logEmbeddingQuot_apply (x : (𝓞 K)ˣ) :
    logEmbeddingQuot K (Additive.ofMul (QuotientGroup.mk x)) =
      logEmbedding K (Additive.ofMul x) := rfl
/-
**NumberField.Units.logEmbeddingQuot_injective** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K], Function.Injec
tive ⇑(NumberField.Units.logEmbeddingQuot K)
参数：K : Type u_1；NumberField.Units.logEmbeddingQuot K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `QuotientGroup.kerLift_injective`：kerLift_injective : Injective (kerLift 
φ)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.toAdditiveLeft_apply_apply`：∀ {α : Type u_3} {β : Type u_4} [i
nst : MulOneClass α] [inst_1 : AddZeroClass β] (a : α →* Multiplicative β)   (a_
1 : Additive α), (MonoidHo…
-/
theorem logEmbeddingQuot_injective :
    Function.Injective (logEmbeddingQuot K) := by
  unfold logEmbeddingQuot
  intro _ _ h
  simp_rw [MonoidHom.toAdditiveLeft_apply_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at h
  exact (EmbeddingLike.apply_eq_iff_eq _).mp <| (QuotientGroup.kerLift_injective _).eq_iff.mp h

set_option backward.isDefEq.respectTransparency.types false in
/-- The linear equivalence between `(𝓞 K)ˣ ⧸ (torsion K)` as an additive `ℤ`-module and
`unitLattice` . -/
/-
**NumberField.Units.logEmbeddingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Uni
ts`。
形式化陈述：(K : Type u_1) →   [inst : Field K] →     [inst_1 : NumberField K] →      
 Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K) ≃ₗ[ℤ] 
↥(NumberField.Units.unitLattice K)
参数：NumberField.RingOfIntegers K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between `(𝓞 K)ˣ ⧸ (torsion K)` as an additive `ℤ`-module 
and
`unitLattice` .
-/
def logEmbeddingEquiv :
    Additive ((𝓞 K)ˣ ⧸ (torsion K)) ≃ₗ[ℤ] (unitLattice K) :=
  LinearEquiv.ofBijective ((logEmbeddingQuot K).codRestrict (unitLattice K)
    (Quotient.ind fun _ ↦ logEmbeddingQuot_apply K _ ▸
      Submodule.mem_map_of_mem trivial)).toIntLinearMap
    ⟨fun _ _ ↦ by
      rw [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.codRestrict_apply,
        AddMonoidHom.codRestrict_apply, Subtype.mk.injEq]
      apply logEmbeddingQuot_injective K, fun ⟨a, ⟨b, _, ha⟩⟩ ↦ ⟨⟦b⟧, by simpa using! ha⟩⟩

@[simp]
/-
**NumberField.Units.logEmbeddingEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x : (NumberFie
ld.RingOfIntegers K)ˣ),   ↑((NumberField.Units.logEmbeddingEquiv K) (Additive.of
Mul ↑x)) = (NumberField.Units.logEmbedding K) (Additive.ofMul x)
参数：K : Type u_1；x : (NumberField.RingOfIntegers K)ˣ；(NumberField.Units.logEmbedd
ingEquiv K) (Additive.ofMul ↑x)；NumberField.Units.logEmbedding K；Additive.ofMul 
x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem logEmbeddingEquiv_apply (x : (𝓞 K)ˣ) :
    logEmbeddingEquiv K (Additive.ofMul (QuotientGroup.mk x)) =
      logEmbedding K (Additive.ofMul x) := rfl
/-
**NumberField.Units.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) := by
  classical exact Module.Free.of_equiv (logEmbeddingEquiv K).symm
/-
**NumberField.Units.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) := by
  classical exact Module.Finite.equiv (logEmbeddingEquiv K).symm

-- Note that we prove this instance first and then deduce from it the instance
-- `Monoid.FG (𝓞 K)ˣ`, and not the other way around, due to no `Subgroup` version
-- of `Submodule.fg_of_fg_map_of_fg_inf_ker` existing.
/-
**NumberField.Units.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite ℤ (Additive (𝓞 K)ˣ) := by
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (MonoidHom.toAdditive (QuotientGroup.mk' (torsion K))).toIntLinearMap ?_ ?_
  · rw [Submodule.map_top, LinearMap.range_eq_top.mpr
      (by exact QuotientGroup.mk'_surjective (torsion K)), ← Module.finite_def]
    infer_instance
  · rw [inf_of_le_right le_top, AddMonoidHom.coe_toIntLinearMap_ker, MonoidHom.coe_toAdditive_ker,
      QuotientGroup.ker_mk', Submodule.fg_iff_addSubgroup_fg,
      AddSubgroup.toIntSubmodule_toAddSubgroup, ← AddGroup.fg_iff_addSubgroup_fg]
    have : Finite (Subgroup.toAddSubgroup (torsion K)) := (inferInstance : Finite (torsion K))
    exact AddGroup.fg_of_finite
/-
**NumberField.Units.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid.FG (𝓞 K)ˣ := by
  rw [Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]
  infer_instance
/-
**NumberField.Units.finrank_modTorsion** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Un
its`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],   Module.finra
nk ℤ (Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K)) 
= NumberField.Units.rank K
参数：K : Type u_1；Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.to
rsion K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `NumberField.Units.unitLattice_rank`：∀ (K : Type u_1) [inst : Field K] [i
nst_1 : NumberField K],   Module.finrank ℤ ↥(NumberField.Units.unitLattice K) = 
NumberField.Units.rank K
-/
theorem finrank_modTorsion : finrank ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) = rank K := by
  rw [← LinearEquiv.finrank_eq (logEmbeddingEquiv K).symm, unitLattice_rank]

@[deprecated (since := "2026-06-05")] alias rank_modTorsion := finrank_modTorsion
/-
**NumberField.Units.finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],   Module.finra
nk ℤ (Additive (NumberField.RingOfIntegers K)ˣ) = NumberField.Units.rank K
参数：K : Type u_1；Additive (NumberField.RingOfIntegers K)ˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finrank_quotient_torsion_eq`：finrank_quotient_torsion_eq {M : Type*} [Ad
dCommGroup M] : Module.finrank Int (M ⧸ (AddCommGroup.torsion M).toIntSubmodule)
 = Module.finrank…
-/
theorem finrank_eq : finrank ℤ (Additive (𝓞 K)ˣ) = rank K := by
  simpa [← finrank_modTorsion] using! finrank_quotient_torsion_eq.symm

/-- A basis of the quotient `(𝓞 K)ˣ ⧸ (torsion K)` seen as an additive ℤ-module. -/
/-
**NumberField.Units.basisModTorsion** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Units
`。
形式化陈述：(K : Type u_1) →   [inst : Field K] →     [inst_1 : NumberField K] →      
 Module.Basis (Fin (NumberField.Units.rank K)) ℤ         (Additive ((NumberField
.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K))
参数：NumberField.Units.rank K；(NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.
torsion K。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.Units.instFreeIntAdditiveQuotientUnitsRingOfIntegersSubgroup
Torsion`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   Module.Free ℤ (Add
itive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K)…
· 使用定理 `NumberField.Units.instFiniteIntAdditiveQuotientUnitsRingOfIntegersSubgro
upTorsion`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   Module.Finite ℤ 
(Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion …

--- 原说明 ---
A basis of the quotient `(𝓞 K)ˣ ⧸ (torsion K)` seen as an additive ℤ-module.
-/
def basisModTorsion : Basis (Fin (rank K)) ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) :=
  Basis.reindex (Module.Free.chooseBasis ℤ _) (Fintype.equivOfCardEq <| by
    rw [← Module.finrank_eq_card_chooseBasisIndex, finrank_modTorsion, Fintype.card_fin])

/-- The basis of the `unitLattice` obtained by mapping `basisModTorsion` via `logEmbedding`. -/
/-
**NumberField.Units.basisUnitLattice** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Unit
s`。
形式化陈述：(K : Type u_1) →   [inst : Field K] →     [inst_1 : NumberField K] → Modul
e.Basis (Fin (NumberField.Units.rank K)) ℤ ↥(NumberField.Units.unitLattice K)
参数：NumberField.Units.rank K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis of the `unitLattice` obtained by mapping `basisModTorsion` via `logEmb
edding`.
-/
def basisUnitLattice : Basis (Fin (rank K)) ℤ (unitLattice K) :=
  (basisModTorsion K).map (logEmbeddingEquiv K)

/-- A fundamental system of units of `K`. The units of `fundSystem` are arbitrary lifts of the
units in `basisModTorsion`. -/
/-
**NumberField.Units.fundSystem** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Units`。
形式化陈述：(K : Type u_1) →   [inst : Field K] → [inst_1 : NumberField K] → Fin (Numb
erField.Units.rank K) → (NumberField.RingOfIntegers K)ˣ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fundamental system of units of `K`. The units of `fundSystem` are arbitrary li
fts of the
units in `basisModTorsion`.
-/
def fundSystem : Fin (rank K) → (𝓞 K)ˣ :=
  -- `:)` prevents the `⧸` decaying to a quotient by `leftRel` when we unfold this later
  fun i ↦ Quotient.out ((basisModTorsion K i).toMul :)
/-
**NumberField.Units.fundSystem_mk** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (i : Fin (Numbe
rField.Units.rank K)),   Additive.ofMul ↑(NumberField.Units.fundSystem K i) = (N
umberField.Units.basisModTorsion K) i
参数：K : Type u_1；i : Fin (NumberField.Units.rank K)；NumberField.Units.fundSystem 
K i；NumberField.Units.basisModTorsion K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fundSystem_mk (i : Fin (rank K)) :
    Additive.ofMul (QuotientGroup.mk (fundSystem K i)) = (basisModTorsion K i) := by
  simp_rw [fundSystem, ← Equiv.eq_symm_apply, Additive.ofMul_symm_eq, Quotient.out_eq']
/-
**NumberField.Units.logEmbedding_fundSystem** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (i : Fin (Numbe
rField.Units.rank K)),   (NumberField.Units.logEmbedding K) (Additive.ofMul (Num
berField.Units.fundSystem K i)) =     ↑((NumberField.Units.basisUnitLattice K) i
)
参数：K : Type u_1；i : Fin (NumberField.Units.rank K)；NumberField.Units.logEmbeddin
g K；Additive.ofMul (NumberField.Units.fundSystem K i)；(NumberField.Units.basisUn
itLattice K) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.Units.basisUnitLattice.eq_1`：∀ (K : Type u_1) [inst : Field 
K] [inst_1 : NumberField K],   NumberField.Units.basisUnitLattice K =     (Numbe
rField.Units.basisModTorsion …
· 使用定理 `Module.Basis.map_apply`：map_apply (i) : b.map f i = f (b i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.Units.fundSystem_mk`：∀ (K : Type u_1) [inst : Field K] [inst
_1 : NumberField K] (i : Fin (NumberField.Units.rank K)),   Additive.ofMul ↑(Num
berField.Units.fundSy…
· 使用定理 `NumberField.Units.logEmbeddingEquiv_apply`：∀ (K : Type u_1) [inst : Fiel
d K] [inst_1 : NumberField K] (x : (NumberField.RingOfIntegers K)ˣ),   ↑((Number
Field.Units.logEmbeddingEquiv K…
-/
theorem logEmbedding_fundSystem (i : Fin (rank K)) :
    logEmbedding K (Additive.ofMul (fundSystem K i)) = basisUnitLattice K i := by
  rw [basisUnitLattice, Basis.map_apply, ← fundSystem_mk, logEmbeddingEquiv_apply]

/-- The exponents that appear in the unique decomposition of a unit as the product of
a root of unity and powers of the units of the fundamental system `fundSystem` (see
`exist_unique_eq_mul_prod`) are given by the representation of the unit on `basisModTorsion`. -/
/-
**NumberField.Units.fun_eq_repr** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] {x ζ : (NumberF
ield.RingOfIntegers K)ˣ}   {f : Fin (NumberField.Units.rank K) → ℤ},   ζ ∈ Numbe
rField.Units.torsion K →     x = ζ * ∏ i, NumberField.Units.fundSystem K i ^ f i
 →       f = ⇑((NumberField.Units.basisModTorsion K).repr (Additive.ofMul ↑x))
参数：K : Type u_1；NumberField.RingOfIntegers K；NumberField.Units.rank K；(NumberFie
ld.Units.basisModTorsion K).repr (Additive.ofMul ↑x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.mk_mul`：mk_mul (a b : G) : ((a * b : G) : Q) = a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `QuotientGroup.mk_prod`：mk_prod {G ι : Type*} [CommGroup G] (N : Subgroup
 G) (s : Finset ι) {f : ι -> G} : ((Finset.prod s f : G) : G ⧸ N) = Finset.prod 
s (fun i =>…
· 使用定理 `ofMul_prod`：ofMul_prod (s : Finset ι) (f : ι -> M) : ofMul (∏ i in s, f 
i) = ∑ i in s, ofMul (f i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `QuotientGroup.out_eq'`：out_eq' (a : α ⧸ s) : mk a.out = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.repr_sum_self`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_
6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M]
 [inst_3 : Finty…

--- 原说明 ---
The exponents that appear in the unique decomposition of a unit as the product o
f
a root of unity and powers of the units of the fundamental system `fundSystem` (
see
`exist_unique_eq_mul_prod`) are given by the representation of the unit on `basi
sModTorsion`.
-/
theorem fun_eq_repr {x ζ : (𝓞 K)ˣ} {f : Fin (rank K) → ℤ} (hζ : ζ ∈ torsion K)
    (h : x = ζ * ∏ i, (fundSystem K i) ^ (f i)) :
    f = (basisModTorsion K).repr (Additive.ofMul ↑x) := by
  suffices Additive.ofMul ↑x = ∑ i, (f i) • (basisModTorsion K i) by
    rw [← (basisModTorsion K).repr_sum_self f, ← this]
  calc
    Additive.ofMul ↑x
    _ = ∑ i, (f i) • Additive.ofMul ↑(fundSystem K i) := by
          rw [h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hζ, one_mul,
            QuotientGroup.mk_prod, ofMul_prod]; rfl
    _ = ∑ i, (f i) • (basisModTorsion K i) := by
          simp_rw [fundSystem, QuotientGroup.out_eq', ofMul_toMul]

/-- **Dirichlet Unit Theorem**. Any unit `x` of `𝓞 K` can be written uniquely as the product of
a root of unity and powers of the units of the fundamental system `fundSystem`. -/
/-
**NumberField.Units.exist_unique_eq_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x : (NumberFie
ld.RingOfIntegers K)ˣ),   ∃! ζe, x = ↑ζe.1 * ∏ i, NumberField.Units.fundSystem K
 i ^ ζe.2 i
参数：K : Type u_1；x : (NumberField.RingOfIntegers K)ˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N
· 使用定理 `QuotientGroup.mk_mul`：mk_mul (a b : G) : ((a * b : G) : Q) = a * b
· 使用定理 `QuotientGroup.mk_inv`：mk_inv (a : G) : ((a⁻¹ : G) : Q) = (a : Q)⁻¹
· 使用定理 `ofMul_eq_zero`：ofMul_eq_zero {A : Type*} [One A] {x : A} : Additive.ofMu
l x = 0 ↔ x = 1
· 使用定理 `ofMul_mul`：ofMul_mul [Mul α] (x y : α) : ofMul (x * y) = ofMul x + ofMul
 y
· 使用定理 `ofMul_inv`：ofMul_inv [Inv α] (x : α) : ofMul x⁻¹ = -ofMul x
· 使用定理 `QuotientGroup.mk_prod`：mk_prod {G ι : Type*} [CommGroup G] (N : Subgroup
 G) (s : Finset ι) {f : ι -> G} : ((Finset.prod s f : G) : G ⧸ N) = Finset.prod 
s (fun i =>…
· 使用定理 `ofMul_prod`：ofMul_prod (s : Finset ι) (f : ι -> M) : ofMul (∏ i in s, f 
i) = ∑ i in s, ofMul (f i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `QuotientGroup.out_eq'`：out_eq' (a : α ⧸ s) : mk a.out = a
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NumberField.Units.fun_eq_repr`：∀ (K : Type u_1) [inst : Field K] [inst_1
 : NumberField K] {x ζ : (NumberField.RingOfIntegers K)ˣ}   {f : Fin (NumberFiel
d.Units.rank K) → ℤ…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a

--- 原说明 ---
**Dirichlet Unit Theorem**. Any unit `x` of `𝓞 K` can be written uniquely as the
 product of
a root of unity and powers of the units of the fundamental system `fundSystem`.
-/
theorem exist_unique_eq_mul_prod (x : (𝓞 K)ˣ) : ∃! ζe : torsion K × (Fin (rank K) → ℤ),
    x = ζe.1 * ∏ i, (fundSystem K i) ^ (ζe.2 i) := by
  let ζ := x * (∏ i, (fundSystem K i) ^ ((basisModTorsion K).repr (Additive.ofMul ↑x) i))⁻¹
  have h_tors : ζ ∈ torsion K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← ofMul_eq_zero,
      ofMul_mul, ofMul_inv, QuotientGroup.mk_prod, ofMul_prod]
    simp_rw [QuotientGroup.mk_zpow, ofMul_zpow, fundSystem, QuotientGroup.out_eq']
    rw [add_eq_zero_iff_eq_neg, neg_neg]
    exact ((basisModTorsion K).sum_repr (Additive.ofMul ↑x)).symm
  refine ⟨⟨⟨ζ, h_tors⟩, ((basisModTorsion K).repr (Additive.ofMul ↑x) : Fin (rank K) → ℤ)⟩, ?_, ?_⟩
  · simp only [ζ, _root_.inv_mul_cancel_right]
  · rintro ⟨⟨ζ', h_tors'⟩, η⟩ hf
    simp only [ζ, ← fun_eq_repr K h_tors' hf, Prod.mk.injEq, Subtype.mk.injEq, and_true]
    nth_rewrite 1 [hf]
    rw [_root_.mul_inv_cancel_right]

/--
The units of the fundamental system and the torsion of `K` generate the full group of units of `K`.
-/
/-
**NumberField.Units.closure_fundSystem_sup_torsion_eq_top** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],   Subgroup.clo
sure (Set.range (NumberField.Units.fundSystem K)) ⊔ NumberField.Units.torsion K 
= ⊤
参数：K : Type u_1；Set.range (NumberField.Units.fundSystem K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.eq_top_iff'`：eq_top_iff' : H = ⊤ ↔ forall x : G, x in H
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `NumberField.Units.exist_unique_eq_mul_prod`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K] (x : (NumberField.RingOfIntegers K)ˣ),   ∃! ζe, x
 = ↑ζe.1 * ∏ i, NumberField.Unit…
· 使用定理 `Subgroup.mul_mem_sup`：mul_mem_sup {S T : Subgroup G} {x y : G} (hx : x i
n S) (hy : y in T) : x * y in S ⊔ T
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `Subgroup.prod_mem`：∀ {G : Type u_3} [inst : CommGroup G] (K : Subgroup G
) {ι : Type u_4} {t : Finset ι} {f : ι → G},   (∀ c ∈ t, f c ∈ K) → ∏ c ∈ t, f c
 ∈ K
· 使用定理 `Subgroup.zpow_mem`：∀ {G : Type u_1} [inst : Group G] (K : Subgroup G) {x
 : G}, x ∈ K → ∀ (n : ℤ), x ^ n ∈ K
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The units of the fundamental system and the torsion of `K` generate the full gro
up of units of `K`.
-/
theorem closure_fundSystem_sup_torsion_eq_top :
    Subgroup.closure (Set.range (fundSystem K)) ⊔ torsion K = ⊤ := by
  rw [Subgroup.eq_top_iff', sup_comm]
  intro x
  obtain ⟨c, rfl, _⟩ := exist_unique_eq_mul_prod K x
  exact Subgroup.mul_mem_sup (SetLike.coe_mem c.1) <| Subgroup.prod_mem _
    fun i _ ↦ Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

end statements

end NumberField.Units

