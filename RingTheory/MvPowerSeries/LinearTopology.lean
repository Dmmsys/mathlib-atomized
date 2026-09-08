/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Data.Finsupp.Interval
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! # Linear topology on the ring of multivariate power series

- `MvPowerSeries.LinearTopology.basis`: the ideals of the ring of multivariate power series
  all coefficients the exponent of which is smaller than some bound vanish.

- `MvPowerSeries.LinearTopology.hasBasis_nhds_zero` :
  the two-sided ideals from `MvPowerSeries.LinearTopology.basis` form a basis
  of neighborhoods of `0` if the topology of `R` is (left and right) linear.

## Instances :

If `R` has a linear topology, then the product topology on `MvPowerSeries σ R`
is a linear topology.

This applies in particular when `R` has the discrete topology.

## Note

If we had an analogue of `PolynomialModule` for power series,
meaning that we could consider the `R⟦X⟧`-module `M⟦X⟧` when `M` is an `R`-module,
then one could prove that `M⟦X⟧` is linearly topologized over `R⟦X⟧`
whenever `M` is linearly topologized over `R`.
To recover the ring case, it would remain to show that the isomorphism between
`Rᵐᵒᵖ⟦X⟧` and `R⟦X⟧ᵐᵒᵖ` identifies their respective actions on `R⟦X⟧`.
(And likewise in the multivariate case.)

-/

@[expose] public section

namespace MvPowerSeries

namespace LinearTopology

open scoped Topology

open Set SetLike Filter

/-- The underlying family for the basis of ideals in a multivariate power series ring. -/
/-
**MvPowerSeries.LinearTopology.basis** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries.Li
nearTopology`。
形式化陈述：basis (σ : Type*) (R : Type*) [Ring R] (Jd : TwoSidedIdeal R × (σ ->₀ Nat)
) : TwoSidedIdeal (MvPowerSeries σ R)
参数：σ : Type*；R : Type*；Jd : TwoSidedIdeal R × (σ ->₀ Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying family for the basis of ideals in a multivariate power series rin
g.
-/
noncomputable def basis (σ : Type*) (R : Type*) [Ring R] (Jd : TwoSidedIdeal R × (σ →₀ ℕ)) :
    TwoSidedIdeal (MvPowerSeries σ R) :=
  TwoSidedIdeal.mk' {f | ∀ e ≤ Jd.2, coeff e f ∈ Jd.1}
    (by simp [coeff_zero])
    (fun hf hg e he ↦ by rw [map_add]; exact add_mem (hf e he) (hg e he))
    (fun {f} hf e he ↦ by simp only [map_neg, neg_mem, hf e he])
    (fun {f g} hg e he ↦ by
      classical
      rw [coeff_mul]
      apply sum_mem
      rintro uv huv
      exact TwoSidedIdeal.mul_mem_left _ _ _
        (hg _ (le_trans (Finset.HasAntidiagonal.antidiagonal.snd_le huv) he)))
    (fun {f g} hf e he ↦ by
      classical
      rw [coeff_mul]
      apply sum_mem
      rintro uv huv
      exact TwoSidedIdeal.mul_mem_right _ _ _
        (hf _ (le_trans (Finset.HasAntidiagonal.antidiagonal.fst_le huv) he)))

variable {σ : Type*} {R : Type*} [Ring R]

set_option backward.isDefEq.respectTransparency false in
/-- A power series `f` belongs to the two-sided ideal `basis σ R ⟨J, d⟩`
if and only if `coeff e f ∈ J` for all `e ≤ d`. -/
/-
**MvPowerSeries.LinearTopology.mem_basis_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerS
eries.LinearTopology`。
形式化陈述：mem_basis_iff {f : MvPowerSeries σ R} {Jd : TwoSidedIdeal R × (σ ->₀ Nat)}
 : f in basis σ R Jd ↔ forall e <= Jd.2, coeff e f in Jd.1
参数：σ ->₀ Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A power series `f` belongs to the two-sided ideal `basis σ R ⟨J, d⟩`
if and only if `coeff e f ∈ J` for all `e ≤ d`.
-/
theorem mem_basis_iff {f : MvPowerSeries σ R} {Jd : TwoSidedIdeal R × (σ →₀ ℕ)} :
    f ∈ basis σ R Jd ↔ ∀ e ≤ Jd.2, coeff e f ∈ Jd.1 := by
  simp [basis]

/-- If `J ≤ K` and `e ≤ d`, then we have the inclusion of two-sided ideals
`basis σ R ⟨J, d⟩ ≤ basis σ R ⟨K, e,>`. -/
/-
**MvPowerSeries.LinearTopology.basis_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries
.LinearTopology`。
形式化陈述：basis_le {Jd Ke : TwoSidedIdeal R × (σ ->₀ Nat)} (hJK : Jd.1 <= Ke.1) (hed
 : Ke.2 <= Jd.2) : basis σ R Jd <= basis σ R Ke
参数：σ ->₀ Nat；hJK : Jd.1 <= Ke.1；hed : Ke.2 <= Jd.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c

--- 原说明 ---
If `J ≤ K` and `e ≤ d`, then we have the inclusion of two-sided ideals
`basis σ R ⟨J, d⟩ ≤ basis σ R ⟨K, e,>`.
-/
theorem basis_le {Jd Ke : TwoSidedIdeal R × (σ →₀ ℕ)} (hJK : Jd.1 ≤ Ke.1) (hed : Ke.2 ≤ Jd.2) :
    basis σ R Jd ≤ basis σ R Ke :=
  fun _ ↦ forall_imp (fun _ h hue ↦ hJK (h (le_trans hue hed)))

set_option backward.isDefEq.respectTransparency false in
/-- `basis σ R ⟨J, d⟩ ≤ basis σ R ⟨K, e⟩` if and only if `J ≤ K` and `e ≤ d`. -/
/-
**MvPowerSeries.LinearTopology.basis_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSe
ries.LinearTopology`。
形式化陈述：basis_le_iff {J K : TwoSidedIdeal R} {d e : σ ->₀ Nat} (hK : K != ⊤) : bas
is σ R ⟨J, d⟩ <= basis σ R ⟨K, e⟩ ↔ J <= K ∧ e <= d
参数：hK : K != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TwoSidedIdeal.coe_mk'`：coe_mk' (carrier : Set R) (zero_mem add_mem neg_m
em mul_mem_left mul_mem_right) : (mk' carrier zero_mem add_mem neg_mem mul_mem_l
eft mul_mem…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.coeff_C`：coeff_C [DecidableEq σ] (n : σ ->₀ Nat) (a : R) :
 coeff n (C a) = if n = 0 then a else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `TwoSidedIdeal.zero_mem`：zero_mem : 0 in I
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MvPowerSeries.LinearTopology.basis_le`：basis_le {Jd Ke : TwoSidedIdeal R
 × (σ ->₀ Nat)} (hJK : Jd.1 <= Ke.1) (hed : Ke.2 <= Jd.2) : basis σ R Jd <= basi
s σ R Ke

--- 原说明 ---
`basis σ R ⟨J, d⟩ ≤ basis σ R ⟨K, e⟩` if and only if `J ≤ K` and `e ≤ d`.
-/
theorem basis_le_iff {J K : TwoSidedIdeal R} {d e : σ →₀ ℕ} (hK : K ≠ ⊤) :
    basis σ R ⟨J, d⟩ ≤ basis σ R ⟨K, e⟩ ↔ J ≤ K ∧ e ≤ d := by
  classical
  constructor
  · simp only [basis, TwoSidedIdeal.le_iff, TwoSidedIdeal.coe_mk', ofPred_subset_ofPred]
    intro h
    constructor
    · intro x hx
      have (d' : _) : coeff d' (C (σ := σ) x) ∈ J := by
        rw [coeff_C]; split_ifs <;> [exact hx; exact J.zero_mem]
      simpa using h (C x) (fun _ _ ↦ this _) _ zero_le
    · by_contra h'
      apply hK
      rw [eq_top_iff]
      intro x _
      have (d') (hd'_le : d' ≤ d) : coeff d' (monomial e x) ∈ J := by
        rw [coeff_monomial]
        split_ifs with hd' <;> [exact (h' (hd' ▸ hd'_le)).elim; exact J.zero_mem]
      simpa using h (monomial e x) this _ le_rfl
  · rintro ⟨hJK, hed⟩
    exact basis_le hJK hed

variable [TopologicalSpace R]

-- We endow MvPowerSeries σ R with the product topology.
open WithPiTopology

set_option backward.isDefEq.respectTransparency false in
/-- If the ring `R` is endowed with a linear topology, then the sets `↑basis σ R (J, d)`,
for `J : TwoSidedIdeal R` which are neighborhoods of `0 : R` and `d : σ →₀ ℕ`,
constitute a basis of neighborhoods of `0 : MvPowerSeries σ R` for the product topology. -/
/-
**MvPowerSeries.LinearTopology.hasBasis_nhds_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvP
owerSeries.LinearTopology`。
形式化陈述：hasBasis_nhds_zero [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] : (𝓝 0
 : Filter (MvPowerSeries σ R)).HasBasis (fun Id : TwoSidedIdeal R × (σ ->₀ Nat) 
=> (Id.1 : Set R) in 𝓝 0) (fun Id => basis _ _ Id)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `Filter.HasBasis.pi_self`：∀ {ι : Type u_1} {α : Type u_3} {κ : Type u_4} 
{f : Filter α} {p : κ → Prop} {s : κ → Set α},   f.HasBasis p s → (Filter.pi fun
 x => f).HasB…
· 使用引理 `IsLinearTopology.hasBasis_twoSidedIdeal`：hasBasis_twoSidedIdeal [IsLinea
rTopology R R] [IsLinearTopology Rᵐᵒᵖ R] : (𝓝 (0 : R)).HasBasis (fun I : TwoSide
dIdeal R => (I : Set R) in 𝓝 …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.LinearTopology.mem_basis_iff`：mem_basis_iff {f : MvPowerSe
ries σ R} {Jd : TwoSidedIdeal R × (σ ->₀ Nat)} : f in basis σ R Jd ↔ forall e <=
 Jd.2, coeff e f in Jd.1
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `Set.finite_Iic`：∀ {α : Type u_1} [inst : Preorder α] [LocallyFiniteOrder
Bot α] (a : α), (Set.Iic a).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `TwoSidedIdeal.coe_mk'`：coe_mk' (carrier : Set R) (zero_mem add_mem neg_m
em mul_mem_left mul_mem_right) : (mk' carrier zero_mem add_mem neg_mem mul_mem_l
eft mul_mem…
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a

--- 原说明 ---
If the ring `R` is endowed with a linear topology, then the sets `↑basis σ R (J,
 d)`,
for `J : TwoSidedIdeal R` which are neighborhoods of `0 : R` and `d : σ →₀ ℕ`,
constitute a basis of neighborhoods of `0 : MvPowerSeries σ R` for the product t
opology.
-/
lemma hasBasis_nhds_zero [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 0 : Filter (MvPowerSeries σ R)).HasBasis
      (fun Id : TwoSidedIdeal R × (σ →₀ ℕ) ↦ (Id.1 : Set R) ∈ 𝓝 0)
      (fun Id ↦ basis _ _ Id) := by
  classical
  rw [nhds_pi]
  refine IsLinearTopology.hasBasis_twoSidedIdeal.pi_self.to_hasBasis ?_ ?_
  · intro ⟨D, I⟩ ⟨hD, hI⟩
    refine ⟨⟨I, Finset.sup hD.toFinset id⟩, hI, fun f hf d hd ↦ ?_⟩
    rw [SetLike.mem_coe, mem_basis_iff] at hf
    convert! hf _ <| Finset.le_sup (hD.mem_toFinset.mpr hd)
  · intro ⟨I, d⟩ hI
    refine ⟨⟨Iic d, I⟩, ⟨finite_Iic d, hI⟩, ?_⟩
    simpa [basis, coeff_apply, Iic, Set.pi] using! subset_rfl

/-- The topology on `MvPowerSeries` is a left linear topology
  when the ring of coefficients has a linear topology. -/
/-
**MvPowerSeries.LinearTopology.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries.LinearT
opology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on `MvPowerSeries` is a left linear topology
  when the ring of coefficients has a linear topology.
-/
instance [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    IsLinearTopology (MvPowerSeries σ R) (MvPowerSeries σ R) :=
  IsLinearTopology.mk_of_hasBasis' _ hasBasis_nhds_zero TwoSidedIdeal.mul_mem_left

/-- The topology on `MvPowerSeries` is a right linear topology
  when the ring of coefficients has a linear topology. -/
/-
**MvPowerSeries.LinearTopology.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries.LinearT
opology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on `MvPowerSeries` is a right linear topology
  when the ring of coefficients has a linear topology.
-/
instance [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    IsLinearTopology (MvPowerSeries σ R)ᵐᵒᵖ (MvPowerSeries σ R) :=
  IsLinearTopology.mk_of_hasBasis' _ hasBasis_nhds_zero (fun J _ _ hg ↦ J.mul_mem_right _ _ hg)
/-
**MvPowerSeries.LinearTopology.isTopologicallyNilpotent_of_constantCoeff** 是 Mat
hlib 中的一个定理，位于命名空间 `MvPowerSeries.LinearTopology`。
形式化陈述：isTopologicallyNilpotent_of_constantCoeff {R : Type*} [CommRing R] [Topolo
gicalSpace R] [IsLinearTopology R R] {f : MvPowerSeries σ R} (hf : IsTopological
lyNilpotent (constantCoeff f)) : IsTopologicallyNilpotent f
参数：hf : IsTopologicallyNilpotent (constantCoeff f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `IsLinearTopology.hasBasis_ideal`：hasBasis_ideal [IsLinearTopology R R] :
 (𝓝 0).HasBasis (fun I : Ideal R => (I : Set R) in 𝓝 0) (fun I : Ideal R => (I :
 Set R))
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent`：coeff_eq_zero_of
_constantCoeff_nilpotent {f : MvPowerSeries σ R} {m : Nat} (hf : constantCoeff f
 ^ m = 0) {d : σ ->₀ Nat} {n : Nat} (hn : m …
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem isTopologicallyNilpotent_of_constantCoeff
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsLinearTopology R R]
    {f : MvPowerSeries σ R} (hf : IsTopologicallyNilpotent (constantCoeff f)) :
    IsTopologicallyNilpotent f := by
  simp_rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto, coeff_zero,
    IsLinearTopology.hasBasis_ideal.tendsto_right_iff]
  intro d I hI
  replace hf := hf.eventually_mem hI
  simp_rw [eventually_atTop, SetLike.mem_coe, ← Ideal.Quotient.eq_zero_iff_mem,
    map_pow, ← coeff_map, ← constantCoeff_map] at hf ⊢
  obtain ⟨N, hN⟩ := hf
  use N + d.degree
  intro n hn
  simpa only [map_pow] using coeff_eq_zero_of_constantCoeff_nilpotent (hN N le_rfl) hn

/-- Assuming the base ring has a linear topology, the powers of a `MvPowerSeries` converge to 0
iff its constant coefficient is topologically nilpotent.

See also `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent`. -/
/-
**MvPowerSeries.LinearTopology.isTopologicallyNilpotent_iff_constantCoeff** 是 Ma
thlib 中的一个定理，位于命名空间 `MvPowerSeries.LinearTopology`。
形式化陈述：isTopologicallyNilpotent_iff_constantCoeff {R : Type*} [CommRing R] [Topol
ogicalSpace R] [IsLinearTopology R R] (f : MvPowerSeries σ R) : Tendsto (fun n :
 Nat => f ^ n) atTop (nhds 0) ↔ IsTopologicallyNilpotent (constantCoeff f)
参数：f : MvPowerSeries σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `MvPowerSeries.WithPiTopology.continuous_constantCoeff`：continuous_consta
ntCoeff [Semiring R] : Continuous (constantCoeff (σ
· 使用定理 `MvPowerSeries.constantCoeff_zero`：constantCoeff_zero : constantCoeff (0 
: MvPowerSeries σ R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPowerSeries.LinearTopology.isTopologicallyNilpotent_of_constantCoeff`：
isTopologicallyNilpotent_of_constantCoeff {R : Type*} [CommRing R] [TopologicalS
pace R] [IsLinearTopology R R] {f : MvPowerSeries σ R} (hf :…

--- 原说明 ---
Assuming the base ring has a linear topology, the powers of a `MvPowerSeries` co
nverge to 0
iff its constant coefficient is topologically nilpotent.

See also `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoef
f_isNilpotent`.
-/
theorem isTopologicallyNilpotent_iff_constantCoeff
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsLinearTopology R R] (f : MvPowerSeries σ R) :
    Tendsto (fun n : ℕ => f ^ n) atTop (nhds 0) ↔
      IsTopologicallyNilpotent (constantCoeff f) := by
  refine ⟨fun H ↦ ?_, isTopologicallyNilpotent_of_constantCoeff⟩
  replace H : Tendsto (fun n ↦ constantCoeff (f ^ n)) atTop (nhds 0) :=
    continuous_constantCoeff R |>.tendsto' 0 0 constantCoeff_zero |>.comp H
  simpa only [map_pow] using! H

end LinearTopology

end MvPowerSeries

