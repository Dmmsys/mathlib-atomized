/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.
-/

public section


noncomputable section

namespace Complex

open Set Filter

open scoped Real

/-
**Complex.hasStrictDerivAt_tan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictDerivAt_tan {x : Complex} (h : cos x != 0) : HasStrictDerivAt tan
 (1 / cos x ^ 2) x
参数：h : cos x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.sin_sq_add_cos_sq`：sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 62 条，此处仅展示前 30 条）
-/
theorem hasStrictDerivAt_tan {x : ℂ} (h : cos x ≠ 0) : HasStrictDerivAt tan (1 / cos x ^ 2) x := by
  convert! (hasStrictDerivAt_sin x).div (hasStrictDerivAt_cos x) h using 1
  rw_mod_cast [← sin_sq_add_cos_sq x]
  ring
/-
**Complex.hasDerivAt_tan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasDerivAt_tan {x : Complex} (h : cos x != 0) : HasDerivAt tan (1 / cos x 
^ 2) x
参数：h : cos x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_tan`：hasStrictDerivAt_tan {x : Complex} (h : co
s x != 0) : HasStrictDerivAt tan (1 / cos x ^ 2) x
-/
theorem hasDerivAt_tan {x : ℂ} (h : cos x ≠ 0) : HasDerivAt tan (1 / cos x ^ 2) x :=
  (hasStrictDerivAt_tan h).hasDerivAt

open scoped Topology
/-
**Complex.tendsto_norm_tan_of_cos_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：tendsto_norm_tan_of_cos_eq_zero {x : Complex} (hx : cos x = 0) : Tendsto (
fun x => ‖tan x‖) (𝓝[!=] x) atTop
参数：hx : cos x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.sin_sq_add_cos_sq`：sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1
· 使用定理 `HasDerivAt.tendsto_nhdsNE`：HasDerivAt.tendsto_nhdsNE (h : HasDerivAt f f
' x) (hf' : f' != 0) : Tendsto f (𝓝[!=] x) (𝓝[!=] f x)
· 使用定理 `Complex.hasDerivAt_cos`：hasDerivAt_cos (x : Complex) : HasDerivAt cos (-
sin x) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Filter.Tendsto.pos_mul_atTop`：Filter.Tendsto.pos_mul_atTop {C : 𝕜} (hC :
 0 < C) (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atTop) : Tendsto (fun x => f 
x * g x) l atTop
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `ContinuousWithinAt.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : Seminor
medAddGroup E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α}   {a : α}, 
ContinuousWit…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `Complex.continuous_sin`：continuous_sin : Continuous sin
· 使用定理 `Filter.Tendsto.inv_tendsto_nhdsGT_zero`：Filter.Tendsto.inv_tendsto_nhdsG
T_zero (h : Tendsto f l (𝓝[>] 0)) : Tendsto f⁻¹ l atTop
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_norm_nhdsNE_zero`：∀ {E : Type u_4} [inst : NormedAddGroup E], Fi
lter.Tendsto norm (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 (Set.Ioi 0))
-/
theorem tendsto_norm_tan_of_cos_eq_zero {x : ℂ} (hx : cos x = 0) :
    Tendsto (fun x => ‖tan x‖) (𝓝[≠] x) atTop := by
  simp only [tan_eq_sin_div_cos, norm_div]
  have A : sin x ≠ 0 := fun h => by simpa [*, sq] using sin_sq_add_cos_sq x
  have B : Tendsto cos (𝓝[≠] x) (𝓝[≠] 0) :=
    hx ▸ (hasDerivAt_cos x).tendsto_nhdsNE (neg_ne_zero.2 A)
  exact continuous_sin.continuousWithinAt.norm.pos_mul_atTop (norm_pos_iff.2 A)
    (tendsto_norm_nhdsNE_zero.comp B).inv_tendsto_nhdsGT_zero
/-
**Complex.tendsto_norm_tan_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：tendsto_norm_tan_atTop (k : Int) : Tendsto (fun x => ‖tan x‖) (𝓝[!=] ((2 *
 k + 1) * π / 2 : Complex)) atTop
参数：k : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.tendsto_norm_tan_of_cos_eq_zero`：tendsto_norm_tan_of_cos_eq_zero
 {x : Complex} (hx : cos x = 0) : Tendsto (fun x => ‖tan x‖) (𝓝[!=] x) atTop
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.cos_eq_zero_iff`：cos_eq_zero_iff {θ : Complex} : cos θ = 0 ↔ exi
sts k : Int, θ = (2 * k + 1) * π / 2
-/
theorem tendsto_norm_tan_atTop (k : ℤ) :
    Tendsto (fun x => ‖tan x‖) (𝓝[≠] ((2 * k + 1) * π / 2 : ℂ)) atTop :=
  tendsto_norm_tan_of_cos_eq_zero <| cos_eq_zero_iff.2 ⟨k, rfl⟩

@[simp]
/-
**Complex.continuousAt_tan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuousAt_tan {x : Complex} : ContinuousAt tan x ↔ cos x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_tendsto_nhds_of_tendsto_atTop`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{l : Filter β} [l.NeBot…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Complex.tendsto_norm_tan_of_cos_eq_zero`：tendsto_norm_tan_of_cos_eq_zero
 {x : Complex} (hx : cos x = 0) : Tendsto (fun x => ‖tan x‖) (𝓝[!=] x) atTop
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousAt.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {a : α},   ContinuousAt f a →
 Contin…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Complex.hasDerivAt_tan`：hasDerivAt_tan {x : Complex} (h : cos x != 0) : 
HasDerivAt tan (1 / cos x ^ 2) x
-/
theorem continuousAt_tan {x : ℂ} : ContinuousAt tan x ↔ cos x ≠ 0 := by
  refine ⟨fun hc h₀ => ?_, fun h => (hasDerivAt_tan h).continuousAt⟩
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_norm_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)

@[simp]
/-
**Complex.differentiableAt_tan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiableAt_tan {x : Complex} : DifferentiableAt Complex tan x ↔ cos 
x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.continuousAt_tan`：continuousAt_tan {x : Complex} : ContinuousAt 
tan x ↔ cos x != 0
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
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
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Complex.hasDerivAt_tan`：hasDerivAt_tan {x : Complex} (h : cos x != 0) : 
HasDerivAt tan (1 / cos x ^ 2) x
-/
theorem differentiableAt_tan {x : ℂ} : DifferentiableAt ℂ tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuousAt_tan.1 h.continuousAt, fun h => (hasDerivAt_tan h).differentiableAt⟩

@[simp]
/-
**Complex.deriv_tan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：deriv_tan (x : Complex) : deriv tan x = 1 / cos x ^ 2
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.differentiableAt_tan`：differentiableAt_tan {x : Complex} : Diffe
rentiableAt Complex tan x ↔ cos x != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Complex.hasDerivAt_tan`：hasDerivAt_tan {x : Complex} (h : cos x != 0) : 
HasDerivAt tan (1 / cos x ^ 2) x
-/
theorem deriv_tan (x : ℂ) : deriv tan x = 1 / cos x ^ 2 :=
  if h : cos x = 0 then by
    have : ¬DifferentiableAt ℂ tan x := mt differentiableAt_tan.1 (Classical.not_not.2 h)
    simp [deriv_zero_of_not_differentiableAt this, h, sq]
  else (hasDerivAt_tan h).deriv

@[simp]
/-
**Complex.contDiffAt_tan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：contDiffAt_tan {x : Complex} {n : WithTop Nat∞} : ContDiffAt Complex n tan
 x ↔ cos x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.continuousAt_tan`：continuousAt_tan {x : Complex} : ContinuousAt 
tan x ↔ cos x != 0
· 使用定理 `ContDiffAt.continuousAt`：ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x
) : ContinuousAt f x
· 使用定理 `ContDiffAt.div`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E :
 Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {
f g …
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_sin`：contDiff_sin {n} : ContDiff Complex n sin
· 使用定理 `Complex.contDiff_cos`：contDiff_cos {n} : ContDiff Complex n cos
-/
theorem contDiffAt_tan {x : ℂ} {n : WithTop ℕ∞} : ContDiffAt ℂ n tan x ↔ cos x ≠ 0 :=
  ⟨fun h => continuousAt_tan.1 h.continuousAt, contDiff_sin.contDiffAt.div contDiff_cos.contDiffAt⟩

end Complex

