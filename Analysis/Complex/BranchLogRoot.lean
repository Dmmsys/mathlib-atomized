/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-!
# Branches of logarithm and `n`th root on simply connected domains

In this file we prove that for a function `g : X → ℂ` defined on a locally path connected space
that is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
there exist continuous branches of `log (g z)` and `ⁿ√(g z)` on `U`.
-/

public section

open Set

namespace Complex

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X] {U : Set X}

/-- If `g : X → ℂ` defined on a locally path connected space
is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
then there exists a continuous branch of `log ∘ g` on `U`.
More precisely, there exists a function `f : X → ℂ` continuous on `U`
such that `exp (f x) = g x` for all `x ∈ U`. -/
/-
**Complex.exists_continuousOn_eqOn_exp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exists_continuousOn_eqOn_exp_comp (hUc : IsSimplyConnected U) (hUo : IsOpe
n U) {g : X -> Complex} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) : exists f :
 X -> Complex, ContinuousOn f U ∧ EqOn (exp ∘ f) g U
参数：hUc : IsSimplyConnected U；hUo : IsOpen U；hgc : ContinuousOn g U；hU₀ : 0 ∉ g '
' U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimplyConnected.simplyConnectedSpace`：IsSimplyConnected.simplyConnecte
dSpace {s : Set X} (hs : IsSimplyConnected s) : SimplyConnectedSpace s
· 使用定理 `IsOpen.locallyPathConnectedSpace`：IsOpen.locallyPathConnectedSpace {U : 
Set X} (h : IsOpen U) : LocallyPathConnectedSpace U
· 使用定理 `IsSimplyConnected.nonempty`：IsSimplyConnected.nonempty {s : Set X} (hs :
 IsSimplyConnected s) : s.Nonempty
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `IsCoveringMapOn.existsUnique_continuousMap_lifts`：IsCoveringMapOn.exists
Unique_continuousMap_lifts [SimplyConnectedSpace A] [LocallyPathConnectedSpace A
] {s : Set X} (cov : IsCoveringMapOn p…
· 使用定理 `Complex.isCoveringMapOn_exp`：isCoveringMapOn_exp : IsCoveringMapOn Compl
ex.exp {0}ᶜ
· 使用定理 `Complex.exp_log`：exp_log {x : Complex} (hx : x != 0) : exp (log x) = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
If `g : X → ℂ` defined on a locally path connected space
is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
then there exists a continuous branch of `log ∘ g` on `U`.
More precisely, there exists a function `f : X → ℂ` continuous on `U`
such that `exp (f x) = g x` for all `x ∈ U`.
-/
theorem exists_continuousOn_eqOn_exp_comp (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : X → ℂ} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) :
    ∃ f : X → ℂ, ContinuousOn f U ∧ EqOn (exp ∘ f) g U := by
  classical
  have := hUc.simplyConnectedSpace
  have := hUo.locallyPathConnectedSpace
  rcases hUc.nonempty with ⟨x₀, hx₀U⟩
  have hx₀ : g x₀ ≠ 0 := ne_of_mem_of_not_mem (mem_image_of_mem g hx₀U) hU₀
  lift x₀ to U using hx₀U
  rcases isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    ⟨U.domRestrict g, continuousOn_iff_continuous_domRestrict.mp hgc⟩ (exp_log hx₀)
    (fun x ↦ ne_of_mem_of_not_mem (mem_image_of_mem g x.2) hU₀) with ⟨f, ⟨-, hf⟩, -⟩
  obtain ⟨g, hg⟩ : ∃ g : X → ℂ, ∀ z : U, g z = f z :=
    ⟨fun z ↦ if hz : z ∈ U then f ⟨z, hz⟩ else 0, by simp⟩
  refine ⟨g, ?hg_cont, ?hg_inv⟩
  case hg_cont =>
    rw [continuousOn_iff_continuous_domRestrict]
    convert! map_continuous f
    ext z
    exact hg z
  case hg_inv =>
    intro x hx
    lift x to U using hx
    simpa [hg] using congr($hf x)

/-- If `g : X → ℂ` defined on a locally path connected space
is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
then for any `n ≠ 0`, there exists a continuous branch of `ⁿ√g` on `U`.
More precisely, there exists a function `f : X → ℂ` continuous on `U`
such that `(f x) ^ n = g x` for all `x`. -/
/-
**Complex.exists_continuousOn_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exists_continuousOn_pow_eq (hUc : IsSimplyConnected U) (hUo : IsOpen U) {g
 : X -> Complex} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) {n : Nat} (hn : n !
= 0) : exists f : X -> Complex, ContinuousOn f U ∧ forall x, f x ^ n = g x
参数：hUc : IsSimplyConnected U；hUo : IsOpen U；hgc : ContinuousOn g U；hU₀ : 0 ∉ g '
' U；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.exists_continuousOn_eqOn_exp_comp`：exists_continuousOn_eqOn_exp_
comp (hUc : IsSimplyConnected U) (hUo : IsOpen U) {g : X -> Complex} (hgc : Cont
inuousOn g U) (hU₀ : 0 ∉ g '' U…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Set.domRestrict_piecewise`：domRestrict_piecewise (f g : α -> β) (s : Set
 α) [forall x, Decidable (x in s)] : s.domRestrict (piecewise s f g) = s.domRest
rict f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousOn.cexp`：ContinuousOn.cexp (h : ContinuousOn f s) : Continuous
On (fun y => exp (f y)) s
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Continuous.div_const`：Continuous.div_const (hf : Continuous f) (y : G₀) 
: Continuous fun x => f x / y
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.piecewise.congr_simp`：∀ {α : Type u} {β : α → Sort v} (s s_1 : Set α
),   s = s_1 →     ∀ (f f_1 : (i : α) → β i),       f = f_1 →         ∀ (g g_1 :
 (i : α) → β i…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Complex.cpow_one`：cpow_one (x : Complex) : x ^ (1 : Complex) = x

--- 原说明 ---
If `g : X → ℂ` defined on a locally path connected space
is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
then for any `n ≠ 0`, there exists a continuous branch of `ⁿ√g` on `U`.
More precisely, there exists a function `f : X → ℂ` continuous on `U`
such that `(f x) ^ n = g x` for all `x`.
-/
theorem exists_continuousOn_pow_eq (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : X → ℂ} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) {n : ℕ} (hn : n ≠ 0) :
    ∃ f : X → ℂ, ContinuousOn f U ∧ ∀ x, f x ^ n = g x := by
  classical
  rcases exists_continuousOn_eqOn_exp_comp hUc hUo hgc hU₀ with ⟨f, hfc, hf⟩
  refine ⟨U.piecewise (exp <| f · / n) (g · ^ (1 / n : ℂ)), ?_, fun z ↦ ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict, domRestrict_piecewise,
      ← continuousOn_iff_continuous_domRestrict]
    fun_prop
  · by_cases hz : z ∈ U
    · simp [hz, ← exp_nat_mul, mul_div_cancel₀ (b := ↑n) (f z) (mod_cast hn), ← hf hz,
        Function.comp_apply]
    · simp [hz, ← cpow_mul_nat, hn]

namespace UnitDisc

/-- If `g : X → 𝔻` defined on a locally path connected space
is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
then for any `n ≠ 0`, there exists a continuous branch of `ⁿ√g` on `U`.
More precisely, there exists a function `f : X → 𝔻` continuous on `U`
such that `(f x) ^ n = g x` for all `x`. -/
/-
**Complex.UnitDisc.exists_continuousOn_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex
.UnitDisc`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [LocallyPathConnectedSpace X]
 {U : Set X},   IsSimplyConnected U →     IsOpen U →       ∀ {g : X → Complex.Un
itDisc},         ContinuousOn g U → 0 ∉ g '' U → ∀ (n : ℕ+), ∃ f, ContinuousOn f
 U ∧ ∀ (x : X), f x ^ n = g x
参数：n : ℕ+；x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.exists_continuousOn_pow_eq`：exists_continuousOn_pow_eq (hUc : Is
SimplyConnected U) (hUo : IsOpen U) {g : X -> Complex} (hgc : ContinuousOn g U) 
(hU₀ : 0 ∉ g '' U) {n : …
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `Complex.UnitDisc.continuous_coe`：continuous_coe : Continuous ((↑) : 𝔻 ->
 Complex)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `PNat.ne_zero`：ne_zero (n : Nat+) : (n : Nat) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_lt_one_iff_of_nonneg`：pow_lt_one_iff_of_nonneg (ha : 0 <= a) (hn : n
 != 0) : a ^ n < 1 ↔ a < 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.UnitDisc.norm_lt_one`：norm_lt_one (z : 𝔻) : ‖(z : Complex)‖ < 1
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Complex.UnitDisc.instCanLiftCoeLtRealNormOfNat`：CanLift ℂ Complex.UnitDi
sc Complex.UnitDisc.coe fun x => ‖x‖ < 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsEmbedding.continuousOn_iff`：Topology.IsEmbedding.continuousOn
_iff {f : α -> β} {g : β -> γ} (hg : IsEmbedding g) {s : Set α} : ContinuousOn f
 s ↔ ContinuousOn (g ∘ f) s
· 使用定理 `Complex.UnitDisc.isEmbedding_coe`：isEmbedding_coe : Topology.IsEmbedding
 ((↑) : 𝔻 -> Complex)

--- 原说明 ---
If `g : X → 𝔻` defined on a locally path connected space
is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
then for any `n ≠ 0`, there exists a continuous branch of `ⁿ√g` on `U`.
More precisely, there exists a function `f : X → 𝔻` continuous on `U`
such that `(f x) ^ n = g x` for all `x`.
-/
protected theorem exists_continuousOn_pow_eq
    (hUc : IsSimplyConnected U) (hUo : IsOpen U) {g : X → 𝔻}
    (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) (n : ℕ+) :
    ∃ f : X → 𝔻, ContinuousOn f U ∧ ∀ x, f x ^ n = g x := by
  rcases exists_continuousOn_pow_eq hUc hUo
    (continuous_coe.comp_continuousOn hgc)
    (by simpa using hU₀) n.ne_zero with ⟨f, hfc, hf⟩
  suffices ∀ x, ‖f x‖ < 1 by
    lift f to X → 𝔻 using this
    refine ⟨f, isEmbedding_coe.continuousOn_iff.mpr hfc, fun x ↦ ?_⟩
    simpa only [← coe_pow, Function.comp_apply, coe_inj] using hf x
  intro x
  rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) n.ne_zero, ← norm_pow, hf]
  exact (g x).norm_lt_one

end UnitDisc

end Complex

