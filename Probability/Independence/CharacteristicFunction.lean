/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Links between independence and characteristic function

Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. More specifically, prove this in Hilbert spaces for
two variables and a finite family of variables. We prove the analogous statements in Banach spaces,
with an arbitrary Lp norm, for the dual characteristic function.
-/

public section

namespace ProbabilityTheory

open MeasureTheory WithLp Finset
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

section IndepFun

variable [IsFiniteMeasure P] {E F : Type*}
  {mE : MeasurableSpace E} [NormedAddCommGroup E]
  [BorelSpace E] [SecondCountableTopology E]
  {mF : MeasurableSpace F} [NormedAddCommGroup F] [CompleteSpace F]
  [BorelSpace F] [SecondCountableTopology F]
  {X : Ω → E} {Y : Ω → F}

section InnerProductSpace

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-
**ProbabilityTheory.IndepFun.charFun_map_add_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [M
easureTheory.IsFiniteMeasure P] {E : Type u_2}   {mE : MeasurableSpace E} [inst 
: NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] {X : Ω → E}  
 [inst_3 : InnerProductSpace ℝ E] {Y : Ω → E},   AEMeasurable X P →     AEMeasur
able Y P →       ProbabilityTheory.IndepFun X Y P →         MeasureTheory.charFu
n (MeasureTheory.Measure.map (X + Y) P) =           MeasureTheory.charFun (Measu
reTheory.Measure.map X P) * MeasureTheory.charFun (MeasureTheory.Measure.map Y P
)
参数：MeasureTheory.Measure.map (X + Y) P；MeasureTheory.Measure.map X P；MeasureTheo
ry.Measure.map Y P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IndepFun.map_add_eq_map_conv_map₀`：∀ {Ω : Type u_7} {m
Ω : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M : Type u_10} [inst : Add
Monoid M]   [inst_1 : MeasurableSpace M] …
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MeasureTheory.charFun_conv`：charFun_conv [IsFiniteMeasure μ] [IsFiniteMe
asure ν] (t : E) : charFun (μ ∗ ν) t = charFun μ t * charFun ν t
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
-/
lemma IndepFun.charFun_map_add_eq_mul {Y : Ω → E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFun (P.map (X + Y)) = charFun (P.map X) * charFun (P.map Y) := by
  ext t
  rw [hXY.map_add_eq_map_conv_map₀ mX mY, charFun_conv, Pi.mul_apply]
/-
**ProbabilityTheory.IndepFun.charFun_map_fun_add_eq_mul** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [M
easureTheory.IsFiniteMeasure P] {E : Type u_2}   {mE : MeasurableSpace E} [inst 
: NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] {X : Ω → E}  
 [inst_3 : InnerProductSpace ℝ E] {Y : Ω → E},   AEMeasurable X P →     AEMeasur
able Y P →       ProbabilityTheory.IndepFun X Y P →         MeasureTheory.charFu
n (MeasureTheory.Measure.map (fun ω => X ω + Y ω) P) =           MeasureTheory.c
harFun (MeasureTheory.Measure.map X P) * MeasureTheory.charFun (MeasureTheory.Me
asure.map Y P)
参数：MeasureTheory.Measure.map (fun ω => X ω + Y ω) P；MeasureTheory.Measure.map X 
P；MeasureTheory.Measure.map Y P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.charFun_map_add_eq_mul`：∀ {Ω : Type u_1} {mΩ 
: MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasur
e P] {E : Type u_2}   {mE : MeasurableS…
-/
lemma IndepFun.charFun_map_fun_add_eq_mul {Y : Ω → E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFun (P.map (fun ω ↦ X ω + Y ω)) = charFun (P.map X) * charFun (P.map Y) :=
  hXY.charFun_map_add_eq_mul mX mY
/-
**ProbabilityTheory.charFun_map_add_prod_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：charFun_map_add_prod_eq_mul {μ ν : Measure E} [IsProbabilityMeasure μ] [Is
ProbabilityMeasure ν] : charFun ((μ.prod ν).map (fun p => p.1 + p.2)) = charFun 
μ * charFun ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IndepFun.charFun_map_fun_add_eq_mul`：∀ {Ω : Type u_1} 
{mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMe
asure P] {E : Type u_2}   {mE : MeasurableS…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用引理 `ProbabilityTheory.indepFun_prod`：indepFun_prod (mX : Measurable X) (mY :
 Measurable Y) : (fun ω => X ω.1) ⟂ᵢ[μ.prod ν] (fun ω => Y ω.2)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.measurePreserving_fst`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure 
α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.measurePreserving_snd`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure 
α}   {ν : MeasureTheory.M…
-/
lemma charFun_map_add_prod_eq_mul {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    charFun ((μ.prod ν).map (fun p ↦ p.1 + p.2)) = charFun μ * charFun ν := by
  rw [IndepFun.charFun_map_fun_add_eq_mul, measurePreserving_fst.map_eq,
    measurePreserving_snd.map_eq]
  any_goals fun_prop
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

/-- Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. This is the version for Hilbert spaces, see
`indepFun_iff_charFunDual_prod` for the Banach space version. -/
/-
**ProbabilityTheory.indepFun_iff_charFun_prod** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：indepFun_iff_charFun_prod [CompleteSpace E] (hX : AEMeasurable X P) (hY : 
AEMeasurable Y P) : X ⟂ᵢ[P] Y ↔ forall t, charFun (P.map (fun ω => toLp 2 (X ω, 
Y ω))) t = charFun (P.map X) t.ofLp.1 * charFun (P.map Y) t.ofLp.2
参数：hX : AEMeasurable X P；hY : AEMeasurable Y P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`：indepFun_iff_ma
p_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsFi
niteMeasure μ] (hf : AEMeasurable f μ) (hg : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.charFun_eq_prod_iff`：charFun_eq_prod_iff {μ : Measure E} {
ν : Measure F} {ξ : Measure (E × F)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [Is
FiniteMeasure ξ] : (for…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `WithLp.measurable_toLp`：measurable_toLp : Measurable (@toLp p X)
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two random variables are independent if and only if their joint characteristic f
unction is equal
to the product of the characteristic functions. This is the version for Hilbert 
spaces, see
`indepFun_iff_charFunDual_prod` for the Banach space version.
-/
lemma indepFun_iff_charFun_prod [CompleteSpace E] (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ ∀ t, charFun (P.map (fun ω ↦ toLp 2 (X ω, Y ω))) t =
      charFun (P.map X) t.ofLp.1 * charFun (P.map Y) t.ofLp.2 := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← charFun_eq_prod_iff,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), Function.comp_def]

end InnerProductSpace

section NormedSpace

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-
**ProbabilityTheory.IndepFun.charFunDual_map_add_eq_mul** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [M
easureTheory.IsFiniteMeasure P] {E : Type u_2}   {mE : MeasurableSpace E} [inst 
: NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] {X : Ω → E}  
 [inst_3 : NormedSpace ℝ E] {Y : Ω → E},   AEMeasurable X P →     AEMeasurable Y
 P →       ProbabilityTheory.IndepFun X Y P →         MeasureTheory.charFunDual 
(MeasureTheory.Measure.map (X + Y) P) =           MeasureTheory.charFunDual (Mea
sureTheory.Measure.map X P) *             MeasureTheory.charFunDual (MeasureTheo
ry.Measure.map Y P)
参数：MeasureTheory.Measure.map (X + Y) P；MeasureTheory.Measure.map X P；MeasureTheo
ry.Measure.map Y P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IndepFun.map_add_eq_map_conv_map₀`：∀ {Ω : Type u_7} {m
Ω : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M : Type u_10} [inst : Add
Monoid M]   [inst_1 : MeasurableSpace M] …
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MeasureTheory.charFunDual_conv`：charFunDual_conv {μ ν : Measure E} [IsFi
niteMeasure μ] [IsFiniteMeasure ν] (L : StrongDual Real E) : charFunDual (μ ∗ ν)
 L = charFunDual μ L…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
-/
lemma IndepFun.charFunDual_map_add_eq_mul {Y : Ω → E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFunDual (P.map (X + Y)) = charFunDual (P.map X) * charFunDual (P.map Y) := by
  ext L
  rw [hXY.map_add_eq_map_conv_map₀ mX mY, charFunDual_conv, Pi.mul_apply]
/-
**ProbabilityTheory.IndepFun.charFunDual_map_fun_add_eq_mul** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [M
easureTheory.IsFiniteMeasure P] {E : Type u_2}   {mE : MeasurableSpace E} [inst 
: NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] {X : Ω → E}  
 [inst_3 : NormedSpace ℝ E] {Y : Ω → E},   AEMeasurable X P →     AEMeasurable Y
 P →       ProbabilityTheory.IndepFun X Y P →         MeasureTheory.charFunDual 
(MeasureTheory.Measure.map (fun ω => X ω + Y ω) P) =           MeasureTheory.cha
rFunDual (MeasureTheory.Measure.map X P) *             MeasureTheory.charFunDual
 (MeasureTheory.Measure.map Y P)
参数：MeasureTheory.Measure.map (fun ω => X ω + Y ω) P；MeasureTheory.Measure.map X 
P；MeasureTheory.Measure.map Y P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.charFunDual_map_add_eq_mul`：∀ {Ω : Type u_1} 
{mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMe
asure P] {E : Type u_2}   {mE : MeasurableS…
-/
lemma IndepFun.charFunDual_map_fun_add_eq_mul {Y : Ω → E}
    (mX : AEMeasurable X P) (mY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y) :
    charFunDual (P.map (fun ω ↦ X ω + Y ω)) = charFunDual (P.map X) * charFunDual (P.map Y) :=
  hXY.charFunDual_map_add_eq_mul mX mY
/-
**ProbabilityTheory.charFunDual_map_add_prod_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：charFunDual_map_add_prod_eq_mul {μ ν : Measure E} [IsProbabilityMeasure μ]
 [IsProbabilityMeasure ν] : charFunDual ((μ.prod ν).map (fun p => p.1 + p.2)) = 
charFunDual μ * charFunDual ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IndepFun.charFunDual_map_fun_add_eq_mul`：∀ {Ω : Type u
_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsFini
teMeasure P] {E : Type u_2}   {mE : MeasurableS…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用引理 `ProbabilityTheory.indepFun_prod`：indepFun_prod (mX : Measurable X) (mY :
 Measurable Y) : (fun ω => X ω.1) ⟂ᵢ[μ.prod ν] (fun ω => Y ω.2)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.measurePreserving_fst`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure 
α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.measurePreserving_snd`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure 
α}   {ν : MeasureTheory.M…
-/
lemma charFunDual_map_add_prod_eq_mul {μ ν : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    charFunDual ((μ.prod ν).map (fun p ↦ p.1 + p.2)) = charFunDual μ * charFunDual ν := by
  rw [IndepFun.charFunDual_map_fun_add_eq_mul, measurePreserving_fst.map_eq,
    measurePreserving_snd.map_eq]
  any_goals fun_prop
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

variable [CompleteSpace E]

/-- Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. This is the version for Banach spaces, see
`indepFun_iff_charFun_prod` for the Hilbert space version. -/
/-
**ProbabilityTheory.indepFun_iff_charFunDual_prod** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：indepFun_iff_charFunDual_prod (hX : AEMeasurable X P) (hY : AEMeasurable Y
 P) : X ⟂ᵢ[P] Y ↔ forall L, charFunDual (P.map (fun ω => (X ω, Y ω))) L = charFu
nDual (P.map X) (L.comp (.inl Real E F)) * charFunDual (P.map Y) (L.comp (.inr R
eal E F))
参数：hX : AEMeasurable X P；hY : AEMeasurable Y P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`：indepFun_iff_ma
p_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsFi
niteMeasure μ] (hf : AEMeasurable f μ) (hg : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.charFunDual_eq_prod_iff`：charFunDual_eq_prod_iff [BorelSpa
ce F] [SecondCountableTopology F] [CompleteSpace E] [CompleteSpace F] {ξ : Measu
re (E × F)} [IsFiniteMeasur…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two random variables are independent if and only if their joint characteristic f
unction is equal
to the product of the characteristic functions. This is the version for Banach s
paces, see
`indepFun_iff_charFun_prod` for the Hilbert space version.
-/
lemma indepFun_iff_charFunDual_prod (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ ∀ L, charFunDual (P.map (fun ω ↦ (X ω, Y ω))) L =
      charFunDual (P.map X) (L.comp (.inl ℝ E F)) *
      charFunDual (P.map Y) (L.comp (.inr ℝ E F)) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← charFunDual_eq_prod_iff]

/-- Two random variables are independent if and only if their joint characteristic function is equal
to the product of the characteristic functions. This is `indepFun_iff_charFunDual_prod` for
`WithLp`. See `indepFun_iff_charFun_prod` for the Hilbert space version. -/
/-
**ProbabilityTheory.indepFun_iff_charFunDual_prod'** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：indepFun_iff_charFunDual_prod' (hX : AEMeasurable X P) (hY : AEMeasurable 
Y P) : X ⟂ᵢ[P] Y ↔ forall L, charFunDual (P.map (fun ω => toLp p (X ω, Y ω))) L 
= charFunDual (P.map X) (L.comp ((prodContinuousLinearEquiv p Real E F).symm.toC
ontinuousLinearMap.comp (.inl Real E F))) * charFunDual (P.map Y) (L.comp ((prod
ContinuousLinearEquiv p Real E F).symm.toContinuousLinearMap.comp (.inr Real E F
)))
参数：hX : AEMeasurable X P；hY : AEMeasurable Y P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`：indepFun_iff_ma
p_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsFi
niteMeasure μ] (hf : AEMeasurable f μ) (hg : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.charFunDual_eq_prod_iff'`：charFunDual_eq_prod_iff' (p : Re
al>=0∞) [Fact (1 <= p)] [BorelSpace F] [SecondCountableTopology F] [CompleteSpac
e E] [CompleteSpace F] {ξ : …
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `WithLp.measurable_toLp`：measurable_toLp : Measurable (@toLp p X)
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two random variables are independent if and only if their joint characteristic f
unction is equal
to the product of the characteristic functions. This is `indepFun_iff_charFunDua
l_prod` for
`WithLp`. See `indepFun_iff_charFun_prod` for the Hilbert space version.
-/
lemma indepFun_iff_charFunDual_prod' (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ ∀ L, charFunDual (P.map (fun ω ↦ toLp p (X ω, Y ω))) L =
      charFunDual (P.map X) (L.comp
        ((prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inl ℝ E F))) *
      charFunDual (P.map Y) (L.comp
        ((prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inr ℝ E F))) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← charFunDual_eq_prod_iff' p,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), Function.comp_def]

end NormedSpace

end IndepFun

section iIndepFun

variable {ι : Type*} {s : Finset ι}

section Sum

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → E}

/-
**ProbabilityTheory.iIndepFun.charFunDual_map_finsetSum_eq_prod** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} {s : Finset ι} {E : Type u_3}   [inst : MeasurableSpace E] [inst_1 
: NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → 
E}   [inst_4 : NormedSpace ℝ E],   (∀ i ∈ s, AEMeasurable (X i) P) →     Probabi
lityTheory.iIndepFun (s.restrict X) P →       MeasureTheory.charFunDual (Measure
Theory.Measure.map (∑ i ∈ s, X i) P) =         ∏ i ∈ s, MeasureTheory.charFunDua
l (MeasureTheory.Measure.map (X i) P)
参数：∀ i ∈ s, AEMeasurable (X i) P；s.restrict X；MeasureTheory.Measure.map (∑ i ∈ s
, X i) P；MeasureTheory.Measure.map (X i) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type 
u_10}   {m : (i : ι) → MeasurableSpace…
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.map_const`：map_const (μ : Measure α) (c : β) : μ.m
ap (fun _ => c) = (μ Set.univ) • dirac c
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `MeasureTheory.charFunDual_dirac`：charFunDual_dirac [OpensMeasurableSpace
 E] {x : E} (L : StrongDual Real E) : charFunDual (Measure.dirac x) L = cexp (L 
x * I)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
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
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `ProbabilityTheory.IndepFun.charFunDual_map_add_eq_mul`：∀ {Ω : Type u_1} 
{mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMe
asure P] {E : Type u_2}   {mE : MeasurableS…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.aemeasurable_sum`：∀ {M : Type u_2} {ι : Type u_3} {α : Type u_4} 
[inst : AddCommMonoid M] [inst_1 : MeasurableSpace M] [MeasurableAdd₂ M]   {m : 
MeasurableSpa…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
（共 54 条，此处仅展示前 30 条）
-/
lemma iIndepFun.charFunDual_map_finsetSum_eq_prod [NormedSpace ℝ E]
    (mX : ∀ i ∈ s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFunDual (P.map (∑ i ∈ s, X i)) = ∏ i ∈ s, charFunDual (P.map (X i)) := by
  classical
  have := hX.isProbabilityMeasure
  induction s using Finset.induction with
  | empty => ext; simp [show (0 : Ω → E) = fun _ ↦ 0 from rfl]
  | insert i s hi hs =>
    rw [Finset.sum_insert hi, IndepFun.charFunDual_map_add_eq_mul, Finset.prod_insert hi, hs]
    · exact fun i hi ↦ (mX i (mem_insert_of_mem hi))
    · exact hX.precomp (g := fun x : s ↦ ⟨x.1, mem_insert_of_mem x.2⟩) (fun _ ↦ by simp)
    · exact mX i (mem_insert_self i s)
    · exact Finset.aemeasurable_sum s (fun i hi ↦ (mX i (mem_insert_of_mem hi)))
    symm
    convert!
      iIndepFun.indepFun_finsetSum_of_notMem₀ (i := ⟨i, mem_insert_self i s⟩) (f :=
        fun (x : (insert i s : Finset ι)) ↦ X x.1) (s := {x | x.1 ∈ s}) hX (fun i ↦ (mX i.1 i.2))
        (by simpa)
    let e : ((insert i s) : Finset ι) → ι := Subtype.val
    convert! (Finset.sum_of_injOn Subtype.val ?_ ?_ ?_ ?_).symm
    · simp
    · intro _ _; grind
    · simp; grind
    · grind

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFunDual_map_finset_sum_eq_prod := iIndepFun.charFunDual_map_finsetSum_eq_prod
/-
**ProbabilityTheory.iIndepFun.charFunDual_map_sum_eq_prod** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} {E : Type u_3}   [inst : MeasurableSpace E] [inst_1 : NormedAddComm
Group E] [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → E}   [inst_4 : 
Fintype ι] [inst_5 : NormedSpace ℝ E],   (∀ (i : ι), AEMeasurable (X i) P) →    
 ProbabilityTheory.iIndepFun X P →       MeasureTheory.charFunDual (MeasureTheor
y.Measure.map (∑ i, X i) P) =         ∏ i, MeasureTheory.charFunDual (MeasureThe
ory.Measure.map (X i) P)
参数：∀ (i : ι), AEMeasurable (X i) P；MeasureTheory.Measure.map (∑ i, X i) P；Measur
eTheory.Measure.map (X i) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.charFunDual_map_finsetSum_eq_prod`：∀ {Ω : Ty
pe u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2} {s
 : Finset ι} {E : Type u_3}   [inst : MeasurableSpa…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProbabilityTheory.iIndepFun.restrict`：∀ {Ω : Type u_1} {ι : Type u_2} {_
mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type u_10}   {m :
 (i : ι) → MeasurableSpace…
-/
lemma iIndepFun.charFunDual_map_sum_eq_prod [Fintype ι] [NormedSpace ℝ E]
    (mX : ∀ i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFunDual (P.map (∑ i, X i)) = ∏ i, charFunDual (P.map (X i)) :=
  (hX.restrict _).charFunDual_map_finsetSum_eq_prod (by simpa)
/-
**ProbabilityTheory.iIndepFun.charFunDual_map_fun_finsetSum_eq_prod** 是 Mathlib 
中的一个定理，位于命名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} {s : Finset ι} {E : Type u_3}   [inst : MeasurableSpace E] [inst_1 
: NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → 
E}   [inst_4 : NormedSpace ℝ E],   (∀ i ∈ s, AEMeasurable (X i) P) →     Probabi
lityTheory.iIndepFun (s.restrict X) P →       MeasureTheory.charFunDual (Measure
Theory.Measure.map (fun ω => ∑ i ∈ s, X i ω) P) =         ∏ i ∈ s, MeasureTheory
.charFunDual (MeasureTheory.Measure.map (X i) P)
参数：∀ i ∈ s, AEMeasurable (X i) P；s.restrict X；MeasureTheory.Measure.map (fun ω =
> ∑ i ∈ s, X i ω) P；MeasureTheory.Measure.map (X i) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.iIndepFun.charFunDual_map_finsetSum_eq_prod`：∀ {Ω : Ty
pe u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2} {s
 : Finset ι} {E : Type u_3}   [inst : MeasurableSpa…
-/
lemma iIndepFun.charFunDual_map_fun_finsetSum_eq_prod [NormedSpace ℝ E]
    (mX : ∀ i ∈ s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFunDual (P.map (fun ω ↦ ∑ i ∈ s, X i ω)) = ∏ i ∈ s, charFunDual (P.map (X i)) := by
  convert! hX.charFunDual_map_finsetSum_eq_prod mX
  simp

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFunDual_map_fun_finset_sum_eq_prod :=
  iIndepFun.charFunDual_map_fun_finsetSum_eq_prod
/-
**ProbabilityTheory.iIndepFun.charFunDual_map_fun_sum_eq_prod** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} {E : Type u_3}   [inst : MeasurableSpace E] [inst_1 : NormedAddComm
Group E] [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → E}   [inst_4 : 
Fintype ι] [inst_5 : NormedSpace ℝ E],   (∀ (i : ι), AEMeasurable (X i) P) →    
 ProbabilityTheory.iIndepFun X P →       MeasureTheory.charFunDual (MeasureTheor
y.Measure.map (fun ω => ∑ i, X i ω) P) =         ∏ i, MeasureTheory.charFunDual 
(MeasureTheory.Measure.map (X i) P)
参数：∀ (i : ι), AEMeasurable (X i) P；MeasureTheory.Measure.map (fun ω => ∑ i, X i 
ω) P；MeasureTheory.Measure.map (X i) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.charFunDual_map_fun_finsetSum_eq_prod`：∀ {Ω 
: Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2
} {s : Finset ι} {E : Type u_3}   [inst : MeasurableSpa…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProbabilityTheory.iIndepFun.restrict`：∀ {Ω : Type u_1} {ι : Type u_2} {_
mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type u_10}   {m :
 (i : ι) → MeasurableSpace…
-/
lemma iIndepFun.charFunDual_map_fun_sum_eq_prod [Fintype ι] [NormedSpace ℝ E]
    (mX : ∀ i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFunDual (P.map (fun ω ↦ ∑ i, X i ω)) = ∏ i, charFunDual (P.map (X i)) :=
  (hX.restrict _).charFunDual_map_fun_finsetSum_eq_prod (by simpa)
/-
**ProbabilityTheory.charFunDual_map_sum_pi_eq_prod** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：charFunDual_map_sum_pi_eq_prod [Fintype ι] [NormedSpace Real E] {μ : ι -> 
Measure E} [forall i, IsProbabilityMeasure (μ i)] : charFunDual ((Measure.pi μ).
map (fun p => ∑ i, p i)) = ∏ i, charFunDual (μ i)
参数：μ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.iIndepFun.charFunDual_map_fun_sum_eq_prod`：∀ {Ω : Type
 u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2} {E :
 Type u_3}   [inst : MeasurableSpace E] [inst_1 :…
· 使用定理 `AEMeasurable.eval`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : Measure
Theory.Measure α} {δ : Type u_6} {X : δ → Type u_7}   {mX : (a : δ) → Measurable
Space (…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用引理 `ProbabilityTheory.iIndepFun_pi`：iIndepFun_pi (mX : forall i, AEMeasurabl
e (X i) (μ i)) : iIndepFun (fun i ω => X i (ω i)) (Measure.pi μ)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.measurePreserving_eval`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
-/
lemma charFunDual_map_sum_pi_eq_prod [Fintype ι] [NormedSpace ℝ E] {μ : ι → Measure E}
    [∀ i, IsProbabilityMeasure (μ i)] :
    charFunDual ((Measure.pi μ).map (fun p ↦ ∑ i, p i)) = ∏ i, charFunDual (μ i) := by
  rw [iIndepFun.charFunDual_map_fun_sum_eq_prod]
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [(measurePreserving_eval μ i).map_eq]
  · exact aemeasurable_id.eval
  · exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
/-
**ProbabilityTheory.iIndepFun.charFun_map_finsetSum_eq_prod** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} {s : Finset ι} {E : Type u_3}   [inst : MeasurableSpace E] [inst_1 
: NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → 
E}   [inst_4 : InnerProductSpace ℝ E],   (∀ i ∈ s, AEMeasurable (X i) P) →     P
robabilityTheory.iIndepFun (s.restrict X) P →       MeasureTheory.charFun (Measu
reTheory.Measure.map (∑ i ∈ s, X i) P) =         ∏ i ∈ s, MeasureTheory.charFun 
(MeasureTheory.Measure.map (X i) P)
参数：∀ i ∈ s, AEMeasurable (X i) P；s.restrict X；MeasureTheory.Measure.map (∑ i ∈ s
, X i) P；MeasureTheory.Measure.map (X i) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_eq_charFunDual_toDualMap`：charFun_eq_charFunDual_t
oDualMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] {mE : Mea
surableSpace E} {μ : Measure E} (t :…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.iIndepFun.charFunDual_map_finsetSum_eq_prod`：∀ {Ω : Ty
pe u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2} {s
 : Finset ι} {E : Type u_3}   [inst : MeasurableSpa…
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iIndepFun.charFun_map_finsetSum_eq_prod [InnerProductSpace ℝ E]
    (mX : ∀ i ∈ s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFun (P.map (∑ i ∈ s, X i)) = ∏ i ∈ s, charFun (P.map (X i)) := by
  ext
  simp [charFun_eq_charFunDual_toDualMap, hX.charFunDual_map_finsetSum_eq_prod mX]

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFun_map_finset_sum_eq_prod := iIndepFun.charFun_map_finsetSum_eq_prod
/-
**ProbabilityTheory.iIndepFun.charFun_map_sum_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} {E : Type u_3}   [inst : MeasurableSpace E] [inst_1 : NormedAddComm
Group E] [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → E}   [inst_4 : 
Fintype ι] [inst_5 : InnerProductSpace ℝ E],   (∀ (i : ι), AEMeasurable (X i) P)
 →     ProbabilityTheory.iIndepFun X P →       MeasureTheory.charFun (MeasureThe
ory.Measure.map (∑ i, X i) P) =         ∏ i, MeasureTheory.charFun (MeasureTheor
y.Measure.map (X i) P)
参数：∀ (i : ι), AEMeasurable (X i) P；MeasureTheory.Measure.map (∑ i, X i) P；Measur
eTheory.Measure.map (X i) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.charFun_map_finsetSum_eq_prod`：∀ {Ω : Type u
_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2} {s : F
inset ι} {E : Type u_3}   [inst : MeasurableSpa…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProbabilityTheory.iIndepFun.restrict`：∀ {Ω : Type u_1} {ι : Type u_2} {_
mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type u_10}   {m :
 (i : ι) → MeasurableSpace…
-/
lemma iIndepFun.charFun_map_sum_eq_prod [Fintype ι] [InnerProductSpace ℝ E]
    (mX : ∀ i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFun (P.map (∑ i, X i)) = ∏ i, charFun (P.map (X i)) :=
  (hX.restrict _).charFun_map_finsetSum_eq_prod (by simpa)
/-
**ProbabilityTheory.iIndepFun.charFun_map_fun_finsetSum_eq_prod** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} {s : Finset ι} {E : Type u_3}   [inst : MeasurableSpace E] [inst_1 
: NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → 
E}   [inst_4 : InnerProductSpace ℝ E],   (∀ i ∈ s, AEMeasurable (X i) P) →     P
robabilityTheory.iIndepFun (s.restrict X) P →       MeasureTheory.charFun (Measu
reTheory.Measure.map (fun ω => ∑ i ∈ s, X i ω) P) =         ∏ i ∈ s, MeasureTheo
ry.charFun (MeasureTheory.Measure.map (X i) P)
参数：∀ i ∈ s, AEMeasurable (X i) P；s.restrict X；MeasureTheory.Measure.map (fun ω =
> ∑ i ∈ s, X i ω) P；MeasureTheory.Measure.map (X i) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.iIndepFun.charFun_map_finsetSum_eq_prod`：∀ {Ω : Type u
_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2} {s : F
inset ι} {E : Type u_3}   [inst : MeasurableSpa…
-/
lemma iIndepFun.charFun_map_fun_finsetSum_eq_prod [InnerProductSpace ℝ E]
    (mX : ∀ i ∈ s, AEMeasurable (X i) P) (hX : iIndepFun (s.restrict X) P) :
    charFun (P.map (fun ω ↦ ∑ i ∈ s, X i ω)) = ∏ i ∈ s, charFun (P.map (X i)) := by
  convert! hX.charFun_map_finsetSum_eq_prod mX
  simp

@[deprecated (since := "2026-04-08")]
alias iIndepFun.charFun_map_fun_finset_sum_eq_prod := iIndepFun.charFun_map_fun_finsetSum_eq_prod
/-
**ProbabilityTheory.iIndepFun.charFun_map_fun_sum_eq_prod** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} {E : Type u_3}   [inst : MeasurableSpace E] [inst_1 : NormedAddComm
Group E] [BorelSpace E] [SecondCountableTopology E] {X : ι → Ω → E}   [inst_4 : 
Fintype ι] [inst_5 : InnerProductSpace ℝ E],   (∀ (i : ι), AEMeasurable (X i) P)
 →     ProbabilityTheory.iIndepFun X P →       MeasureTheory.charFun (MeasureThe
ory.Measure.map (fun ω => ∑ i, X i ω) P) =         ∏ i, MeasureTheory.charFun (M
easureTheory.Measure.map (X i) P)
参数：∀ (i : ι), AEMeasurable (X i) P；MeasureTheory.Measure.map (fun ω => ∑ i, X i 
ω) P；MeasureTheory.Measure.map (X i) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.charFun_map_fun_finsetSum_eq_prod`：∀ {Ω : Ty
pe u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2} {s
 : Finset ι} {E : Type u_3}   [inst : MeasurableSpa…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProbabilityTheory.iIndepFun.restrict`：∀ {Ω : Type u_1} {ι : Type u_2} {_
mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type u_10}   {m :
 (i : ι) → MeasurableSpace…
-/
lemma iIndepFun.charFun_map_fun_sum_eq_prod [Fintype ι] [InnerProductSpace ℝ E]
    (mX : ∀ i, AEMeasurable (X i) P) (hX : iIndepFun X P) :
    charFun (P.map (fun ω ↦ ∑ i, X i ω)) = ∏ i, charFun (P.map (X i)) :=
  (hX.restrict _).charFun_map_fun_finsetSum_eq_prod (by simpa)
/-
**ProbabilityTheory.charFun_map_sum_pi_eq_prod** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：charFun_map_sum_pi_eq_prod [Fintype ι] [InnerProductSpace Real E] (μ : ι -
> Measure E) [forall i, IsProbabilityMeasure (μ i)] : charFun ((Measure.pi μ).ma
p (fun p => ∑ i, p i)) = ∏ i, charFun (μ i)
参数：μ : ι -> Measure E；μ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_eq_charFunDual_toDualMap`：charFun_eq_charFunDual_t
oDualMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] {mE : Mea
surableSpace E} {μ : Measure E} (t :…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ProbabilityTheory.charFunDual_map_sum_pi_eq_prod`：charFunDual_map_sum_pi
_eq_prod [Fintype ι] [NormedSpace Real E] {μ : ι -> Measure E} [forall i, IsProb
abilityMeasure (μ i)] : charFunDual ((…
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charFun_map_sum_pi_eq_prod [Fintype ι] [InnerProductSpace ℝ E]
    (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)] :
    charFun ((Measure.pi μ).map (fun p ↦ ∑ i, p i)) = ∏ i, charFun (μ i) := by
  ext
  simp [charFun_eq_charFunDual_toDualMap, charFunDual_map_sum_pi_eq_prod]

end Sum

variable [Fintype ι] [IsProbabilityMeasure P] {E : ι → Type*}
  {mE : ∀ i, MeasurableSpace (E i)} [∀ i, NormedAddCommGroup (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}

section InnerProductSpace

variable [∀ i, InnerProductSpace ℝ (E i)]

/-- A finite number of random variables are independent if and only if their joint characteristic
function is equal to the product of the characteristic functions. This is the version for Hilbert
spaces, see `iIndepFun_iff_charFunDual_pi` for the Banach space version. -/
/-
**ProbabilityTheory.iIndepFun_iff_charFun_pi** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：iIndepFun_iff_charFun_pi (hX : forall i, AEMeasurable (X i) P) : iIndepFun
 X P ↔ forall t, charFun (P.map (fun ω => toLp 2 (X · ω))) t = ∏ i, charFun (P.m
ap (X i)) (t i)
参数：hX : forall i, AEMeasurable (X i) P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`：iIndepFun_iff_map_fun
_eq_pi_map [Fintype ι] {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)} {f
 : Π i, Ω -> β i} [IsProbabilityMeasure…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.charFun_eq_pi_iff`：charFun_eq_pi_iff {μ : (i : ι) -> Measu
re (E i)} {ν : Measure (Π i, E i)} [forall i, IsFiniteMeasure (μ i)] [IsFiniteMe
asure ν] : (forall t,…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `WithLp.measurable_toLp`：measurable_toLp : Measurable (@toLp p X)
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A finite number of random variables are independent if and only if their joint c
haracteristic
function is equal to the product of the characteristic functions. This is the ve
rsion for Hilbert
spaces, see `iIndepFun_iff_charFunDual_pi` for the Banach space version.
-/
lemma iIndepFun_iff_charFun_pi (hX : ∀ i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ ∀ t, charFun (P.map (fun ω ↦ toLp 2 (X · ω))) t =
      ∏ i, charFun (P.map (X i)) (t i) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX, ← charFun_eq_pi_iff,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), Function.comp_def]

end InnerProductSpace

section NormedSpace

variable [∀ i, NormedSpace ℝ (E i)] [DecidableEq ι]

/-- A finite number of random variables are independent if and only if their joint characteristic
function is equal to the product of the characteristic functions. This is the version for Banach
spaces, see `iIndepFun_iff_charFun_pi` for the Hilbert space version. -/
/-
**ProbabilityTheory.iIndepFun_iff_charFunDual_pi** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：iIndepFun_iff_charFunDual_pi (hX : forall i, AEMeasurable (X i) P) : iInde
pFun X P ↔ forall L, charFunDual (P.map (fun ω => (X · ω))) L = ∏ i, charFunDual
 (P.map (X i)) (L.comp (.single Real E i))
参数：hX : forall i, AEMeasurable (X i) P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`：iIndepFun_iff_map_fun
_eq_pi_map [Fintype ι] {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)} {f
 : Π i, Ω -> β i} [IsProbabilityMeasure…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.charFunDual_eq_pi_iff`：charFunDual_eq_pi_iff {ι : Type*} [
Fintype ι] [DecidableEq ι] {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)]
 [forall i, NormedSpace R…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A finite number of random variables are independent if and only if their joint c
haracteristic
function is equal to the product of the characteristic functions. This is the ve
rsion for Banach
spaces, see `iIndepFun_iff_charFun_pi` for the Hilbert space version.
-/
lemma iIndepFun_iff_charFunDual_pi (hX : ∀ i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ ∀ L, charFunDual (P.map (fun ω ↦ (X · ω))) L =
      ∏ i, charFunDual (P.map (X i)) (L.comp (.single ℝ E i)) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX, ← charFunDual_eq_pi_iff]

/-- A finite number of random variables are independent if and only if their joint characteristic
function is equal to the product of the characteristic functions.
This is `iIndepFun_iff_charFunDual_pi` for `WithLp`. See `iIndepFun_iff_charFun_pi` for the
Hilbert space version. -/
/-
**ProbabilityTheory.iIndepFun_iff_charFunDual_pi'** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：iIndepFun_iff_charFunDual_pi' (hX : forall i, AEMeasurable (X i) P) : iInd
epFun X P ↔ forall L, charFunDual (P.map (fun ω => toLp p (X · ω))) L = ∏ i, cha
rFunDual (P.map (X i)) (L.comp ((PiLp.continuousLinearEquiv p Real E).symm.toCon
tinuousLinearMap.comp (.single Real E i)))
参数：hX : forall i, AEMeasurable (X i) P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`：iIndepFun_iff_map_fun
_eq_pi_map [Fintype ι] {β : ι -> Type*} {m : forall i, MeasurableSpace (β i)} {f
 : Π i, Ω -> β i} [IsProbabilityMeasure…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.charFunDual_eq_pi_iff'`：charFunDual_eq_pi_iff' (p : Real>=
0∞) [Fact (1 <= p)] {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι -> Type*} [fo
rall i, NormedAddCommGroup…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `WithLp.measurable_toLp`：measurable_toLp : Measurable (@toLp p X)
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A finite number of random variables are independent if and only if their joint c
haracteristic
function is equal to the product of the characteristic functions.
This is `iIndepFun_iff_charFunDual_pi` for `WithLp`. See `iIndepFun_iff_charFun_
pi` for the
Hilbert space version.
-/
lemma iIndepFun_iff_charFunDual_pi' (hX : ∀ i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ ∀ L, charFunDual (P.map (fun ω ↦ toLp p (X · ω))) L =
      ∏ i, charFunDual (P.map (X i)) (L.comp
        ((PiLp.continuousLinearEquiv p ℝ E).symm.toContinuousLinearMap.comp (.single ℝ E i))) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map hX, ← charFunDual_eq_pi_iff' p,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop), Function.comp_def]

end NormedSpace

end iIndepFun

end ProbabilityTheory

