/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Disintegration.Density
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Radon-Nikodym derivative and Lebesgue decomposition for kernels

Let `α` and `γ` be two measurable spaces, where either `α` is countable or `γ` is
countably generated. Let `κ, η : Kernel α γ` be finite kernels.
Then there exists a function `Kernel.rnDeriv κ η : α → γ → ℝ≥0∞` jointly measurable on `α × γ`
and a kernel `Kernel.singularPart κ η : Kernel α γ` such that
* `κ = Kernel.withDensity η (Kernel.rnDeriv κ η) + Kernel.singularPart κ η`,
* for all `a : α`, `Kernel.singularPart κ η a ⟂ₘ η a`,
* for all `a : α`, `Kernel.singularPart κ η a = 0 ↔ κ a ≪ η a`,
* for all `a : α`, `Kernel.withDensity η (Kernel.rnDeriv κ η) a = 0 ↔ κ a ⟂ₘ η a`.

Furthermore, the sets `{a | κ a ≪ η a}` and `{a | κ a ⟂ₘ η a}` are measurable.

When `γ` is countably generated, the construction of the derivative starts from `Kernel.density`:
for two finite kernels `κ' : Kernel α (γ × β)` and `η' : Kernel α γ` with `fst κ' ≤ η'`,
the function `density κ' η' : α → γ → Set β → ℝ` is jointly measurable in the first two arguments
and satisfies that for all `a : α` and all measurable sets `s : Set β` and `A : Set γ`,
`∫ x in A, density κ' η' a x s ∂(η' a) = (κ' a (A ×ˢ s)).toReal`.
We use that definition for `β = Unit` and `κ' = map κ (fun a ↦ (a, ()))`. We can't choose `η' = η`
in general because we might not have `κ ≤ η`, but if we could, we would get a measurable function
`f` with the property `κ = withDensity η f`, which is the decomposition we want for `κ ≤ η`.
To circumvent that difficulty, we take `η' = κ + η` and thus define `rnDerivAux κ η`.
Finally, `rnDeriv κ η a x` is given by
`ENNReal.ofReal (rnDerivAux κ (κ + η) a x) / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)`.
Up to some conversions between `ℝ` and `ℝ≥0`, the singular part is
`withDensity (κ + η) (rnDerivAux κ (κ + η) - (1 - rnDerivAux κ (κ + η)) * rnDeriv κ η)`.

The countably generated measurable space assumption is not needed to have a decomposition for
measures, but the additional difficulty with kernels is to obtain joint measurability of the
derivative. This is why we can't simply define `rnDeriv κ η` by `a ↦ (κ a).rnDeriv (ν a)`
everywhere unless `α` is countable (although `rnDeriv κ η` has that value almost everywhere).
See the construction of `Kernel.density` for details on how the countably generated hypothesis
is used.

## Main definitions

* `ProbabilityTheory.Kernel.rnDeriv`: a function `α → γ → ℝ≥0∞` jointly measurable on `α × γ`
* `ProbabilityTheory.Kernel.singularPart`: a `Kernel α γ`

## Main statements

* `ProbabilityTheory.Kernel.mutuallySingular_singularPart`: for all `a : α`,
  `Kernel.singularPart κ η a ⟂ₘ η a`
* `ProbabilityTheory.Kernel.rnDeriv_add_singularPart`:
  `Kernel.withDensity η (Kernel.rnDeriv κ η) + Kernel.singularPart κ η = κ`
* `ProbabilityTheory.Kernel.measurableSet_absolutelyContinuous` : the set `{a | κ a ≪ η a}`
  is Measurable
* `ProbabilityTheory.Kernel.measurableSet_mutuallySingular` : the set `{a | κ a ⟂ₘ η a}`
  is Measurable

Uniqueness results: if `κ = η.withDensity f + ξ` for measurable `f` and `ξ` is such that
`ξ a ⟂ₘ η a` for some `a : α` then
* `ProbabilityTheory.Kernel.eq_rnDeriv`: `f a =ᵐ[η a] Kernel.rnDeriv κ η a`
* `ProbabilityTheory.Kernel.eq_singularPart`: `ξ a = Kernel.singularPart κ η a`

## References

Theorem 1.28 in [O. Kallenberg, Random Measures, Theory and Applications][kallenberg2017].

-/

@[expose] public section

open MeasureTheory Set Filter ENNReal

open scoped NNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {κ η : Kernel α γ}
  [hαγ : MeasurableSpace.CountableOrCountablyGenerated α γ]

open scoped Classical in
/-- Auxiliary function used to define `ProbabilityTheory.Kernel.rnDeriv` and
`ProbabilityTheory.Kernel.singularPart`.

This has the properties we want for a Radon-Nikodym derivative only if `κ ≪ ν`. The definition of
`rnDeriv κ η` will be built from `rnDerivAux κ (κ + η)`. -/
noncomputable
/-
**ProbabilityTheory.Kernel.rnDerivAux** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：rnDerivAux (κ η : Kernel α γ) (a : α) (x : γ) : Real
参数：κ η : Kernel α γ；a : α；x : γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rnDerivAux (κ η : Kernel α γ) (a : α) (x : γ) : ℝ :=
  if hα : Countable α then ((κ a).rnDeriv (η a) x).toReal
  else haveI := hαγ.countableOrCountablyGenerated.resolve_left hα
    density (map κ (fun a ↦ (a, ()))) η a x univ
/-
**ProbabilityTheory.Kernel.rnDerivAux_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：rnDerivAux_nonneg (hκη : κ <= η) {a : α} {x : γ} : 0 <= rnDerivAux κ η a x
参数：hκη : κ <= η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.rnDerivAux.eq_1`：∀ {α : Type u_1} {γ : Type u_2
} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : MeasurableSpace.Cou
ntableOrCountablyGenerated α γ…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `MeasurableSpace.CountableOrCountablyGenerated.countableOrCountablyGenera
ted`：∀ {α : Type u_5} {β : Type u_6} {inst : MeasurableSpace β} [self : Measurab
leSpace.CountableOrCountablyGenerated α β],   Countable α ∨ Measu…
· 使用引理 `ProbabilityTheory.Kernel.density_nonneg`：density_nonneg (hκν : fst κ <= 
ν) (a : α) (x : γ) (s : Set β) : 0 <= density κ ν a x s
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用引理 `ProbabilityTheory.Kernel.fst_map_id_prod`：fst_map_id_prod (κ : Kernel α 
β) {f : β -> γ} (hf : Measurable f) : fst (map κ (fun a => (a, f a))) = κ
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
lemma rnDerivAux_nonneg (hκη : κ ≤ η) {a : α} {x : γ} : 0 ≤ rnDerivAux κ η a x := by
  rw [rnDerivAux]
  split_ifs with hα
  · exact ENNReal.toReal_nonneg
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_nonneg ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _
/-
**ProbabilityTheory.Kernel.rnDerivAux_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：rnDerivAux_le_one [IsFiniteKernel η] (hκη : κ <= η) {a : α} : rnDerivAux κ
 η a <=ᵐ[η a] 1
参数：hκη : κ <= η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_le_one_of_le`：rnDeriv_le_one_of_le (hμν : 
μ <= ν) [SigmaFinite ν] : μ.rnDeriv ν <=ᵐ[ν] 1
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ENNReal.toReal_le_of_le_ofReal`：toReal_le_of_le_ofReal {a : Real>=0∞} {b
 : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b) : ENNReal.toReal a <= b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `MeasurableSpace.CountableOrCountablyGenerated.countableOrCountablyGenera
ted`：∀ {α : Type u_5} {β : Type u_6} {inst : MeasurableSpace β} [self : Measurab
leSpace.CountableOrCountablyGenerated α β],   Countable α ∨ Measu…
· 使用引理 `ProbabilityTheory.Kernel.density_le_one`：density_le_one (hκν : fst κ <= 
ν) (a : α) (x : γ) (s : Set β) : density κ ν a x s <= 1
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用引理 `ProbabilityTheory.Kernel.fst_map_id_prod`：fst_map_id_prod (κ : Kernel α 
β) {f : β -> γ} (hf : Measurable f) : fst (map κ (fun a => (a, f a))) = κ
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
lemma rnDerivAux_le_one [IsFiniteKernel η] (hκη : κ ≤ η) {a : α} :
    rnDerivAux κ η a ≤ᵐ[η a] 1 := by
  filter_upwards [Measure.rnDeriv_le_one_of_le (hκη a)] with x hx_le_one
  simp_rw [rnDerivAux]
  split_ifs with hα
  · refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [Pi.one_apply, ENNReal.ofReal_one]
    exact hx_le_one
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_le_one ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

@[fun_prop]
/-
**ProbabilityTheory.Kernel.measurable_rnDerivAux** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：measurable_rnDerivAux (κ η : Kernel α γ) : Measurable (fun p : α × γ => Ke
rnel.rnDerivAux κ η p.1 p.2)
参数：κ η : Kernel α γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用引理 `measurable_from_prod_countable_right'`：measurable_from_prod_countable_ri
ght' [Countable α] {f : α × β -> γ} (hf : forall x, Measurable fun y => f (x, y)
) (h'f : forall x x' y, x' …
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用引理 `mem_of_mem_measurableAtom`：mem_of_mem_measurableAtom {x y : β} (h : y in
 measurableAtom x) {s : Set β} (hs : MeasurableSet s) (hxs : x in s) : y in s
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `MeasurableSpace.CountableOrCountablyGenerated.countableOrCountablyGenera
ted`：∀ {α : Type u_5} {β : Type u_6} {inst : MeasurableSpace β} [self : Measurab
leSpace.CountableOrCountablyGenerated α β],   Countable α ∨ Measu…
· 使用引理 `ProbabilityTheory.Kernel.measurable_density`：measurable_density (κ : Ker
nel α (γ × β)) (ν : Kernel α γ) {s : Set β} (hs : MeasurableSet s) : Measurable 
(fun (p : α × γ) => density κ ν p…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma measurable_rnDerivAux (κ η : Kernel α γ) :
    Measurable (fun p : α × γ ↦ Kernel.rnDerivAux κ η p.1 p.2) := by
  simp_rw [rnDerivAux]
  split_ifs with hα
  · refine Measurable.ennreal_toReal <| measurable_from_prod_countable_right'
      (fun a ↦ Measure.measurable_rnDeriv (κ a) (η a)) fun a a' c ha'_mem_a ↦ ?_
    have h_eq : ∀ κ : Kernel α γ, κ a' = κ a := fun κ ↦ by
      ext s hs
      exact mem_of_mem_measurableAtom ha'_mem_a
        (Kernel.measurable_coe κ hs (measurableSet_singleton (κ a s))) rfl
    rw [h_eq κ, h_eq η]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact measurable_density _ η MeasurableSet.univ

@[fun_prop]
/-
**ProbabilityTheory.Kernel.measurable_rnDerivAux_right** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：measurable_rnDerivAux_right (κ η : Kernel α γ) (a : α) : Measurable (fun x
 : γ => rnDerivAux κ η a x)
参数：κ η : Kernel α γ；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDerivAux`：measurable_rnDerivAux (κ
 η : Kernel α γ) : Measurable (fun p : α × γ => Kernel.rnDerivAux κ η p.1 p.2)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma measurable_rnDerivAux_right (κ η : Kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ rnDerivAux κ η a x) := by fun_prop
/-
**ProbabilityTheory.Kernel.setLIntegral_rnDerivAux** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：setLIntegral_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKer
nel η] (a : α) {s : Set γ} (hs : MeasurableSet s) : ∫⁻ x in s, ENNReal.ofReal (r
nDerivAux κ (κ + η) a x) ∂(κ + η) a = κ a s
参数：κ η : Kernel α γ；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `ProbabilityTheory.Kernel.instAddLeftMono`：∀ {α : Type u_4} {β : Type u_5
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β],   AddLeftMono (Probab
ilityTheory.Kernel α β)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.setLIntegral_rnDeriv`：setLIntegral_rnDeriv [HaveLe
besgueDecomposition μ ν] [SFinite ν] (hμν : μ ≪ ν) (s : Set α) : ∫⁻ x in s, μ.rn
Deriv ν x ∂ν = μ s
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.add`：∀ {α : Type u_1} {β : Type u_2} {m
α : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory.Kernel 
α β)   [ProbabilityTheory.…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
· 使用定理 `MeasureTheory.setLIntegral_congr_fun_ae`：setLIntegral_congr_fun_ae {f g 
: α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s 
-> f x = g x) : ∫⁻ x in s, f …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `MeasurableSpace.CountableOrCountablyGenerated.countableOrCountablyGenera
ted`：∀ {α : Type u_5} {β : Type u_6} {inst : MeasurableSpace β} [self : Measurab
leSpace.CountableOrCountablyGenerated α β],   Countable α ∨ Measu…
· 使用引理 `ProbabilityTheory.Kernel.setLIntegral_density`：setLIntegral_density (hκν
 : fst κ <= ν) [IsFiniteKernel ν] (a : α) {s : Set β} (hs : MeasurableSet s) {A 
: Set γ} (hA : MeasurableSet A) : ∫…
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用引理 `ProbabilityTheory.Kernel.fst_map_id_prod`：fst_map_id_prod (κ : Kernel α 
β) {f : β -> γ} (hf : Measurable f) : fst (map κ (fun a => (a, f a))) = κ
（共 43 条，此处仅展示前 30 条）
-/
lemma setLIntegral_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) {s : Set γ} (hs : MeasurableSet s) :
    ∫⁻ x in s, ENNReal.ofReal (rnDerivAux κ (κ + η) a x) ∂(κ + η) a = κ a s := by
  have h_le : κ ≤ κ + η := le_add_of_nonneg_right bot_le
  simp_rw [rnDerivAux]
  split_ifs with hα
  · have h_ac : κ a ≪ (κ + η) a := Measure.absolutelyContinuous_of_le (h_le a)
    rw [← Measure.setLIntegral_rnDeriv h_ac]
    refine setLIntegral_congr_fun_ae hs ?_
    filter_upwards [Measure.rnDeriv_lt_top (κ a) ((κ + η) a)] with x hx_lt _
    rw [ENNReal.ofReal_toReal hx_lt.ne]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    rw [setLIntegral_density ((fst_map_id_prod _ measurable_const).trans_le h_le) _
      MeasurableSet.univ hs, map_apply' _ (by fun_prop) _ (hs.prod MeasurableSet.univ)]
    congr 1 with x
    simp
/-
**ProbabilityTheory.Kernel.withDensity_rnDerivAux** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：withDensity_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKern
el η] : withDensity (κ + η) (fun a x => Real.toNNReal (rnDerivAux κ (κ + η) a x)
) = κ
参数：κ η : Kernel α γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply'`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (
κ : ProbabilityTheory.Kernel α β)…
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `Measurable.real_toNNReal`：Measurable.real_toNNReal {f : α -> Real} (hf :
 Measurable f) : Measurable fun x => Real.toNNReal (f x)
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDerivAux`：measurable_rnDerivAux (κ
 η : Kernel α γ) : Measurable (fun p : α × γ => Kernel.rnDerivAux κ η p.1 p.2)
· 使用引理 `ProbabilityTheory.Kernel.setLIntegral_rnDerivAux`：setLIntegral_rnDerivAu
x (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) {s : Set γ} (
hs : MeasurableSet s) : ∫⁻ x in s, ENN…
-/
lemma withDensity_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x)) = κ := by
  ext a s hs
  rw [Kernel.withDensity_apply']
  swap; · fun_prop
  simp_rw [ofNNReal_toNNReal]
  exact setLIntegral_rnDerivAux κ η a hs
/-
**ProbabilityTheory.Kernel.withDensity_one_sub_rnDerivAux** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：withDensity_one_sub_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFi
niteKernel η] : withDensity (κ + η) (fun a x => Real.toNNReal (1 - rnDerivAux κ 
(κ + η) a x)) = η
参数：κ η : Kernel α γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `ProbabilityTheory.Kernel.instAddLeftMono`：∀ {α : Type u_4} {β : Type u_5
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β],   AddLeftMono (Probab
ilityTheory.Kernel α β)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity.congr_simp`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ κ_1 : ProbabilityT
heory.Kernel α β)   (e_κ : κ = κ_1) […
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.ofReal_sub`：ofReal_sub (p : Real) {q : Real} (hq : 0 <= q) : ENN
Real.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q
· 使用引理 `ProbabilityTheory.Kernel.rnDerivAux_nonneg`：rnDerivAux_nonneg (hκη : κ <
= η) {a : α} {x : γ} : 0 <= rnDerivAux κ η a x
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用引理 `ProbabilityTheory.Kernel.withDensity_sub_add_cancel`：withDensity_sub_add
_cancel [IsSFiniteKernel κ] {f g : α -> β -> Real>=0∞} (hf : Measurable (Functio
n.uncurry f)) (hg : Measurable (Function.…
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDerivAux`：measurable_rnDerivAux (κ
 η : Kernel α γ) : Measurable (fun p : α × γ => Kernel.rnDerivAux κ η p.1 p.2)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.rnDerivAux_le_one`：rnDerivAux_le_one [IsFiniteK
ernel η] (hκη : κ <= η) {a : α} : rnDerivAux κ η a <=ᵐ[η a] 1
· 使用定理 `ProbabilityTheory.IsFiniteKernel.add`：∀ {α : Type u_1} {β : Type u_2} {m
α : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory.Kernel 
α β)   [ProbabilityTheory.…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `ProbabilityTheory.Kernel.withDensity_one'`：withDensity_one' (κ : Kernel 
α β) [IsSFiniteKernel κ] : Kernel.withDensity κ (fun _ _ => 1) = κ
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.add_right_inj`：add_right_inj (h : a != ∞) : a + b = a + c ↔ b = 
c
（共 36 条，此处仅展示前 30 条）
-/
lemma withDensity_one_sub_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity (κ + η) (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) = η := by
  have h_le : κ ≤ κ + η := le_add_of_nonneg_right bot_le
  suffices withDensity (κ + η) (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
      + withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x))
      = κ + η by
    ext a s
    have h : (withDensity (κ + η) (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
          + withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x))) a s
        = κ a s + η a s := by
      rw [this]
      simp
    simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add] at h
    rwa [withDensity_rnDerivAux, add_comm, ENNReal.add_right_inj (measure_ne_top _ _)] at h
  simp_rw [ofNNReal_toNNReal, ENNReal.ofReal_sub _ (rnDerivAux_nonneg h_le), ENNReal.ofReal_one]
  rw [withDensity_sub_add_cancel]
  · rw [withDensity_one']
  · exact measurable_const
  · fun_prop
  · intro a
    filter_upwards [rnDerivAux_le_one h_le] with x hx
    simp only [ENNReal.ofReal_le_one]
    exact hx

/-- A set of points in `α × γ` related to the absolute continuity / mutual singularity of
`κ` and `η`. -/
/-
**ProbabilityTheory.Kernel.mutuallySingularSet** 是 Mathlib 中的一个定义，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：mutuallySingularSet (κ η : Kernel α γ) : Set (α × γ)
参数：κ η : Kernel α γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of points in `α × γ` related to the absolute continuity / mutual singulari
ty of
`κ` and `η`.
-/
def mutuallySingularSet (κ η : Kernel α γ) : Set (α × γ) := {p | 1 ≤ rnDerivAux κ (κ + η) p.1 p.2}

/-- A set of points in `α × γ` related to the absolute continuity / mutual singularity of
`κ` and `η`. That is,
* `withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a) = 0`,
* `singularPart κ η a (mutuallySingularSetSlice κ η a)ᶜ = 0`.
-/
/-
**ProbabilityTheory.Kernel.mutuallySingularSetSlice** 是 Mathlib 中的一个定义，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) : Set γ
参数：κ η : Kernel α γ；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of points in `α × γ` related to the absolute continuity / mutual singulari
ty of
`κ` and `η`. That is,
* `withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a) = 0`,
* `singularPart κ η a (mutuallySingularSetSlice κ η a)ᶜ = 0`.
-/
def mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) : Set γ :=
  {x | 1 ≤ rnDerivAux κ (κ + η) a x}
/-
**ProbabilityTheory.Kernel.mem_mutuallySingularSetSlice** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory.Kernel`。
形式化陈述：mem_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) (x : γ) : x in mut
uallySingularSetSlice κ η a ↔ 1 <= rnDerivAux κ (κ + η) a x
参数：κ η : Kernel α γ；a : α；x : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.mutuallySingularSetSlice.eq_1`：∀ {α : Type u_1}
 {γ : Type u_2} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : Measu
rableSpace.CountableOrCountablyGenerated α γ…
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) (x : γ) :
    x ∈ mutuallySingularSetSlice κ η a ↔ 1 ≤ rnDerivAux κ (κ + η) a x := by
  rw [mutuallySingularSetSlice, mem_ofPred]
/-
**ProbabilityTheory.Kernel.notMem_mutuallySingularSetSlice** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：notMem_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) (x : γ) : x ∉ m
utuallySingularSetSlice κ η a ↔ rnDerivAux κ (κ + η) a x < 1
参数：κ η : Kernel α γ；a : α；x : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma notMem_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) (x : γ) :
    x ∉ mutuallySingularSetSlice κ η a ↔ rnDerivAux κ (κ + η) a x < 1 := by
  simp [mutuallySingularSetSlice]
/-
**ProbabilityTheory.Kernel.measurableSet_mutuallySingularSet** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：measurableSet_mutuallySingularSet (κ η : Kernel α γ) : MeasurableSet (mutu
allySingularSet κ η)
参数：κ η : Kernel α γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDerivAux`：measurable_rnDerivAux (κ
 η : Kernel α γ) : Measurable (fun p : α × γ => Kernel.rnDerivAux κ η p.1 p.2)
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
lemma measurableSet_mutuallySingularSet (κ η : Kernel α γ) :
    MeasurableSet (mutuallySingularSet κ η) :=
  measurable_rnDerivAux κ (κ + η) measurableSet_Ici
/-
**ProbabilityTheory.Kernel.measurableSet_mutuallySingularSetSlice** 是 Mathlib 中的
一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：measurableSet_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) : Measur
ableSet (mutuallySingularSetSlice κ η a)
参数：κ η : Kernel α γ；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用引理 `ProbabilityTheory.Kernel.measurableSet_mutuallySingularSet`：measurableSe
t_mutuallySingularSet (κ η : Kernel α γ) : MeasurableSet (mutuallySingularSet κ 
η)
-/
lemma measurableSet_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) :
    MeasurableSet (mutuallySingularSetSlice κ η a) :=
  measurable_prodMk_left (measurableSet_mutuallySingularSet κ η)
/-
**ProbabilityTheory.Kernel.measure_mutuallySingularSetSlice** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：measure_mutuallySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ] [Is
FiniteKernel η] (a : α) : η a (mutuallySingularSetSlice κ η a) = 0
参数：κ η : Kernel α γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply'`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (
κ : ProbabilityTheory.Kernel α β)…
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用定理 `Measurable.const_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDerivAux`：measurable_rnDerivAux (κ
 η : Kernel α γ) : Measurable (fun p : α × γ => Kernel.rnDerivAux κ η p.1 p.2)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDerivAux_right`：measurable_rnDeriv
Aux_right (κ η : Kernel α γ) (a : α) : Measurable (fun x : γ => rnDerivAux κ η a
 x)
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_restrict_iff`：ae_restrict_iff {p : α -> Prop} (hp : Mea
surableSet { x | p x }) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s 
-> p x
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ProbabilityTheory.Kernel.withDensity_one_sub_rnDerivAux`：withDensity_one
_sub_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] : withD
ensity (κ + η) (fun a x => Real.toNNReal (1 -…
-/
lemma measure_mutuallySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) :
    η a (mutuallySingularSetSlice κ η a) = 0 := by
  suffices withDensity (κ + η) (fun a x ↦ Real.toNNReal
      (1 - rnDerivAux κ (κ + η) a x)) a {x | 1 ≤ rnDerivAux κ (κ + η) a x} = 0 by
    rwa [withDensity_one_sub_rnDerivAux κ η] at this
  simp_rw [ofNNReal_toNNReal]
  rw [Kernel.withDensity_apply', lintegral_eq_zero_iff, EventuallyEq, ae_restrict_iff]
  rotate_left
  · exact (measurableSet_singleton 0).preimage (by fun_prop)
  · fun_prop
  · fun_prop
  refine ae_of_all _ (fun x hx ↦ ?_)
  simp only [mem_ofPred_eq] at hx
  simp [hx]

/-- Radon-Nikodym derivative of the kernel `κ` with respect to the kernel `η`. -/
noncomputable
irreducible_def rnDeriv (κ η : Kernel α γ) (a : α) (x : γ) : ℝ≥0∞ :=
  ENNReal.ofReal (rnDerivAux κ (κ + η) a x) / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)

/-
**ProbabilityTheory.Kernel.rnDeriv_def'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：rnDeriv_def' (κ η : Kernel α γ) : rnDeriv κ η = fun a x => ENNReal.ofReal 
(rnDerivAux κ (κ + η) a x) / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)
参数：κ η : Kernel α γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.rnDeriv_def`：∀ {α : Type u_3} {γ : Type u_4} {m
α : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : MeasurableSpace.Countab
leOrCountablyGenerated α γ…
-/
lemma rnDeriv_def' (κ η : Kernel α γ) :
    rnDeriv κ η = fun a x ↦ ENNReal.ofReal (rnDerivAux κ (κ + η) a x)
      / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x) := by ext; rw [rnDeriv_def]

@[fun_prop]
/-
**ProbabilityTheory.Kernel.measurable_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：measurable_rnDeriv (κ η : Kernel α γ) : Measurable (fun p : α × γ => rnDer
iv κ η p.1 p.2)
参数：κ η : Kernel α γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.rnDeriv_def`：∀ {α : Type u_3} {γ : Type u_4} {m
α : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : MeasurableSpace.Countab
leOrCountablyGenerated α γ…
· 使用定理 `Measurable.div`：Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (h
g : Measurable g) : Measurable (f / g)
· 使用定理 `measurableDiv₂_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [
inst_1 : DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G],   MeasurableDiv₂ 
G
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDerivAux`：measurable_rnDerivAux (κ
 η : Kernel α γ) : Measurable (fun p : α × γ => Kernel.rnDerivAux κ η p.1 p.2)
· 使用定理 `Measurable.sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableSub₂ G], 
Meas…
· 使用定理 `ContinuousSub.measurableSub₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Sub γ] [Con…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
lemma measurable_rnDeriv (κ η : Kernel α γ) :
    Measurable (fun p : α × γ ↦ rnDeriv κ η p.1 p.2) := by
  simp_rw [rnDeriv_def]
  exact (measurable_rnDerivAux κ _).ennreal_ofReal.div
    (measurable_const.sub (measurable_rnDerivAux κ _)).ennreal_ofReal

@[fun_prop]
/-
**ProbabilityTheory.Kernel.measurable_rnDeriv_right** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：measurable_rnDeriv_right (κ η : Kernel α γ) (a : α) : Measurable (fun x : 
γ => rnDeriv κ η a x)
参数：κ η : Kernel α γ；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDeriv`：measurable_rnDeriv (κ η : K
ernel α γ) : Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma measurable_rnDeriv_right (κ η : Kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ rnDeriv κ η a x) := by fun_prop
/-
**ProbabilityTheory.Kernel.rnDeriv_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：rnDeriv_eq_top_iff (κ η : Kernel α γ) (a : α) (x : γ) : rnDeriv κ η a x = 
∞ ↔ (a, x) in mutuallySingularSet κ η
参数：κ η : Kernel α γ；a : α；x : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.rnDeriv_def`：∀ {α : Type u_3} {γ : Type u_4} {m
α : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : MeasurableSpace.Countab
leOrCountablyGenerated α γ…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma rnDeriv_eq_top_iff (κ η : Kernel α γ) (a : α) (x : γ) :
    rnDeriv κ η a x = ∞ ↔ (a, x) ∈ mutuallySingularSet κ η := by
  simp only [rnDeriv, ENNReal.div_eq_top, ne_eq, ENNReal.ofReal_eq_zero, not_le,
    tsub_le_iff_right, zero_add, ENNReal.ofReal_ne_top, not_false_eq_true, and_true, or_false,
    mutuallySingularSet, mem_ofPred_eq, and_iff_right_iff_imp]
  exact fun h ↦ zero_lt_one.trans_le h
/-
**ProbabilityTheory.Kernel.rnDeriv_eq_top_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：rnDeriv_eq_top_iff' (κ η : Kernel α γ) (a : α) (x : γ) : rnDeriv κ η a x =
 ∞ ↔ x in mutuallySingularSetSlice κ η a
参数：κ η : Kernel α γ；a : α；x : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_top_iff`：rnDeriv_eq_top_iff (κ η : K
ernel α γ) (a : α) (x : γ) : rnDeriv κ η a x = ∞ ↔ (a, x) in mutuallySingularSet
 κ η
· 使用定理 `ProbabilityTheory.Kernel.mutuallySingularSet.eq_1`：∀ {α : Type u_1} {γ :
 Type u_2} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : Measurable
Space.CountableOrCountablyGenerated α γ…
· 使用定理 `ProbabilityTheory.Kernel.mutuallySingularSetSlice.eq_1`：∀ {α : Type u_1}
 {γ : Type u_2} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : Measu
rableSpace.CountableOrCountablyGenerated α γ…
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rnDeriv_eq_top_iff' (κ η : Kernel α γ) (a : α) (x : γ) :
    rnDeriv κ η a x = ∞ ↔ x ∈ mutuallySingularSetSlice κ η a := by
  rw [rnDeriv_eq_top_iff, mutuallySingularSet, mutuallySingularSetSlice, mem_ofPred, mem_ofPred]

/-- Singular part of the kernel `κ` with respect to the kernel `η`. -/
noncomputable
irreducible_def singularPart (κ η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    Kernel α γ :=
  withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x)
    - Real.toNNReal (1 - rnDerivAux κ (κ + η) a x) * rnDeriv κ η a x)

/-
**ProbabilityTheory.Kernel.measurable_singularPart_fun** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory.Kernel`。
形式化陈述：measurable_singularPart_fun (κ η : Kernel α γ) : Measurable (fun p : α × γ
 => Real.toNNReal (rnDerivAux κ (κ + η) p.1 p.2) - Real.toNNReal (1 - rnDerivAux
 κ (κ + η) p.1 p.2) * rnDeriv κ η p.1 p.2)
参数：κ η : Kernel α γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fun_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableSub₂ 
G], Meas…
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `Measurable.real_toNNReal`：Measurable.real_toNNReal {f : α -> Real} (hf :
 Measurable f) : Measurable fun x => Real.toNNReal (f x)
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDerivAux`：measurable_rnDerivAux (κ
 η : Kernel α γ) : Measurable (fun p : α × γ => Kernel.rnDerivAux κ η p.1 p.2)
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.const_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDeriv`：measurable_rnDeriv (κ η : K
ernel α γ) : Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2)
-/
lemma measurable_singularPart_fun (κ η : Kernel α γ) :
    Measurable (fun p : α × γ ↦ Real.toNNReal (rnDerivAux κ (κ + η) p.1 p.2)
      - Real.toNNReal (1 - rnDerivAux κ (κ + η) p.1 p.2) * rnDeriv κ η p.1 p.2) := by fun_prop
/-
**ProbabilityTheory.Kernel.measurable_singularPart_fun_right** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：measurable_singularPart_fun_right (κ η : Kernel α γ) (a : α) : Measurable 
(fun x : γ => Real.toNNReal (rnDerivAux κ (κ + η) a x) - Real.toNNReal (1 - rnDe
rivAux κ (κ + η) a x) * rnDeriv κ η a x)
参数：κ η : Kernel α γ；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `ProbabilityTheory.Kernel.measurable_singularPart_fun`：measurable_singula
rPart_fun (κ η : Kernel α γ) : Measurable (fun p : α × γ => Real.toNNReal (rnDer
ivAux κ (κ + η) p.1 p.2) - Real.toNNReal (…
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
lemma measurable_singularPart_fun_right (κ η : Kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x)
      - Real.toNNReal (1 - rnDerivAux κ (κ + η) a x) * rnDeriv κ η a x) := by
  change Measurable ((Function.uncurry fun a b ↦
    ENNReal.ofReal (rnDerivAux κ (κ + η) a b)
    - ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a b) * rnDeriv κ η a b) ∘ (fun b ↦ (a, b)))
  exact (measurable_singularPart_fun κ η).comp measurable_prodMk_left
/-
**ProbabilityTheory.Kernel.singularPart_compl_mutuallySingularSetSlice** 是 Mathl
ib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：singularPart_compl_mutuallySingularSetSlice (κ η : Kernel α γ) [IsSFiniteK
ernel κ] [IsSFiniteKernel η] (a : α) : singularPart κ η a (mutuallySingularSetSl
ice κ η a)ᶜ = 0
参数：κ η : Kernel α γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.singularPart_def`：∀ {α : Type u_3} {γ : Type u_
4} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : MeasurableSpace.Co
untableOrCountablyGenerated α γ…
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply'`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (
κ : ProbabilityTheory.Kernel α β)…
· 使用引理 `ProbabilityTheory.Kernel.measurable_singularPart_fun`：measurable_singula
rPart_fun (κ η : Kernel α γ) : Measurable (fun p : α × γ => Real.toNNReal (rnDer
ivAux κ (κ + η) p.1 p.2) - Real.toNNReal (…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用引理 `ProbabilityTheory.Kernel.measurable_singularPart_fun_right`：measurable_s
ingularPart_fun_right (κ η : Kernel α γ) (a : α) : Measurable (fun x : γ => Real
.toNNReal (rnDerivAux κ (κ + η) a x) - Real.toNN…
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_restrict_iff`：ae_restrict_iff {p : α -> Prop} (hp : Mea
surableSet { x | p x }) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s 
-> p x
· 使用定理 `measurableSet_preimage`：measurableSet_preimage {t : Set β} (hf : Measura
ble f) (ht : MeasurableSet t) : MeasurableSet (f ⁻¹' t)
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.Kernel.rnDeriv_def`：∀ {α : Type u_3} {γ : Type u_4} {m
α : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : MeasurableSpace.Countab
leOrCountablyGenerated α γ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_div_of_pos`：ofReal_div_of_pos {x y : Real} (hy : 0 < y) :
 ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
（共 44 条，此处仅展示前 30 条）
-/
lemma singularPart_compl_mutuallySingularSetSlice (κ η : Kernel α γ) [IsSFiniteKernel κ]
    [IsSFiniteKernel η] (a : α) :
    singularPart κ η a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  rw [singularPart, Kernel.withDensity_apply', lintegral_eq_zero_iff, EventuallyEq,
    ae_restrict_iff]
  all_goals simp_rw [ofNNReal_toNNReal]
  rotate_left
  · exact measurableSet_preimage (measurable_singularPart_fun_right κ η a)
      (measurableSet_singleton _)
  · exact measurable_singularPart_fun_right κ η a
  · exact measurable_singularPart_fun κ η
  refine ae_of_all _ (fun x hx ↦ ?_)
  simp only [mem_compl_iff, mutuallySingularSetSlice, mem_ofPred, not_le] at hx
  simp_rw [rnDeriv]
  rw [← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul, ← mul_assoc,
    mul_inv_cancel₀, one_mul, tsub_self, Pi.zero_apply]
  · simp only [ne_eq, sub_eq_zero, hx.ne', not_false_eq_true]
  · simp only [sub_nonneg, hx.le]
  · simp only [sub_pos, hx]
/-
**ProbabilityTheory.Kernel.singularPart_of_subset_compl_mutuallySingularSetSlice
** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：singularPart_of_subset_compl_mutuallySingularSetSlice [IsSFiniteKernel κ] 
[IsFiniteKernel η] {a : α} {s : Set γ} (hs : s subseteq (mutuallySingularSetSlic
e κ η a)ᶜ) : singularPart κ η a s = 0
参数：hs : s subseteq (mutuallySingularSetSlice κ η a)ᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.Kernel.singularPart_compl_mutuallySingularSetSlice`：si
ngularPart_compl_mutuallySingularSetSlice (κ η : Kernel α γ) [IsSFiniteKernel κ]
 [IsSFiniteKernel η] (a : α) : singularPart κ η a (mutuall…
-/
lemma singularPart_of_subset_compl_mutuallySingularSetSlice [IsSFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ} (hs : s ⊆ (mutuallySingularSetSlice κ η a)ᶜ) :
    singularPart κ η a s = 0 :=
  measure_mono_null hs (singularPart_compl_mutuallySingularSetSlice κ η a)
/-
**ProbabilityTheory.Kernel.singularPart_of_subset_mutuallySingularSetSlice** 是 M
athlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：singularPart_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ] [IsFini
teKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s) (hs : s subseteq mutuall
ySingularSetSlice κ η a) : singularPart κ η a s = κ a s
参数：hsm : MeasurableSet s；hs : s subseteq mutuallySingularSetSlice κ η a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.singularPart_def`：∀ {α : Type u_3} {γ : Type u_
4} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : MeasurableSpace.Co
untableOrCountablyGenerated α γ…
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply'`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (
κ : ProbabilityTheory.Kernel α β)…
· 使用引理 `ProbabilityTheory.Kernel.measurable_singularPart_fun`：measurable_singula
rPart_fun (κ η : Kernel α γ) : Measurable (fun p : α × γ => Real.toNNReal (rnDer
ivAux κ (κ + η) p.1 p.2) - Real.toNNReal (…
· 使用定理 `MeasureTheory.setLIntegral_congr_fun_ae`：setLIntegral_congr_fun_ae {f g 
: α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s 
-> f x = g x) : ∫⁻ x in s, f …
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `ProbabilityTheory.Kernel.instAddLeftMono`：∀ {α : Type u_4} {β : Type u_5
} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β],   AddLeftMono (Probab
ilityTheory.Kernel α β)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.rnDerivAux_le_one`：rnDerivAux_le_one [IsFiniteK
ernel η] (hκη : κ <= η) {a : α} : rnDerivAux κ η a <=ᵐ[η a] 1
· 使用定理 `ProbabilityTheory.IsFiniteKernel.add`：∀ {α : Type u_1} {β : Type u_2} {m
α : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory.Kernel 
α β)   [ProbabilityTheory.…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.toNNReal_one`：toNNReal_one : Real.toNNReal 1 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Real.toNNReal_zero`：toNNReal_zero : Real.toNNReal 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `MeasureTheory.Measure.restrict_add`：restrict_add {_m0 : MeasurableSpace 
α} (μ ν : Measure α) (s : Set α) : (μ + ν).restrict s = μ.restrict s + ν.restric
t s
（共 37 条，此处仅展示前 30 条）
-/
lemma singularPart_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s ⊆ mutuallySingularSetSlice κ η a) :
    singularPart κ η a s = κ a s := by
  have hs' : ∀ x ∈ s, 1 ≤ rnDerivAux κ (κ + η) a x := fun _ hx ↦ hs hx
  rw [singularPart, Kernel.withDensity_apply']
  swap; · exact measurable_singularPart_fun κ η
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (rnDerivAux κ (κ + η) a x)) -
      ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) * rnDeriv κ η a x
      ∂(κ + η) a
    = ∫⁻ _ in s, 1 ∂(κ + η) a := by
        refine setLIntegral_congr_fun_ae hsm ?_
        have h_le : κ ≤ κ + η := le_add_of_nonneg_right bot_le
        filter_upwards [rnDerivAux_le_one h_le] with x hx hxs
        have h_eq_one : rnDerivAux κ (κ + η) a x = 1 := le_antisymm hx (hs' x hxs)
        simp [h_eq_one]
  _ = (κ + η) a s := by simp
  _ = κ a s := by
        suffices η a s = 0 by simp [this]
        exact measure_mono_null hs (measure_mutuallySingularSetSlice κ η a)
/-
**ProbabilityTheory.Kernel.withDensity_rnDeriv_mutuallySingularSetSlice** 是 Math
lib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：withDensity_rnDeriv_mutuallySingularSetSlice (κ η : Kernel α γ) [IsFiniteK
ernel κ] [IsFiniteKernel η] (a : α) : withDensity η (rnDeriv κ η) a (mutuallySin
gularSetSlice κ η a) = 0
参数：κ η : Kernel α γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply'`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (
κ : ProbabilityTheory.Kernel α β)…
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDeriv`：measurable_rnDeriv (κ η : K
ernel α γ) : Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2)
· 使用定理 `MeasureTheory.setLIntegral_measure_zero`：setLIntegral_measure_zero (s : 
Set α) (f : α -> Real>=0∞) (hs' : μ s = 0) : ∫⁻ x in s, f x ∂μ = 0
· 使用引理 `ProbabilityTheory.Kernel.measure_mutuallySingularSetSlice`：measure_mutua
llySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a 
: α) : η a (mutuallySingularSetSlice κ η a) = 0
-/
lemma withDensity_rnDeriv_mutuallySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a) = 0 := by
  rw [Kernel.withDensity_apply']
  · exact setLIntegral_measure_zero _ _ (measure_mutuallySingularSetSlice κ η a)
  · exact measurable_rnDeriv κ η
/-
**ProbabilityTheory.Kernel.withDensity_rnDeriv_of_subset_mutuallySingularSetSlic
e** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：withDensity_rnDeriv_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ] 
[IsFiniteKernel η] {a : α} {s : Set γ} (hs : s subseteq mutuallySingularSetSlice
 κ η a) : withDensity η (rnDeriv κ η) a s = 0
参数：hs : s subseteq mutuallySingularSetSlice κ η a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.Kernel.withDensity_rnDeriv_mutuallySingularSetSlice`：w
ithDensity_rnDeriv_mutuallySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ
] [IsFiniteKernel η] (a : α) : withDensity η (rnDeriv κ η) …
-/
lemma withDensity_rnDeriv_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ}
    (hs : s ⊆ mutuallySingularSetSlice κ η a) :
    withDensity η (rnDeriv κ η) a s = 0 :=
  measure_mono_null hs (withDensity_rnDeriv_mutuallySingularSetSlice κ η a)
/-
**ProbabilityTheory.Kernel.withDensity_rnDeriv_of_subset_compl_mutuallySingularS
etSlice** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice [IsFiniteKern
el κ] [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s) (hs : s sub
seteq (mutuallySingularSetSlice κ η a)ᶜ) : withDensity η (rnDeriv κ η) a s = κ a
 s
参数：hsm : MeasurableSet s；hs : s subseteq (mutuallySingularSetSlice κ η a)ᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
· 使用定理 `ProbabilityTheory.Kernel.instIsSFiniteKernelWithDensityOfNNReal`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : 
ProbabilityTheory.Kernel α β)   [inst : ProbabilityTh…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_def'`：rnDeriv_def' (κ η : Kernel α γ) :
 rnDeriv κ η = fun a x => ENNReal.ofReal (rnDerivAux κ (κ + η) a x) / ENNReal.of
Real (1 - rnDerivAux κ (κ +…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.withDensity_one_sub_rnDerivAux`：withDensity_one
_sub_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] : withD
ensity (κ + η) (fun a x => Real.toNNReal (1 -…
· 使用定理 `ProbabilityTheory.Kernel.withDensity_mul`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kerne
l α β}   [inst : ProbabilityTh…
· 使用定理 `Measurable.real_toNNReal`：Measurable.real_toNNReal {f : α -> Real} (hf :
 Measurable f) : Measurable fun x => Real.toNNReal (f x)
· 使用定理 `Measurable.const_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDerivAux`：measurable_rnDerivAux (κ
 η : Kernel α γ) : Measurable (fun p : α × γ => Kernel.rnDerivAux κ η p.1 p.2)
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDeriv`：measurable_rnDeriv (κ η : K
ernel α γ) : Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2)
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply'`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (
κ : ProbabilityTheory.Kernel α β)…
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.rnDeriv_def`：∀ {α : Type u_3} {γ : Type u_4} {m
α : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : MeasurableSpace.Countab
leOrCountablyGenerated α γ…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `ENNReal.ofNNReal_toNNReal`：ofNNReal_toNNReal (x : Real) : (Real.toNNReal
 x : Real>=0∞) = ENNReal.ofReal x
· 使用定理 `ENNReal.ofReal_div_of_pos`：ofReal_div_of_pos {x y : Real} (hy : 0 < y) :
 ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
（共 46 条，此处仅展示前 30 条）
-/
lemma withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice
    [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s ⊆ (mutuallySingularSetSlice κ η a)ᶜ) :
    withDensity η (rnDeriv κ η) a s = κ a s := by
  have : withDensity η (rnDeriv κ η)
      = withDensity (withDensity (κ + η)
        (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))) (rnDeriv κ η) := by
    rw [rnDeriv_def']
    congr
    exact (withDensity_one_sub_rnDerivAux κ η).symm
  rw [this, ← withDensity_mul, Kernel.withDensity_apply']
  rotate_left
  · fun_prop
  · fun_prop
  · exact measurable_rnDeriv _ _
  simp_rw [rnDeriv]
  have hs' : ∀ x ∈ s, rnDerivAux κ (κ + η) a x < 1 := by
    simp_rw [← notMem_mutuallySingularSetSlice]
    exact fun x hx hx_mem ↦ hs hx hx_mem
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) *
      (ENNReal.ofReal (rnDerivAux κ (κ + η) a x) /
        ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)) ∂(κ + η) a
  _ = ∫⁻ x in s, ENNReal.ofReal (rnDerivAux κ (κ + η) a x) ∂(κ + η) a := by
      refine setLIntegral_congr_fun hsm (fun x hx ↦ ?_)
      rw [ofNNReal_toNNReal, ← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul,
        ← mul_assoc, mul_inv_cancel₀, one_mul]
      · rw [ne_eq, sub_eq_zero]
        exact (hs' x hx).ne'
      · simp [(hs' x hx).le]
      · simp [hs' x hx]
  _ = κ a s := setLIntegral_rnDerivAux κ η a hsm

/-- The singular part of `κ` with respect to `η` is mutually singular with `η`. -/
/-
**ProbabilityTheory.Kernel.mutuallySingular_singularPart** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory.Kernel`。
形式化陈述：mutuallySingular_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFin
iteKernel η] (a : α) : singularPart κ η a ⟂ₘ η a
参数：κ η : Kernel α γ；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.Kernel.measurableSet_mutuallySingularSetSlice`：measura
bleSet_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) : MeasurableSet (mutu
allySingularSetSlice κ η a)
· 使用引理 `ProbabilityTheory.Kernel.measure_mutuallySingularSetSlice`：measure_mutua
llySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a 
: α) : η a (mutuallySingularSetSlice κ η a) = 0
· 使用引理 `ProbabilityTheory.Kernel.singularPart_compl_mutuallySingularSetSlice`：si
ngularPart_compl_mutuallySingularSetSlice (κ η : Kernel α γ) [IsSFiniteKernel κ]
 [IsSFiniteKernel η] (a : α) : singularPart κ η a (mutuall…

--- 原说明 ---
The singular part of `κ` with respect to `η` is mutually singular with `η`.
-/
lemma mutuallySingular_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) :
    singularPart κ η a ⟂ₘ η a := by
  symm
  exact ⟨mutuallySingularSetSlice κ η a, measurableSet_mutuallySingularSetSlice κ η a,
    measure_mutuallySingularSetSlice κ η a, singularPart_compl_mutuallySingularSetSlice κ η a⟩

/-- Lebesgue decomposition of a finite kernel `κ` with respect to another one `η`.
`κ` is the sum of an absolutely continuous part `withDensity η (rnDeriv κ η)` and a singular part
`singularPart κ η`. -/
/-
**ProbabilityTheory.Kernel.rnDeriv_add_singularPart** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.Kernel`。
形式化陈述：rnDeriv_add_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKe
rnel η] : withDensity η (rnDeriv κ η) + singularPart κ η = κ
参数：κ η : Kernel α γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FunLike.coe_add`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Add F] [inst_2 : Add β]   [IsAddApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用引理 `ProbabilityTheory.Kernel.measurableSet_mutuallySingularSetSlice`：measura
bleSet_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) : MeasurableSet (mutu
allySingularSetSlice κ η a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用引理 `ProbabilityTheory.Kernel.singularPart_of_subset_mutuallySingularSetSlice
`：singularPart_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ] [IsFiniteKe
rnel η] {a : α} {s : Set γ} (hsm : MeasurableSet s) (hs : s su…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用引理 `ProbabilityTheory.Kernel.singularPart_of_subset_compl_mutuallySingularSe
tSlice`：singularPart_of_subset_compl_mutuallySingularSetSlice [IsSFiniteKernel κ
] [IsFiniteKernel η] {a : α} {s : Set γ} (hs : s subseteq (mutuallyS…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `ProbabilityTheory.Kernel.withDensity_rnDeriv_of_subset_mutuallySingularS
etSlice`：withDensity_rnDeriv_of_subset_mutuallySingularSetSlice [IsFiniteKernel 
κ] [IsFiniteKernel η] {a : α} {s : Set γ} (hs : s subseteq mutuallySi…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `ProbabilityTheory.Kernel.withDensity_rnDeriv_of_subset_compl_mutuallySin
gularSetSlice`：withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice [IsF
initeKernel κ] [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet …
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Lebesgue decomposition of a finite kernel `κ` with respect to another one `η`.
`κ` is the sum of an absolutely continuous part `withDensity η (rnDeriv κ η)` an
d a singular part
`singularPart κ η`.
-/
lemma rnDeriv_add_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity η (rnDeriv κ η) + singularPart κ η = κ := by
  ext a s hs
  rw [← inter_union_sdiff s (mutuallySingularSetSlice κ η a)]
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add]
  have hm := measurableSet_mutuallySingularSetSlice κ η a
  simp only [measure_union (Disjoint.mono inter_subset_right le_rfl disjoint_sdiff_right)
    (hs.diff hm)]
  rw [singularPart_of_subset_mutuallySingularSetSlice (hs.inter hm) inter_subset_right,
    singularPart_of_subset_compl_mutuallySingularSetSlice (sdiff_subset_iff.mpr (by simp)),
    add_zero, withDensity_rnDeriv_of_subset_mutuallySingularSetSlice inter_subset_right,
    zero_add, withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice (hs.diff hm)
      (sdiff_subset_iff.mpr (by simp)), add_comm]

section EqZeroIff

/-
**ProbabilityTheory.Kernel.singularPart_eq_zero_iff_apply_eq_zero** 是 Mathlib 中的
一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：singularPart_eq_zero_iff_apply_eq_zero (κ η : Kernel α γ) [IsSFiniteKernel
 κ] [IsSFiniteKernel η] (a : α) : singularPart κ η a = 0 ↔ singularPart κ η a (m
utuallySingularSetSlice κ η a) = 0
参数：κ η : Kernel α γ；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `ProbabilityTheory.Kernel.measurableSet_mutuallySingularSetSlice`：measura
bleSet_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) : MeasurableSet (mutu
allySingularSetSlice κ η a)
· 使用引理 `ProbabilityTheory.Kernel.singularPart_compl_mutuallySingularSetSlice`：si
ngularPart_compl_mutuallySingularSetSlice (κ η : Kernel α γ) [IsSFiniteKernel κ]
 [IsSFiniteKernel η] (a : α) : singularPart κ η a (mutuall…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma singularPart_eq_zero_iff_apply_eq_zero (κ η : Kernel α γ) [IsSFiniteKernel κ]
    [IsSFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ singularPart κ η a (mutuallySingularSetSlice κ η a) = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) ∪ (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this, measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl,
    singularPart_compl_mutuallySingularSetSlice, add_zero]
/-
**ProbabilityTheory.Kernel.withDensity_rnDeriv_eq_zero_iff_apply_eq_zero** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：withDensity_rnDeriv_eq_zero_iff_apply_eq_zero (κ η : Kernel α γ) [IsFinite
Kernel κ] [IsFiniteKernel η] (a : α) : withDensity η (rnDeriv κ η) a = 0 ↔ withD
ensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a)ᶜ = 0
参数：κ η : Kernel α γ；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `ProbabilityTheory.Kernel.measurableSet_mutuallySingularSetSlice`：measura
bleSet_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) : MeasurableSet (mutu
allySingularSetSlice κ η a)
· 使用引理 `ProbabilityTheory.Kernel.withDensity_rnDeriv_mutuallySingularSetSlice`：w
ithDensity_rnDeriv_mutuallySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ
] [IsFiniteKernel η] (a : α) : withDensity η (rnDeriv κ η) …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma withDensity_rnDeriv_eq_zero_iff_apply_eq_zero (κ η : Kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0
      ↔ withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) ∪ (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this, measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl,
    withDensity_rnDeriv_mutuallySingularSetSlice, zero_add]
/-
**ProbabilityTheory.Kernel.singularPart_eq_zero_iff_absolutelyContinuous** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：singularPart_eq_zero_iff_absolutelyContinuous (κ η : Kernel α γ) [IsFinite
Kernel κ] [IsFiniteKernel η] (a : α) : singularPart κ η a = 0 ↔ κ a ≪ η a
参数：κ η : Kernel α γ；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_add_singularPart`：rnDeriv_add_singularP
art (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] : withDensity η (rn
Deriv κ η) + singularPart κ η = κ
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ProbabilityTheory.Kernel.withDensity_absolutelyContinuous`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probab
ilityTheory.Kernel α β}   [inst : ProbabilityTh…
· 使用引理 `MeasureTheory.Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingula
r`：eq_zero_of_absolutelyContinuous_of_mutuallySingular {μ ν : Measure α} (h_ac :
 μ ≪ ν) (h_ms : μ ⟂ₘ ν) : μ = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_left_iff`：add_left_iff {μ
₁ μ₂ ν : Measure α} : μ₁ + μ₂ ≪ ν ↔ μ₁ ≪ ν ∧ μ₂ ≪ ν
· 使用引理 `ProbabilityTheory.Kernel.mutuallySingular_singularPart`：mutuallySingular
_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
 singularPart κ η a ⟂ₘ η a
-/
lemma singularPart_eq_zero_iff_absolutelyContinuous (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ κ a ≪ η a := by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, add_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, add_zero]
    exact withDensity_absolutelyContinuous _ _
  rw [Measure.AbsolutelyContinuous.add_left_iff] at h
  exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2
    (mutuallySingular_singularPart _ _ _)
/-
**ProbabilityTheory.Kernel.withDensity_rnDeriv_eq_zero_iff_mutuallySingular** 是 
Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：withDensity_rnDeriv_eq_zero_iff_mutuallySingular (κ η : Kernel α γ) [IsFin
iteKernel κ] [IsFiniteKernel η] (a : α) : withDensity η (rnDeriv κ η) a = 0 ↔ κ 
a ⟂ₘ η a
参数：κ η : Kernel α γ；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_add_singularPart`：rnDeriv_add_singularP
art (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] : withDensity η (rn
Deriv κ η) + singularPart κ η = κ
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `ProbabilityTheory.Kernel.mutuallySingular_singularPart`：mutuallySingular
_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
 singularPart κ η a ⟂ₘ η a
· 使用引理 `MeasureTheory.Measure.MutuallySingular.self_iff`：self_iff (μ : Measure α
) : μ ⟂ₘ μ ↔ μ = 0
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.MutuallySingular.add_left_iff`：add_left_iff : μ₁ +
 μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `ProbabilityTheory.Kernel.withDensity_absolutelyContinuous`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probab
ilityTheory.Kernel α β}   [inst : ProbabilityTh…
-/
lemma withDensity_rnDeriv_eq_zero_iff_mutuallySingular (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0 ↔ κ a ⟂ₘ η a := by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, add_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, zero_add]
    exact mutuallySingular_singularPart _ _ _
  rw [Measure.MutuallySingular.add_left_iff] at h
  rw [← Measure.MutuallySingular.self_iff]
  exact h.1.mono_ac Measure.AbsolutelyContinuous.rfl
    (withDensity_absolutelyContinuous (κ := η) (rnDeriv κ η) a)
/-
**ProbabilityTheory.Kernel.singularPart_eq_zero_iff_measure_eq_zero** 是 Mathlib 
中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：singularPart_eq_zero_iff_measure_eq_zero (κ η : Kernel α γ) [IsFiniteKerne
l κ] [IsFiniteKernel η] (a : α) : singularPart κ η a = 0 ↔ κ a (mutuallySingular
SetSlice κ η a) = 0
参数：κ η : Kernel α γ；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_add_singularPart`：rnDeriv_add_singularP
art (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] : withDensity η (rn
Deriv κ η) + singularPart κ η = κ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FunLike.coe_add`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Add F] [inst_2 : Add β]   [IsAddApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用引理 `ProbabilityTheory.Kernel.withDensity_rnDeriv_mutuallySingularSetSlice`：w
ithDensity_rnDeriv_mutuallySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ
] [IsFiniteKernel η] (a : α) : withDensity η (rnDeriv κ η) …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `ProbabilityTheory.Kernel.measurableSet_mutuallySingularSetSlice`：measura
bleSet_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) : MeasurableSet (mutu
allySingularSetSlice κ η a)
· 使用引理 `ProbabilityTheory.Kernel.singularPart_eq_zero_iff_apply_eq_zero`：singula
rPart_eq_zero_iff_apply_eq_zero (κ η : Kernel α γ) [IsSFiniteKernel κ] [IsSFinit
eKernel η] (a : α) : singularPart κ η a = 0 ↔ singula…
-/
lemma singularPart_eq_zero_iff_measure_eq_zero (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ κ a (mutuallySingularSetSlice κ η a) = 0 := by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [Kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)
    (measurableSet_mutuallySingularSetSlice κ η a)
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add,
    withDensity_rnDeriv_mutuallySingularSetSlice κ η, zero_add] at h_eq_add
  rw [← h_eq_add]
  exact singularPart_eq_zero_iff_apply_eq_zero κ η a
/-
**ProbabilityTheory.Kernel.withDensity_rnDeriv_eq_zero_iff_measure_eq_zero** 是 M
athlib 中的一个引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：withDensity_rnDeriv_eq_zero_iff_measure_eq_zero (κ η : Kernel α γ) [IsFini
teKernel κ] [IsFiniteKernel η] (a : α) : withDensity η (rnDeriv κ η) a = 0 ↔ κ a
 (mutuallySingularSetSlice κ η a)ᶜ = 0
参数：κ η : Kernel α γ；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_add_singularPart`：rnDeriv_add_singularP
art (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] : withDensity η (rn
Deriv κ η) + singularPart κ η = κ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FunLike.coe_add`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Add F] [inst_2 : Add β]   [IsAddApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用引理 `ProbabilityTheory.Kernel.singularPart_compl_mutuallySingularSetSlice`：si
ngularPart_compl_mutuallySingularSetSlice (κ η : Kernel α γ) [IsSFiniteKernel κ]
 [IsSFiniteKernel η] (a : α) : singularPart κ η a (mutuall…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `ProbabilityTheory.Kernel.measurableSet_mutuallySingularSetSlice`：measura
bleSet_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) : MeasurableSet (mutu
allySingularSetSlice κ η a)
· 使用引理 `ProbabilityTheory.Kernel.withDensity_rnDeriv_eq_zero_iff_apply_eq_zero`：
withDensity_rnDeriv_eq_zero_iff_apply_eq_zero (κ η : Kernel α γ) [IsFiniteKernel
 κ] [IsFiniteKernel η] (a : α) : withDensity η (rnDeriv κ η)…
-/
lemma withDensity_rnDeriv_eq_zero_iff_measure_eq_zero (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0 ↔ κ a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [Kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)ᶜ
    (measurableSet_mutuallySingularSetSlice κ η a).compl
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add,
    singularPart_compl_mutuallySingularSetSlice κ η, add_zero] at h_eq_add
  rw [← h_eq_add]
  exact withDensity_rnDeriv_eq_zero_iff_apply_eq_zero κ η a

end EqZeroIff

/-- The set of points `a : α` such that `κ a ≪ η a` is measurable. -/
@[measurability]
/-
**ProbabilityTheory.Kernel.measurableSet_absolutelyContinuous** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：measurableSet_absolutelyContinuous (κ η : Kernel α γ) [IsFiniteKernel κ] [
IsFiniteKernel η] : MeasurableSet {a | κ a ≪ η a}
参数：κ η : Kernel α γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left`：measurable_kerne
l_prodMk_left [IsSFiniteKernel κ] {t : Set (α × β)} (ht : MeasurableSet t) : Mea
surable fun a => κ a (Prod.mk a ⁻¹' t)
· 使用引理 `ProbabilityTheory.Kernel.measurableSet_mutuallySingularSet`：measurableSe
t_mutuallySingularSet (κ η : Kernel α γ) : MeasurableSet (mutuallySingularSet κ 
η)
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal

--- 原说明 ---
The set of points `a : α` such that `κ a ≪ η a` is measurable.
-/
lemma measurableSet_absolutelyContinuous (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a ≪ η a} := by
  simp_rw [← singularPart_eq_zero_iff_absolutelyContinuous,
    singularPart_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prodMk_left (measurableSet_mutuallySingularSet κ η)
    (measurableSet_singleton 0)

/-- The set of points `a : α` such that `κ a ⟂ₘ η a` is measurable. -/
@[measurability]
/-
**ProbabilityTheory.Kernel.measurableSet_mutuallySingular** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.Kernel`。
形式化陈述：measurableSet_mutuallySingular (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFi
niteKernel η] : MeasurableSet {a | κ a ⟂ₘ η a}
参数：κ η : Kernel α γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left`：measurable_kerne
l_prodMk_left [IsSFiniteKernel κ] {t : Set (α × β)} (ht : MeasurableSet t) : Mea
surable fun a => κ a (Prod.mk a ⁻¹' t)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `ProbabilityTheory.Kernel.measurableSet_mutuallySingularSet`：measurableSe
t_mutuallySingularSet (κ η : Kernel α γ) : MeasurableSet (mutuallySingularSet κ 
η)
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal

--- 原说明 ---
The set of points `a : α` such that `κ a ⟂ₘ η a` is measurable.
-/
lemma measurableSet_mutuallySingular (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a ⟂ₘ η a} := by
  simp_rw [← withDensity_rnDeriv_eq_zero_iff_mutuallySingular,
    withDensity_rnDeriv_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prodMk_left (measurableSet_mutuallySingularSet κ η).compl
    (measurableSet_singleton 0)

@[simp]
/-
**ProbabilityTheory.Kernel.singularPart_self** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：singularPart_self (κ : Kernel α γ) [IsFiniteKernel κ] : κ.singularPart κ =
 0
参数：κ : Kernel α γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ProbabilityTheory.Kernel.instIsZeroApplyMeasure`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsZeroApply (Proba
bilityTheory.Kernel α β) α (MeasureTh…
· 使用引理 `ProbabilityTheory.Kernel.singularPart_eq_zero_iff_absolutelyContinuous`：
singularPart_eq_zero_iff_absolutelyContinuous (κ η : Kernel α γ) [IsFiniteKernel
 κ] [IsFiniteKernel η] (a : α) : singularPart κ η a = 0 ↔ κ …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.refl`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α), μ.AbsolutelyContinuous μ
-/
lemma singularPart_self (κ : Kernel α γ) [IsFiniteKernel κ] : κ.singularPart κ = 0 := by
  ext : 1; rw [zero_apply, singularPart_eq_zero_iff_absolutelyContinuous]

section Unique

variable {ξ : Kernel α γ} {f : α → γ → ℝ≥0∞} [IsFiniteKernel η]

omit hαγ in
/-
**ProbabilityTheory.Kernel.eq_rnDeriv_measure** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：eq_rnDeriv_measure (h : κ = η.withDensity f + ξ) (hf : Measurable (Functio
n.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) : f a =ᵐ[η a] ∂(κ a)/∂(η a)
参数：h : κ = η.withDensity f + ξ；hf : Measurable (Function.uncurry f)；a : α；hξ : ξ
 a ⟂ₘ η a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.Measure.eq_rnDeriv₀`：eq_rnDeriv₀ [SigmaFinite ν] {s : Meas
ure α} {f : α -> Real>=0∞} (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s +
 ν.withDensity f) : f =…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
lemma eq_rnDeriv_measure (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    f a =ᵐ[η a] ∂(κ a)/∂(η a) := by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h, add_apply, η.withDensity_apply hf, add_comm]
  exact (κ a).eq_rnDeriv₀ (hf.comp measurable_prodMk_left).aemeasurable hξ this

omit hαγ in
/-
**ProbabilityTheory.Kernel.eq_singularPart_measure** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：eq_singularPart_measure (h : κ = η.withDensity f + ξ) (hf : Measurable (Fu
nction.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) : ξ a = (κ a).singularPart (η a)
参数：h : κ = η.withDensity f + ξ；hf : Measurable (Function.uncurry f)；a : α；hξ : ξ
 a ⟂ₘ η a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.Measure.eq_singularPart`：eq_singularPart {s : Measure α} {
f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensi
ty f) : s = μ.singularPart …
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
lemma eq_singularPart_measure (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    ξ a = (κ a).singularPart (η a) := by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h, add_apply, η.withDensity_apply hf, add_comm]
  exact (κ a).eq_singularPart (hf.comp measurable_prodMk_left) hξ this

variable [IsFiniteKernel κ] {a : α}
/-
**ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.Kernel`。
形式化陈述：rnDeriv_eq_rnDeriv_measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.eq_rnDeriv_measure`：eq_rnDeriv_measure (h : κ =
 η.withDensity f + ξ) (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂
ₘ η a) : f a =ᵐ[η a] ∂(κ a)/∂(η a…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_add_singularPart`：rnDeriv_add_singularP
art (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] : withDensity η (rn
Deriv κ η) + singularPart κ η = κ
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDeriv`：measurable_rnDeriv (κ η : K
ernel α γ) : Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2)
· 使用引理 `ProbabilityTheory.Kernel.mutuallySingular_singularPart`：mutuallySingular
_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
 singularPart κ η a ⟂ₘ η a
-/
lemma rnDeriv_eq_rnDeriv_measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a) :=
  eq_rnDeriv_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η) a
    (mutuallySingular_singularPart κ η a)
/-
**ProbabilityTheory.Kernel.singularPart_eq_singularPart_measure** 是 Mathlib 中的一个
引理，位于命名空间 `ProbabilityTheory.Kernel`。
形式化陈述：singularPart_eq_singularPart_measure : singularPart κ η a = (κ a).singular
Part (η a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.Kernel.eq_singularPart_measure`：eq_singularPart_measur
e (h : κ = η.withDensity f + ξ) (hf : Measurable (Function.uncurry f)) (a : α) (
hξ : ξ a ⟂ₘ η a) : ξ a = (κ a).singula…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_add_singularPart`：rnDeriv_add_singularP
art (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] : withDensity η (rn
Deriv κ η) + singularPart κ η = κ
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDeriv`：measurable_rnDeriv (κ η : K
ernel α γ) : Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2)
· 使用引理 `ProbabilityTheory.Kernel.mutuallySingular_singularPart`：mutuallySingular
_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
 singularPart κ η a ⟂ₘ η a
-/
lemma singularPart_eq_singularPart_measure : singularPart κ η a = (κ a).singularPart (η a) :=
  eq_singularPart_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η) a
    (mutuallySingular_singularPart κ η a)
/-
**ProbabilityTheory.Kernel.eq_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry.Kernel`。
形式化陈述：eq_rnDeriv (h : κ = η.withDensity f + ξ) (hf : Measurable (Function.uncurr
y f)) (a : α) (hξ : ξ a ⟂ₘ η a) : f a =ᵐ[η a] rnDeriv κ η a
参数：h : κ = η.withDensity f + ξ；hf : Measurable (Function.uncurry f)；a : α；hξ : ξ
 a ⟂ₘ η a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.eq_rnDeriv_measure`：eq_rnDeriv_measure (h : κ =
 η.withDensity f + ξ) (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂
ₘ η a) : f a =ᵐ[η a] ∂(κ a)/∂(η a…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
-/
lemma eq_rnDeriv (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    f a =ᵐ[η a] rnDeriv κ η a :=
  (eq_rnDeriv_measure h hf a hξ).trans rnDeriv_eq_rnDeriv_measure.symm
/-
**ProbabilityTheory.Kernel.eq_singularPart** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.Kernel`。
形式化陈述：eq_singularPart (h : κ = η.withDensity f + ξ) (hf : Measurable (Function.u
ncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) : ξ a = singularPart κ η a
参数：h : κ = η.withDensity f + ξ；hf : Measurable (Function.uncurry f)；a : α；hξ : ξ
 a ⟂ₘ η a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.Kernel.eq_singularPart_measure`：eq_singularPart_measur
e (h : κ = η.withDensity f + ξ) (hf : Measurable (Function.uncurry f)) (a : α) (
hξ : ξ a ⟂ₘ η a) : ξ a = (κ a).singula…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.singularPart_eq_singularPart_measure`：singularP
art_eq_singularPart_measure : singularPart κ η a = (κ a).singularPart (η a)
-/
lemma eq_singularPart (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    ξ a = singularPart κ η a :=
  (eq_singularPart_measure h hf a hξ).trans singularPart_eq_singularPart_measure.symm

end Unique

/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hκ : IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (withDensity η (rnDeriv κ η)) := by
  refine ⟨κ.bound, κ.bound_lt_top, fun a ↦ ?_⟩
  rw [Kernel.withDensity_apply', setLIntegral_univ]
  swap; · exact measurable_rnDeriv κ η
  rw [lintegral_congr_ae rnDeriv_eq_rnDeriv_measure]
  exact Measure.lintegral_rnDeriv_le.trans (measure_le_bound _ _ _)
/-
**ProbabilityTheory.Kernel.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory.Kernel`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hκ : IsFiniteKernel κ] [IsFiniteKernel η] : IsFiniteKernel (singularPart κ η) := by
  refine ⟨κ.bound, κ.bound_lt_top, fun a ↦ ?_⟩
  have h : withDensity η (rnDeriv κ η) a univ + singularPart κ η a univ = κ a univ := by
    conv_rhs => rw [← rnDeriv_add_singularPart κ η]
    simp
  exact (self_le_add_left _ _).trans (h.le.trans (measure_le_bound _ _ _))

/-- For two kernels `κ, η`, the singular part of `κ a` with respect to `η a` is a measurable
function of `a`. -/
/-
**ProbabilityTheory.Kernel.measurable_singularPart** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：measurable_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKer
nel η] : Measurable (fun a => (κ a).singularPart (η a))
参数：κ η : Kernel α γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measurable_of_measurable_coe`：measurable_of_measur
able_coe (f : β -> Measure α) (h : forall (s : Set α), MeasurableSet s -> Measur
able fun b => f b s) : Measurable f
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.singularPart_eq_singularPart_measure`：singularP
art_eq_singularPart_measure : singularPart κ η a = (κ a).singularPart (η a)
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.add`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory
.Kernel α β)   [ProbabilityTheory.…
· 使用定理 `ProbabilityTheory.Kernel.singularPart_def`：∀ {α : Type u_3} {γ : Type u_
4} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}   [hαγ : MeasurableSpace.Co
untableOrCountablyGenerated α γ…
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…

--- 原说明 ---
For two kernels `κ, η`, the singular part of `κ a` with respect to `η a` is a me
asurable
function of `a`.
-/
lemma measurable_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ (κ a).singularPart (η a)) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs ↦ ?_)
  simp_rw [← κ.singularPart_eq_singularPart_measure, κ.singularPart_def η]
  exact Kernel.measurable_coe _ hs
/-
**ProbabilityTheory.Kernel.rnDeriv_self** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.Kernel`。
形式化陈述：rnDeriv_self (κ : Kernel α γ) [IsFiniteKernel κ] (a : α) : rnDeriv κ κ a =
ᵐ[κ a] 1
参数：κ : Kernel α γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用引理 `MeasureTheory.Measure.rnDeriv_self`：rnDeriv_self (μ : Measure α) [SigmaF
inite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ => 1
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
-/
lemma rnDeriv_self (κ : Kernel α γ) [IsFiniteKernel κ] (a : α) : rnDeriv κ κ a =ᵐ[κ a] 1 :=
  (κ.rnDeriv_eq_rnDeriv_measure).trans (κ a).rnDeriv_self
/-
**ProbabilityTheory.Kernel.rnDeriv_singularPart** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：rnDeriv_singularPart (κ ν : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel
 ν] (a : α) : rnDeriv (singularPart κ ν) ν a =ᵐ[ν a] 0
参数：κ ν : Kernel α γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_zero`：rnDeriv_eq_zero (μ ν : Measure α)
 [μ.HaveLebesgueDecomposition ν] : μ.rnDeriv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.instIsFiniteKernelSingularPart`：∀ {α : Type u_1
} {γ : Type u_2} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {κ η : Probab
ilityTheory.Kernel α γ}   [hαγ : MeasurableSp…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用引理 `ProbabilityTheory.Kernel.mutuallySingular_singularPart`：mutuallySingular
_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
 singularPart κ η a ⟂ₘ η a
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma rnDeriv_singularPart (κ ν : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    rnDeriv (singularPart κ ν) ν a =ᵐ[ν a] 0 := by
  filter_upwards [(singularPart κ ν).rnDeriv_eq_rnDeriv_measure,
    (Measure.rnDeriv_eq_zero _ _).mpr (mutuallySingular_singularPart κ ν a)] with x h1 h2
  rw [h1, h2]
/-
**ProbabilityTheory.Kernel.rnDeriv_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：rnDeriv_lt_top (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a
 : α} : forallᵐ x ∂(η a), rnDeriv κ η a x < ∞
参数：κ η : Kernel α γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_ne_top`：rnDeriv_ne_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x != ∞
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma rnDeriv_lt_top (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} :
    ∀ᵐ x ∂(η a), rnDeriv κ η a x < ∞ := by
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure, (κ a).rnDeriv_ne_top _]
    with x heq htop using heq ▸ htop.lt_top
/-
**ProbabilityTheory.Kernel.rnDeriv_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.Kernel`。
形式化陈述：rnDeriv_ne_top (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a
 : α} : forallᵐ x ∂(η a), rnDeriv κ η a x != ∞
参数：κ η : Kernel α γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_lt_top`：rnDeriv_lt_top (κ η : Kernel α 
γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} : forallᵐ x ∂(η a), rnDeriv κ η
 a x < ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma rnDeriv_ne_top (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} :
    ∀ᵐ x ∂(η a), rnDeriv κ η a x ≠ ∞ := by
  filter_upwards [κ.rnDeriv_lt_top η] with a h using h.ne
/-
**ProbabilityTheory.Kernel.rnDeriv_pos** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：rnDeriv_pos [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (ha : κ a ≪ η a)
 : forallᵐ x ∂(κ a), 0 < rnDeriv κ η a x
参数：ha : κ a ≪ η a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_pos`：rnDeriv_pos [HaveLebesgueDecompositio
n μ ν] (hμν : μ ≪ ν) : forallᵐ x ∂μ, 0 < μ.rnDeriv ν x
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma rnDeriv_pos [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (ha : κ a ≪ η a) :
    ∀ᵐ x ∂(κ a), 0 < rnDeriv κ η a x := by
  filter_upwards [ha.ae_le κ.rnDeriv_eq_rnDeriv_measure, Measure.rnDeriv_pos ha]
    with x heq hpos using heq ▸ hpos
/-
**ProbabilityTheory.Kernel.rnDeriv_toReal_pos** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.Kernel`。
形式化陈述：rnDeriv_toReal_pos [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a 
≪ η a) : forallᵐ x ∂(κ a), 0 < (rnDeriv κ η a x).toReal
参数：h : κ a ≪ η a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_ne_top`：rnDeriv_ne_top (κ η : Kernel α 
γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} : forallᵐ x ∂(η a), rnDeriv κ η
 a x != ∞
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_pos`：rnDeriv_pos [IsFiniteKernel κ] [Is
FiniteKernel η] {a : α} (ha : κ a ≪ η a) : forallᵐ x ∂(κ a), 0 < rnDeriv κ η a x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma rnDeriv_toReal_pos [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a) :
    ∀ᵐ x ∂(κ a), 0 < (rnDeriv κ η a x).toReal := by
  filter_upwards [rnDeriv_pos h, h.ae_le (rnDeriv_ne_top κ _)] with x h0 htop
  simp_all only [pos_iff_ne_zero, ne_eq, ENNReal.toReal_pos, not_false_eq_true]
/-
**ProbabilityTheory.Kernel.rnDeriv_add** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.Kernel`。
形式化陈述：rnDeriv_add (κ ν η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] [Is
FiniteKernel η] (a : α) : rnDeriv (κ + ν) η a =ᵐ[η a] rnDeriv κ η a + rnDeriv ν 
η a
参数：κ ν η : Kernel α γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_add`：rnDeriv_add (ν₁ ν₂ μ : Measure α) [Is
FiniteMeasure ν₁] [IsFiniteMeasure ν₂] [ν₁.HaveLebesgueDecomposition μ] [ν₂.Have
LebesgueDecomposition μ…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.add_left`：∀ {α : Type u_
1} {m : MeasurableSpace α} {μ ν μ' : MeasureTheory.Measure α} [μ.HaveLebesgueDec
omposition ν]   [μ'.HaveLebesgueDecomposition …
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用定理 `ProbabilityTheory.IsFiniteKernel.add`：∀ {α : Type u_1} {β : Type u_2} {m
α : MeasurableSpace α} {mβ : MeasurableSpace β} (κ η : ProbabilityTheory.Kernel 
α β)   [ProbabilityTheory.…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ProbabilityTheory.Kernel.instIsAddApplyMeasure`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β},   IsAddApply (Probabi
lityTheory.Kernel α β) α (MeasureThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rnDeriv_add (κ ν η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] [IsFiniteKernel η]
    (a : α) :
    rnDeriv (κ + ν) η a =ᵐ[η a] rnDeriv κ η a + rnDeriv ν η a := by
  filter_upwards [(κ + ν).rnDeriv_eq_rnDeriv_measure, κ.rnDeriv_eq_rnDeriv_measure,
    ν.rnDeriv_eq_rnDeriv_measure, (κ a).rnDeriv_add (ν a) (η a)] with x h1 h2 h3 h4
  simp [h1, h2, h3, h4]
/-
**ProbabilityTheory.Kernel.setLIntegral_rnDeriv_le** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.Kernel`。
形式化陈述：setLIntegral_rnDeriv_le {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKer
nel η] {a : α} {s : Set γ} (hs : MeasurableSet s) : ∫⁻ c in s, κ.rnDeriv η a c ∂
η a <= κ a s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_congr_fun_ae`：setLIntegral_congr_fun_ae {f g 
: α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s 
-> f x = g x) : ∫⁻ x in s, f …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_apply'`：withDensity_apply' [SFinite μ] (f : α 
-> Real>=0∞) (s : Set α) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_le`：withDensity_rnDeriv_le (μ 
ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ
-/
lemma setLIntegral_rnDeriv_le {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    {a : α} {s : Set γ} (hs : MeasurableSet s) :
    ∫⁻ c in s, κ.rnDeriv η a c ∂η a ≤ κ a s := by
  rw [setLIntegral_congr_fun_ae hs ((κ.rnDeriv_eq_rnDeriv_measure).mono (fun x hx _ ↦ hx)),
    ← withDensity_apply' _ s]
  exact (κ a).withDensity_rnDeriv_le _ _
/-
**ProbabilityTheory.Kernel.setLIntegral_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory.Kernel`。
形式化陈述：setLIntegral_rnDeriv {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel
 η] {a : α} (h : κ a ≪ η a) {s : Set γ} (hs : MeasurableSet s) : ∫⁻ c in s, κ.rn
Deriv η a c ∂η a = κ a s
参数：h : κ a ≪ η a；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_congr_fun_ae`：setLIntegral_congr_fun_ae {f g 
: α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s 
-> f x = g x) : ∫⁻ x in s, f …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
-/
lemma setLIntegral_rnDeriv {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    {a : α} (h : κ a ≪ η a) {s : Set γ} (hs : MeasurableSet s) :
    ∫⁻ c in s, κ.rnDeriv η a c ∂η a = κ a s := by
  rw [setLIntegral_congr_fun_ae hs ((κ.rnDeriv_eq_rnDeriv_measure).mono (fun x hx _ ↦ hx)),
    ← withDensity_apply _ hs, (κ a).withDensity_rnDeriv_eq _ h]
/-
**ProbabilityTheory.Kernel.lintegral_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.Kernel`。
形式化陈述：lintegral_rnDeriv {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
 {a : α} (h : κ a ≪ η a) : ∫⁻ c, κ.rnDeriv η a c ∂η a = κ a univ
参数：h : κ a ≪ η a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用引理 `ProbabilityTheory.Kernel.setLIntegral_rnDeriv`：setLIntegral_rnDeriv {κ η
 : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a) {s 
: Set γ} (hs : MeasurableSet s) : ∫…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma lintegral_rnDeriv {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    {a : α} (h : κ a ≪ η a) :
    ∫⁻ c, κ.rnDeriv η a c ∂η a = κ a univ := by
  rw [← setLIntegral_univ, setLIntegral_rnDeriv h MeasurableSet.univ]
/-
**ProbabilityTheory.Kernel.withDensity_rnDeriv_le** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：withDensity_rnDeriv_le (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKern
el η] (a : α) : η.withDensity (κ.rnDeriv η) a <= κ a
参数：κ η : Kernel α γ；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.le_intro`：le_intro (h : forall s, MeasurableSet s 
-> s.Nonempty -> μ₁ s <= μ₂ s) : μ₁ <= μ₂
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply'`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (
κ : ProbabilityTheory.Kernel α β)…
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDeriv`：measurable_rnDeriv (κ η : K
ernel α γ) : Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2)
· 使用引理 `ProbabilityTheory.Kernel.setLIntegral_rnDeriv_le`：setLIntegral_rnDeriv_l
e {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} {s : Set γ} (
hs : MeasurableSet s) : ∫⁻ c in s, κ.r…
-/
lemma withDensity_rnDeriv_le (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    η.withDensity (κ.rnDeriv η) a ≤ κ a := by
  refine Measure.le_intro (fun s hs _ ↦ ?_)
  rw [Kernel.withDensity_apply']
  · exact setLIntegral_rnDeriv_le hs
  · exact κ.measurable_rnDeriv _
/-
**ProbabilityTheory.Kernel.withDensity_rnDeriv_eq** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.Kernel`。
形式化陈述：withDensity_rnDeriv_eq [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : 
κ a ≪ η a) : η.withDensity (κ.rnDeriv η) a = κ a
参数：h : κ a ≪ η a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
· 使用引理 `ProbabilityTheory.Kernel.measurable_rnDeriv`：measurable_rnDeriv (κ η : K
ernel α γ) : Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用定理 `MeasureTheory.withDensity_congr_ae`：withDensity_congr_ae {f g : α -> Rea
l>=0∞} (h : f =ᵐ[μ] g) : μ.withDensity f = μ.withDensity g
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
-/
lemma withDensity_rnDeriv_eq [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a) :
    η.withDensity (κ.rnDeriv η) a = κ a := by
  rw [Kernel.withDensity_apply]
  swap; · exact κ.measurable_rnDeriv _
  have h_ae := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  rw [MeasureTheory.withDensity_congr_ae h_ae, (κ a).withDensity_rnDeriv_eq _ h]
/-
**ProbabilityTheory.Kernel.rnDeriv_withDensity** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.Kernel`。
形式化陈述：rnDeriv_withDensity [IsFiniteKernel κ] {f : α -> γ -> Real>=0∞} [IsFiniteK
ernel (withDensity κ f)] (hf : Measurable (Function.uncurry f)) (a : α) : (κ.wit
hDensity f).rnDeriv κ a =ᵐ[κ a] f a
参数：withDensity κ f；hf : Measurable (Function.uncurry f)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用定理 `Measurable.of_uncurry_left`：Measurable.of_uncurry_left {f : α -> β -> γ}
 (hf : Measurable (uncurry f)) {x : α} : Measurable (f x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity`：rnDeriv_withDensity (ν : Meas
ure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) : (ν.withDensity 
f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.withDensity_apply`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β → ENNReal}   (κ
 : ProbabilityTheory.Kernel α β)…
-/
lemma rnDeriv_withDensity [IsFiniteKernel κ] {f : α → γ → ℝ≥0∞} [IsFiniteKernel (withDensity κ f)]
    (hf : Measurable (Function.uncurry f)) (a : α) :
    (κ.withDensity f).rnDeriv κ a =ᵐ[κ a] f a := by
  have h_ae := (κ.withDensity f).rnDeriv_eq_rnDeriv_measure (η := κ) (a := a)
  have hf' : ∀ a, Measurable (f a) := fun _ ↦ hf.of_uncurry_left
  filter_upwards [h_ae, (κ a).rnDeriv_withDensity (hf' a)] with x hx1 hx2
  rw [hx1, κ.withDensity_apply hf, hx2]
/-
**ProbabilityTheory.Kernel.rnDeriv_eq_one_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.Kernel`。
形式化陈述：rnDeriv_eq_one_iff_eq [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h_ac 
: κ a ≪ η a) : (forallᵐ b ∂(η a), κ.rnDeriv η a b = 1) ↔ κ a = η a
参数：h_ac : κ a ≪ η a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_one_iff_eq`：rnDeriv_eq_one_iff_eq [Have
LebesgueDecomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν) : μ.rnDeriv ν =ᵐ[ν] 1 ↔
 μ = ν
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.Kernel.rnDeriv_eq_rnDeriv_measure`：rnDeriv_eq_rnDeriv_
measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rnDeriv_eq_one_iff_eq [IsFiniteKernel κ] [IsFiniteKernel η] {a : α}
    (h_ac : κ a ≪ η a) :
    (∀ᵐ b ∂(η a), κ.rnDeriv η a b = 1) ↔ κ a = η a := by
  rw [← Measure.rnDeriv_eq_one_iff_eq h_ac]
  refine eventually_congr ?_
  filter_upwards [rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with c hc
  rw [hc, Pi.one_apply]

end ProbabilityTheory.Kernel

