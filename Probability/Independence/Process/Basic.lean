/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Probability.Independence.Basic

/-!
# Independence of stochastic processes

We prove that a stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$ if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independent from $Y$.

We prove that two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent.
We prove an analogous condition for a family of stochastic processes.

## Tags

independence, stochastic processes
-/

public section

open MeasureTheory MeasurableSpace Set

namespace ProbabilityTheory

variable {S T Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α Ω} {P : Measure α}

/-- If `X` is a process independent from `Y` and for all `i`, `X' i` is almost everywhere equal
to `X i`, then `X'` is also independent from `Y`. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable. -/
/-
**ProbabilityTheory.Kernel.IndepFun.process_congr_left** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {m
α : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : MeasureTheory.M
easure α} {𝓧 : S → Type u_5} {𝓨 : Type u_6}   [inst : (i : S) → MeasurableSpace 
(𝓧 i)] [inst_1 : MeasurableSpace 𝓨] {X X' : (i : S) → Ω → 𝓧 i} {Y : Ω → 𝓨},   Pr
obabilityTheory.Kernel.IndepFun (fun ω i => X i ω) Y κ P →     (∀ (i : S), ∀ᵐ (a
 : α) ∂P, X i =ᵐ[κ a] X' i) → ProbabilityTheory.Kernel.IndepFun (fun ω i => X' i
 ω) Y κ P
参数：i : S；𝓧 i；i : S；fun ω i => X i ω；∀ (i : S), ∀ᵐ (a : α) ∂P, X i =ᵐ[κ a] X' i；f
un ω i => X' i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MeasurableSet.eq_preimage_restrict_countable`：∀ {ι : Type 
u_2} {α : ι → Type u_1} [inst : (i : ι) → MeasurableSpace (α i)] {s : Set ((i : 
ι) → α i)},   MeasurableSet s → ∃ I t, I.Countab…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.ae_eq_set_inter`：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
· 使用定理 `Filter.EventuallyEq.preimage`：∀ {α : Type u} {β : Type v} {l : Filter α}
 {f g : α → β}, f =ᶠ[l] g → ∀ (s : Set β), f ⁻¹' s =ᶠ[l] g ⁻¹' s
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `X` is a process independent from `Y` and for all `i`, `X' i` is almost every
where equal
to `X i`, then `X'` is also independent from `Y`. This implies that independence
 results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable.
-/
lemma IndepFun.process_congr_left {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X X' : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (h1 : IndepFun (fun ω i ↦ X i ω) Y κ P) (h2 : ∀ i, ∀ᵐ a ∂P, X i =ᵐ[κ a] X' i) :
    IndepFun (fun ω i ↦ X' i ω) Y κ P := by
  rintro - - ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  have : ∀ᵐ a ∂P, κ a (((fun ω i ↦ X i ω) ⁻¹' s) ∩ (Y ⁻¹' t)) =
      κ a ((fun ω i ↦ X i ω) ⁻¹' s) * κ a (Y ⁻¹' t) :=
    h1 ((fun ω i ↦ X i ω) ⁻¹' s) (Y ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  obtain ⟨I, u, hI, rfl⟩ : ∃ (I : Set S) (u : Set (Π i : I, 𝓧 i)),
      I.Countable ∧ s = I.domRestrict ⁻¹' u := hs.eq_preimage_restrict_countable
  have aux (f : (i : S) → Ω → 𝓧 i) : (fun ω i ↦ f i ω) ⁻¹' I.domRestrict ⁻¹' u =
      (fun ω (i : I) ↦ f i ω) ⁻¹' u := rfl
  simp_rw [aux] at *
  have _ : Countable I := hI.to_subtype
  have h : ∀ᵐ a ∂P, (fun ω (i : I) ↦ X i ω) =ᵐ[κ a] (fun ω (i : I) ↦ X' i ω) := by
    filter_upwards [ae_all_iff.2 fun (i : I) ↦ h2 i] with
      a (ha : ∀ (i : I), ∀ᵐ ω ∂κ a, X i ω = X' i ω)
    filter_upwards [ae_all_iff.2 ha] with ω hω using by simp [hω]
  filter_upwards [this, h] with a ha1 ha2
  refine .trans (measure_congr (ae_eq_set_inter (ha2.symm.preimage _) .rfl)) (ha1.trans ?_)
  congr 1
  exact measure_congr (ha2.preimage _)

/-- If `X` is a process independent from `Y` and for all `i`, `X' i` is almost everywhere equal
to `X i`, then `X'` is also independent from `Y`. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable. -/
/-
**ProbabilityTheory.Kernel.IndepFun.process_congr_right** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.Kernel.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {m
α : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : MeasureTheory.M
easure α} {𝓧 : S → Type u_5} {𝓨 : Type u_6}   [inst : (i : S) → MeasurableSpace 
(𝓧 i)] [inst_1 : MeasurableSpace 𝓨] {X X' : (i : S) → Ω → 𝓧 i} {Y : Ω → 𝓨},   Pr
obabilityTheory.Kernel.IndepFun Y (fun ω i => X i ω) κ P →     (∀ (i : S), ∀ᵐ (a
 : α) ∂P, X i =ᵐ[κ a] X' i) → ProbabilityTheory.Kernel.IndepFun Y (fun ω i => X'
 i ω) κ P
参数：i : S；𝓧 i；i : S；fun ω i => X i ω；∀ (i : S), ∀ᵐ (a : α) ∂P, X i =ᵐ[κ a] X' i；f
un ω i => X' i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.symm`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
   {κ : ProbabilityTheory.Ke…
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_congr_left`：∀ {S : Type u_1} {
Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}  
 {κ : ProbabilityTheory.Kernel α Ω} {P : M…

--- 原说明 ---
If `X` is a process independent from `Y` and for all `i`, `X' i` is almost every
where equal
to `X i`, then `X'` is also independent from `Y`. This implies that independence
 results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable.
-/
lemma IndepFun.process_congr_right {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X X' : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (h1 : IndepFun Y (fun ω i ↦ X i ω) κ P) (h2 : ∀ i, ∀ᵐ a ∂P, X i =ᵐ[κ a] X' i) :
    IndepFun Y (fun ω i ↦ X' i ω) κ P :=
  (h1.symm.process_congr_left h2).symm

/-- If `X` and `Y` are two independent processes and for all `i`, `X' i` is almost everywhere equal
to `X i`, and for all `j`, `Y' j` is almost everywhere equal to `Y j`,
then `X'` is independent from `Y'`. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable. -/
/-
**ProbabilityTheory.Kernel.IndepFun.process_congr** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.Kernel.IndepFun`。
形式化陈述：∀ {S : Type u_1} {T : Type u_2} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α
 : Type u_4} {mα : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : 
MeasureTheory.Measure α} {𝓧 : S → Type u_5} {𝓨 : T → Type u_6}   [inst : (i : S)
 → MeasurableSpace (𝓧 i)] [inst_1 : (j : T) → MeasurableSpace (𝓨 j)] {X X' : (i 
: S) → Ω → 𝓧 i}   {Y Y' : (j : T) → Ω → 𝓨 j},   ProbabilityTheory.Kernel.IndepFu
n (fun ω i => X i ω) (fun ω j => Y j ω) κ P →     (∀ (i : S), ∀ᵐ (a : α) ∂P, X i
 =ᵐ[κ a] X' i) →       (∀ (j : T), ∀ᵐ (a : α) ∂P, Y j =ᵐ[κ a] Y' j) →         Pr
obabilityTheory.Kernel.IndepFun (fun ω i => X' i ω) (fun ω j => Y' j ω) κ P
参数：i : S；𝓧 i；j : T；𝓨 j；i : S；j : T；fun ω i => X i ω；fun ω j => Y j ω；∀ (i : S), 
∀ᵐ (a : α) ∂P, X i =ᵐ[κ a] X' i；∀ (j : T), ∀ᵐ (a : α) ∂P, Y j =ᵐ[κ a] Y' j；fun ω
 i => X' i ω；fun ω j => Y' j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_congr_left`：∀ {S : Type u_1} {
Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}  
 {κ : ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_congr_right`：∀ {S : Type u_1} 
{Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α} 
  {κ : ProbabilityTheory.Kernel α Ω} {P : M…

--- 原说明 ---
If `X` and `Y` are two independent processes and for all `i`, `X' i` is almost e
verywhere equal
to `X i`, and for all `j`, `Y' j` is almost everywhere equal to `Y j`,
then `X'` is independent from `Y'`. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable.
-/
lemma IndepFun.process_congr {𝓧 : S → Type*} {𝓨 : T → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [∀ j, MeasurableSpace (𝓨 j)] {X X' : (i : S) → Ω → 𝓧 i}
    {Y Y' : (j : T) → Ω → (𝓨 j)} (hXY : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) κ P)
    (hX : ∀ i, ∀ᵐ a ∂P, X i =ᵐ[κ a] X' i) (hY : ∀ j, ∀ᵐ a ∂P, Y j =ᵐ[κ a] Y' j) :
    IndepFun (fun ω i ↦ X' i ω) (fun ω j ↦ Y' j ω) κ P :=
  (hXY.process_congr_right hY).process_congr_left hX

/-- A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$ if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independent from $Y$. -/
/-
**ProbabilityTheory.Kernel.IndepFun.process_indepFun** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {m
α : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : MeasureTheory.M
easure α} {𝓧 : S → Type u_5} {𝓨 : Type u_6}   [inst : (i : S) → MeasurableSpace 
(𝓧 i)] [inst_1 : MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i} {Y : Ω → 𝓨},   (∀ (i
 : S), Measurable (X i)) →     Measurable Y →       (∀ (I : Finset S), Probabili
tyTheory.Kernel.IndepFun (fun ω i => X (↑i) ω) Y κ P) →         ∀ [ProbabilityTh
eory.IsZeroOrMarkovKernel κ], ProbabilityTheory.Kernel.IndepFun (fun ω i => X i 
ω) Y κ P
参数：i : S；𝓧 i；i : S；∀ (i : S), Measurable (X i)；∀ (I : Finset S), ProbabilityTheo
ry.Kernel.IndepFun (fun ω i => X (↑i) ω) Y κ P；fun ω i => X i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPiSystem.comap`：IsPiSystem.comap {α β} {S : Set (Set β)} (h_pi : IsPiS
ystem S) (f : α -> β) : IsPiSystem { s : Set α | exists t in S, f ⁻¹' t = s }
· 使用定理 `MeasureTheory.isPiSystem_squareCylinders`：isPiSystem_squareCylinders {C 
: forall i, Set (Set (α i))} (hC : forall i, IsPiSystem (C i)) (hC_univ : forall
 i, univ in C i) : IsPiSystem …
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.generateFrom_squareCylinders`：generateFrom_squareCylinders
 [forall i, MeasurableSpace (α i)] : MeasurableSpace.generateFrom (squareCylinde
rs fun i => {s : Set (α i) | Mea…
· 使用定理 `MeasurableSpace.comap_generateFrom`：comap_generateFrom {f : α -> β} {s :
 Set (Set β)} : (generateFrom s).comap f = generateFrom (preimage f '' s)
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {m1 m2 m : MeasurableSpace Ω}   {κ : ProbabilityTheo
ry.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `MeasurableSpace.generateFrom_measurableSet`：generateFrom_measurableSet [
MeasurableSpace α] : generateFrom {s : Set α | MeasurableSet s} = ‹_›
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_attach`：coe_attach (s : Finset α) : (s.attach : Set s) = Set.
univ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.measure_inter_preimage_eq_mul`：∀ {α : 
Type u_1} {Ω : Type u_2} {β : Type u_4} {β' : Type u_5} {mα : MeasurableSpace α}
 {mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Ke…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$
 if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independen
t from $Y$.
-/
lemma IndepFun.process_indepFun {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (hX : ∀ i, Measurable (X i)) (hY : Measurable Y)
    (h : ∀ (I : Finset S),
      IndepFun (fun ω (i : I) ↦ X i ω) Y κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i ↦ X i ω) Y κ P := by
  -- The π-system obtained by pulling back the π-system of square cylinders by `X`.
  let πX := {s : Set Ω | ∃ t ∈ squareCylinders (fun i ↦ {s : Set (𝓧 i) | MeasurableSet s}),
      (fun ω i ↦ X i ω) ⁻¹' t = s}
  have πX_pi : IsPiSystem πX :=
    IsPiSystem.comap (isPiSystem_squareCylinders (fun _ ↦ isPiSystem_measurableSet) (by simp)) _
  have πX_gen : (MeasurableSpace.pi.comap fun ω i ↦ X i ω) = generateFrom πX := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    rfl
  -- To prove independence, we prove independence of the generating π-system with the `σ`-algebra.
  refine IndepSets.indep (measurable_pi_iff.2 hX).comap_le hY.comap_le
    πX_pi (@isPiSystem_measurableSet Ω (.comap Y inferInstance)) πX_gen
    (@generateFrom_measurableSet Ω (.comap Y inferInstance)).symm ?_
  rintro - - ⟨-, ⟨I, s, hs, rfl⟩, rfl⟩ ⟨t, ht, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, forall_const] at hs
  have : (fun ω i ↦ X i ω) ⁻¹' .pi I s =
      (fun ω (i : I) ↦ X i ω) ⁻¹' .pi (SetLike.coe Finset.univ) (fun i ↦ s i)
       := by
    ext; simp
  have h1 : MeasurableSet <| .pi (SetLike.coe Finset.univ) (fun (i : I) ↦ s i) :=
    .pi (Finset.countable_toSet _) (fun _ _ ↦ hs _)
  filter_upwards [(h I).measure_inter_preimage_eq_mul _ _ h1 ht] with ω hω
  rw [this, hω]

/-- A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$ if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independent from $Y$.

This version only requires a.e.-measurability. -/
/-
**ProbabilityTheory.Kernel.IndepFun.process_indepFun** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {m
α : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : MeasureTheory.M
easure α} {𝓧 : S → Type u_5} {𝓨 : Type u_6}   [inst : (i : S) → MeasurableSpace 
(𝓧 i)] [inst_1 : MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i} {Y : Ω → 𝓨},   (∀ (i
 : S), Measurable (X i)) →     Measurable Y →       (∀ (I : Finset S), Probabili
tyTheory.Kernel.IndepFun (fun ω i => X (↑i) ω) Y κ P) →         ∀ [ProbabilityTh
eory.IsZeroOrMarkovKernel κ], ProbabilityTheory.Kernel.IndepFun (fun ω i => X i 
ω) Y κ P
参数：i : S；𝓧 i；i : S；∀ (i : S), Measurable (X i)；∀ (I : Finset S), ProbabilityTheo
ry.Kernel.IndepFun (fun ω i => X (↑i) ω) Y κ P；fun ω i => X i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPiSystem.comap`：IsPiSystem.comap {α β} {S : Set (Set β)} (h_pi : IsPiS
ystem S) (f : α -> β) : IsPiSystem { s : Set α | exists t in S, f ⁻¹' t = s }
· 使用定理 `MeasureTheory.isPiSystem_squareCylinders`：isPiSystem_squareCylinders {C 
: forall i, Set (Set (α i))} (hC : forall i, IsPiSystem (C i)) (hC_univ : forall
 i, univ in C i) : IsPiSystem …
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.generateFrom_squareCylinders`：generateFrom_squareCylinders
 [forall i, MeasurableSpace (α i)] : MeasurableSpace.generateFrom (squareCylinde
rs fun i => {s : Set (α i) | Mea…
· 使用定理 `MeasurableSpace.comap_generateFrom`：comap_generateFrom {f : α -> β} {s :
 Set (Set β)} : (generateFrom s).comap f = generateFrom (preimage f '' s)
· 使用定理 `ProbabilityTheory.Kernel.IndepSets.indep`：∀ {α : Type u_1} {Ω : Type u_2
} {_mα : MeasurableSpace α} {m1 m2 m : MeasurableSpace Ω}   {κ : ProbabilityTheo
ry.Kernel α Ω} {μ : MeasureThe…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `MeasurableSpace.generateFrom_measurableSet`：generateFrom_measurableSet [
MeasurableSpace α] : generateFrom {s : Set α | MeasurableSet s} = ‹_›
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_attach`：coe_attach (s : Finset α) : (s.attach : Set s) = Set.
univ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.measure_inter_preimage_eq_mul`：∀ {α : 
Type u_1} {Ω : Type u_2} {β : Type u_4} {β' : Type u_5} {mα : MeasurableSpace α}
 {mΩ : MeasurableSpace Ω}   {κ : ProbabilityTheory.Ke…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$
 if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independen
t from $Y$.

This version only requires a.e.-measurability.
-/
lemma IndepFun.process_indepFun₀ {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (hX : ∀ i, AEMeasurable (X i) (κ ∘ₘ P)) (hY : AEMeasurable Y (κ ∘ₘ P))
    (h : ∀ (I : Finset S), IndepFun (fun ω (i : I) ↦ X i ω) Y κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i ↦ X i ω) Y κ P := by
  refine .congr' ?_ (ae_of_all _ fun _ ↦ .rfl) (Measure.ae_ae_of_ae_comp hY.ae_eq_mk.symm)
  apply process_congr_left (X := fun i ↦ (hX i).mk (X i))
  · refine IndepFun.process_indepFun (fun i ↦ (hX i).measurable_mk) hY.measurable_mk
      fun I ↦ process_congr_left (X := fun (i : I) ↦ X i) ?_ (fun i ↦ ?_)
    · exact (h I).congr' (ae_of_all _ fun _ ↦ .rfl) (Measure.ae_ae_of_ae_comp hY.ae_eq_mk)
    · exact Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk
  exact fun i ↦ Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk.symm

/-- A random variable $X$ is independent from a stochastic process $(Y_s)_{s \in S}$  if
for all $s_1, ..., s_p \in S$ the variable $Y$ is independent from the family
$(X_{s_1}, ..., X_{s_p})$. -/
/-
**ProbabilityTheory.Kernel.IndepFun.indepFun_process** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {m
α : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : MeasureTheory.M
easure α} {𝓧 : Type u_5} {𝓨 : S → Type u_6}   [inst : MeasurableSpace 𝓧] [inst_1
 : (i : S) → MeasurableSpace (𝓨 i)] {X : Ω → 𝓧} {Y : (i : S) → Ω → 𝓨 i},   Measu
rable X →     (∀ (i : S), Measurable (Y i)) →       (∀ (I : Finset S), Probabili
tyTheory.Kernel.IndepFun X (fun ω i => Y (↑i) ω) κ P) →         ∀ [ProbabilityTh
eory.IsZeroOrMarkovKernel κ], ProbabilityTheory.Kernel.IndepFun X (fun ω i => Y 
i ω) κ P
参数：i : S；𝓨 i；i : S；∀ (i : S), Measurable (Y i)；∀ (I : Finset S), ProbabilityTheo
ry.Kernel.IndepFun X (fun ω i => Y (↑i) ω) κ P；fun ω i => Y i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.symm`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
   {κ : ProbabilityTheory.Ke…
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_indepFun`：∀ {S : Type u_1} {Ω 
: Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}   {
κ : ProbabilityTheory.Kernel α Ω} {P : M…

--- 原说明 ---
A random variable $X$ is independent from a stochastic process $(Y_s)_{s \in S}$
  if
for all $s_1, ..., s_p \in S$ the variable $Y$ is independent from the family
$(X_{s_1}, ..., X_{s_p})$.
-/
lemma IndepFun.indepFun_process {𝓧 : Type*} {𝓨 : S → Type*}
    [MeasurableSpace 𝓧] [∀ i, MeasurableSpace (𝓨 i)] {X : Ω → 𝓧}
    {Y : (i : S) → Ω → 𝓨 i} (hX : Measurable X) (hY : ∀ i, Measurable (Y i))
    (h : ∀ (I : Finset S),
      IndepFun X (fun ω (i : I) ↦ Y i ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun X (fun ω i ↦ Y i ω) κ P :=
  (IndepFun.process_indepFun hY hX (fun I ↦ (h I).symm)).symm

/-- A random variable $X$ is independent from a stochastic process $(Y_s)_{s \in S}$  if
for all $s_1, ..., s_p \in S$ the variable $Y$ is independent from the family
$(X_{s_1}, ..., X_{s_p})$.

This version only requires a.e.-measurability. -/
/-
**ProbabilityTheory.Kernel.IndepFun.indepFun_process** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.Kernel.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {m
α : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : MeasureTheory.M
easure α} {𝓧 : Type u_5} {𝓨 : S → Type u_6}   [inst : MeasurableSpace 𝓧] [inst_1
 : (i : S) → MeasurableSpace (𝓨 i)] {X : Ω → 𝓧} {Y : (i : S) → Ω → 𝓨 i},   Measu
rable X →     (∀ (i : S), Measurable (Y i)) →       (∀ (I : Finset S), Probabili
tyTheory.Kernel.IndepFun X (fun ω i => Y (↑i) ω) κ P) →         ∀ [ProbabilityTh
eory.IsZeroOrMarkovKernel κ], ProbabilityTheory.Kernel.IndepFun X (fun ω i => Y 
i ω) κ P
参数：i : S；𝓨 i；i : S；∀ (i : S), Measurable (Y i)；∀ (I : Finset S), ProbabilityTheo
ry.Kernel.IndepFun X (fun ω i => Y (↑i) ω) κ P；fun ω i => Y i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.symm`：∀ {α : Type u_1} {Ω : Type u_2} 
{β : Type u_4} {β' : Type u_5} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
   {κ : ProbabilityTheory.Ke…
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_indepFun`：∀ {S : Type u_1} {Ω 
: Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}   {
κ : ProbabilityTheory.Kernel α Ω} {P : M…

--- 原说明 ---
A random variable $X$ is independent from a stochastic process $(Y_s)_{s \in S}$
  if
for all $s_1, ..., s_p \in S$ the variable $Y$ is independent from the family
$(X_{s_1}, ..., X_{s_p})$.

This version only requires a.e.-measurability.
-/
lemma IndepFun.indepFun_process₀ {𝓧 : Type*} {𝓨 : S → Type*}
    [MeasurableSpace 𝓧] [∀ i, MeasurableSpace (𝓨 i)] {X : Ω → 𝓧}
    {Y : (i : S) → Ω → 𝓨 i} (hX : AEMeasurable X (κ ∘ₘ P)) (hY : ∀ i, AEMeasurable (Y i) (κ ∘ₘ P))
    (h : ∀ (I : Finset S),
      IndepFun X (fun ω (i : I) ↦ Y i ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun X (fun ω i ↦ Y i ω) κ P :=
  (IndepFun.process_indepFun₀ hY hX (fun I ↦ (h I).symm)).symm

/-- Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent. -/
/-
**ProbabilityTheory.Kernel.IndepFun.process_indepFun_process** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.Kernel.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {m
α : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : MeasureTheory.M
easure α} {T : Type u_5} {𝓧 : S → Type u_6} {𝓨 : T → Type u_7}   [inst : (i : S)
 → MeasurableSpace (𝓧 i)] [inst_1 : (j : T) → MeasurableSpace (𝓨 j)] {X : (i : S
) → Ω → 𝓧 i}   {Y : (j : T) → Ω → 𝓨 j},   (∀ (i : S), Measurable (X i)) →     (∀
 (j : T), Measurable (Y j)) →       (∀ (I : Finset S) (J : Finset T),           
ProbabilityTheory.Kernel.IndepFun (fun ω i => X (↑i) ω) (fun ω j => Y (↑j) ω) κ 
P) →         ∀ [ProbabilityTheory.IsZeroOrMarkovKernel κ],           Probability
Theory.Kernel.IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) κ P
参数：i : S；𝓧 i；j : T；𝓨 j；i : S；j : T；∀ (i : S), Measurable (X i)；∀ (j : T), Measur
able (Y j)；∀ (I : Finset S) (J : Finset T),           ProbabilityTheory.Kernel.I
ndepFun (fun ω i => X (↑i) ω) (fun ω j => Y (↑j) ω) κ P；fun ω i => X i ω；fun ω j
 => Y j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_indepFun`：∀ {S : Type u_1} {Ω 
: Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}   {
κ : ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.indepFun_process`：∀ {S : Type u_1} {Ω 
: Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}   {
κ : ProbabilityTheory.Kernel α Ω} {P : M…

--- 原说明 ---
Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent
 if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent.
-/
lemma IndepFun.process_indepFun_process {T : Type*} {𝓧 : S → Type*} {𝓨 : T → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [∀ j, MeasurableSpace (𝓨 j)] {X : (i : S) → Ω → 𝓧 i}
    {Y : (j : T) → Ω → 𝓨 j} (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (h : ∀ (I : Finset S) (J : Finset T),
      IndepFun (fun ω (i : I) ↦ X i ω) (fun ω (j : J) ↦ Y j ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) κ P := by
  refine IndepFun.process_indepFun hX (measurable_pi_lambda _ hY) fun I ↦ ?_
  exact IndepFun.indepFun_process (measurable_pi_lambda _ fun _ ↦ hX _) hY fun J ↦ h I J

/-- Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent.

This version only requires a.e.-measurability. -/
/-
**ProbabilityTheory.Kernel.IndepFun.process_indepFun_process** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.Kernel.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {m
α : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : MeasureTheory.M
easure α} {T : Type u_5} {𝓧 : S → Type u_6} {𝓨 : T → Type u_7}   [inst : (i : S)
 → MeasurableSpace (𝓧 i)] [inst_1 : (j : T) → MeasurableSpace (𝓨 j)] {X : (i : S
) → Ω → 𝓧 i}   {Y : (j : T) → Ω → 𝓨 j},   (∀ (i : S), Measurable (X i)) →     (∀
 (j : T), Measurable (Y j)) →       (∀ (I : Finset S) (J : Finset T),           
ProbabilityTheory.Kernel.IndepFun (fun ω i => X (↑i) ω) (fun ω j => Y (↑j) ω) κ 
P) →         ∀ [ProbabilityTheory.IsZeroOrMarkovKernel κ],           Probability
Theory.Kernel.IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) κ P
参数：i : S；𝓧 i；j : T；𝓨 j；i : S；j : T；∀ (i : S), Measurable (X i)；∀ (j : T), Measur
able (Y j)；∀ (I : Finset S) (J : Finset T),           ProbabilityTheory.Kernel.I
ndepFun (fun ω i => X (↑i) ω) (fun ω j => Y (↑j) ω) κ P；fun ω i => X i ω；fun ω j
 => Y j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_indepFun`：∀ {S : Type u_1} {Ω 
: Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}   {
κ : ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.indepFun_process`：∀ {S : Type u_1} {Ω 
: Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}   {
κ : ProbabilityTheory.Kernel α Ω} {P : M…

--- 原说明 ---
Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent
 if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent.

This version only requires a.e.-measurability.
-/
lemma IndepFun.process_indepFun_process₀ {T : Type*} {𝓧 : S → Type*} {𝓨 : T → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [∀ j, MeasurableSpace (𝓨 j)] {X : (i : S) → Ω → 𝓧 i}
    {Y : (j : T) → Ω → 𝓨 j} (hX : ∀ i, AEMeasurable (X i) (κ ∘ₘ P))
    (hY : ∀ j, AEMeasurable (Y j) (κ ∘ₘ P))
    (h : ∀ (I : Finset S) (J : Finset T),
      IndepFun (fun ω (i : I) ↦ X i ω) (fun ω (j : J) ↦ Y j ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) κ P := by
  refine process_congr ?_ (fun i ↦ Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk.symm)
    (fun j ↦ Measure.ae_ae_of_ae_comp (hY j).ae_eq_mk.symm)
  refine process_indepFun_process
    (fun i ↦ (hX i).measurable_mk) (fun j ↦ (hY j).measurable_mk) fun I J ↦ ?_
  exact process_congr (h I J) (fun i ↦ Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk)
    (fun j ↦ Measure.ae_ae_of_ae_comp (hY j).ae_eq_mk)

/-- If stochastic processes `X : (i : S) → (j : T i) → Ω → 𝓧 i j` are independent and
for all `i j`, `X' i j` is almost everywhere equal to `X i j`,
then `X'` are also independent. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable. -/
/-
**ProbabilityTheory.Kernel.iIndepFun.process_congr** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {m
α : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : MeasureTheory.M
easure α} {T : S → Type u_5} {𝓧 : (i : S) → T i → Type u_6}   [inst : (i : S) → 
(j : T i) → MeasurableSpace (𝓧 i j)] {X X' : (i : S) → (j : T i) → Ω → 𝓧 i j},  
 ProbabilityTheory.Kernel.iIndepFun (fun i ω j => X i j ω) κ P →     (∀ (i : S) 
(j : T i), ∀ᵐ (a : α) ∂P, X i j =ᵐ[κ a] X' i j) →       ProbabilityTheory.Kernel
.iIndepFun (fun i ω j => X' i j ω) κ P
参数：i : S；i : S；j : T i；𝓧 i j；i : S；j : T i；fun i ω j => X i j ω；∀ (i : S) (j : T
 i), ∀ᵐ (a : α) ∂P, X i j =ᵐ[κ a] X' i j；fun i ω j => X' i j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `biInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι 
→ α} {p : ι → Prop},   (∀ (i : ι), p i → f i = g i) → ⨅ i, ⨅ (_ : p i), f i = ⨅ 
i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_ball_iff`：ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.C
ountable) {p : α -> forall i in S, Prop} : (forallᵐ x ∂μ, forall i (hi : i in S)
, p x i hi) ↔ f…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.ae_eq_set_biInter`：ae_eq_set_biInter {s : Set β} (hs : s.C
ountable) {t t' : β -> Set α} (h : forall b in s, t b =ᵐ[μ] t' b) : (⋂ b in s, t
 b : Set α) =ᵐ[μ] (⋂ …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.preimage`：∀ {α : Type u} {β : Type v} {l : Filter α}
 {f g : α → β}, f =ᶠ[l] g → ∀ (s : Set β), f ⁻¹' s =ᶠ[l] g ⁻¹' s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `MeasureTheory.MeasurableSet.eq_preimage_restrict_countable`：∀ {ι : Type 
u_2} {α : ι → Type u_1} [inst : (i : ι) → MeasurableSpace (α i)] {s : Set ((i : 
ι) → α i)},   MeasurableSet s → ∃ I t, I.Countab…

--- 原说明 ---
If stochastic processes `X : (i : S) → (j : T i) → Ω → 𝓧 i j` are independent an
d
for all `i j`, `X' i j` is almost everywhere equal to `X i j`,
then `X'` are also independent. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable.
-/
lemma iIndepFun.process_congr {T : S → Type*} {𝓧 : (i : S) → (j : T i) → Type*}
    [∀ i j, MeasurableSpace (𝓧 i j)] {X X' : (i : S) → (j : T i) → Ω → 𝓧 i j}
    (h1 : iIndepFun (fun i ω j ↦ X i j ω) κ P) (h2 : ∀ i j, ∀ᵐ a ∂P, X i j =ᵐ[κ a] X' i j) :
    iIndepFun (fun i ω j ↦ X' i j ω) κ P := by
  intro s f hf
  choose! g mg hg using hf
  have h3 : ⋂ i ∈ s, f i = ⋂ i ∈ s, (fun i ω j ↦ X' i j ω) i ⁻¹' g i := (biInf_congr hg).symm
  have h3' a : ∏ i ∈ s, κ a (f i) = ∏ i ∈ s, κ a ((fun i ω j ↦ X' i j ω) i ⁻¹' g i) := by
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [hg i hi]
  simp_rw [h3, h3']
  choose! I u hI hu using fun i hi ↦ (mg i hi).eq_preimage_restrict_countable
  have h4 (f : (i : S) → (j : T i) → Ω → 𝓧 i j) : ⋂ i ∈ s, (fun i ω j ↦ f i j ω) i ⁻¹' g i =
      ⋂ i ∈ s, (fun i ω j ↦ f i j ω) i ⁻¹' (I i).domRestrict ⁻¹' u i :=
      (biInf_congr (fun i hi ↦ by rw [hu i hi])).symm
  have h4' a (f : (i : S) → (j : T i) → Ω → 𝓧 i j) :
      ∏ i ∈ s, κ a ((fun i ω j ↦ f i j ω) i ⁻¹' g i) =
      ∏ i ∈ s, κ a ((fun i ω j ↦ f i j ω) i ⁻¹' (I i).domRestrict ⁻¹' u i) := by
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [hu i hi]
  have h5 := h1 s (fun i hi ↦ ⟨g i, mg i hi, rfl⟩)
  simp_rw [h4, h4'] at h5 ⊢
  have h6 i (f : (j : T i) → Ω → 𝓧 i j) : (fun ω j ↦ f j ω) ⁻¹' (I i).domRestrict ⁻¹' (u i) =
      (fun ω (j : I i) ↦ f j ω) ⁻¹' (u i) := rfl
  simp_rw [h6] at h5 ⊢
  have h :
      ∀ᵐ a ∂P, ∀ i ∈ s, (fun ω (j : I i) ↦ X i j ω) =ᵐ[κ a] (fun ω (j : I i) ↦ X' i j ω) := by
    refine (ae_ball_iff s.countable_toSet).2 fun i hi ↦ ?_
    have := (hI i hi).to_subtype
    filter_upwards [ae_all_iff.2 fun (j : I i) ↦ h2 i j] with
      a (ha : ∀ (j : I i), ∀ᵐ ω ∂κ a, X i j ω = X' i j ω)
    filter_upwards [ae_all_iff.2 ha] with ω hω using by simp [hω]
  filter_upwards [h5, h] with a ha1 ha2
  refine .trans (measure_congr (ae_eq_set_biInter s.countable_toSet
    (fun i hi ↦ ((ha2 i hi).preimage _).symm))) (ha1.trans ?_)
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [measure_congr ((ha2 i hi).preimage _)]

/-- Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}$ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent. -/
/-
**ProbabilityTheory.Kernel.iIndepFun.iIndepFun_process** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {m
α : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : MeasureTheory.M
easure α} {T : S → Type u_5} {𝓧 : (i : S) → T i → Type u_6}   [inst : (i : S) → 
(j : T i) → MeasurableSpace (𝓧 i j)] {X : (i : S) → (j : T i) → Ω → 𝓧 i j},   (∀
 (i : S) (j : T i), Measurable (X i j)) →     (∀ (I : Finset S) (J : (i : ↥I) → 
Finset (T ↑i)),         ProbabilityTheory.Kernel.iIndepFun (fun i ω j => X (↑i) 
(↑j) ω) κ P) →       ProbabilityTheory.Kernel.iIndepFun (fun i ω j => X i j ω) κ
 P
参数：i : S；i : S；j : T i；𝓧 i j；i : S；j : T i；∀ (i : S) (j : T i), Measurable (X i 
j)；∀ (I : Finset S) (J : (i : ↥I) → Finset (T ↑i)),         ProbabilityTheory.Ke
rnel.iIndepFun (fun i ω j => X (↑i) (↑j) ω) κ P；fun i ω j => X i j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.exists_ae_eq_isMarkovKernel`：exists_ae_eq_isMar
kovKernel {μ : Measure α} (h : forallᵐ a ∂μ, IsProbabilityMeasure (κ a)) (h' : μ
 != 0) : exists (η : Kernel α β), (κ =ᵐ[μ]…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.ae_isProbabilityMeasure`：∀ {α : Type 
u_1} {Ω : Type u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → Measurable
Space (β i)}   {_mα : MeasurableSpace α} {_mΩ : …
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.congr`：∀ {α : Type u_1} {Ω : Type u_2
} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ η : Pr
obabilityTheory.Kernel α Ω} {μ…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `IsPiSystem.comap`：IsPiSystem.comap {α β} {S : Set (Set β)} (h_pi : IsPiS
ystem S) (f : α -> β) : IsPiSystem { s : Set α | exists t in S, f ⁻¹' t = s }
· 使用定理 `MeasureTheory.isPiSystem_squareCylinders`：isPiSystem_squareCylinders {C 
: forall i, Set (Set (α i))} (hC : forall i, IsPiSystem (C i)) (hC_univ : forall
 i, univ in C i) : IsPiSystem …
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.generateFrom_squareCylinders`：generateFrom_squareCylinders
 [forall i, MeasurableSpace (α i)] : MeasurableSpace.generateFrom (squareCylinde
rs fun i => {s : Set (α i) | Mea…
· 使用定理 `MeasurableSpace.comap_generateFrom`：comap_generateFrom {f : α -> β} {s :
 Set (Set β)} : (generateFrom s).comap f = generateFrom (preimage f '' s)
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.iIndep`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.iInter₂_congr`：iInter₂_congr {s t : forall i, κ i -> Set α} (h : for
all i j, s i j = t i j) : ⋂ (i) (j), s i j = ⋂ (i) (j), t i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.coe_attach`：coe_attach (s : Finset α) : (s.attach : Set s) = Set.
univ
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent 
if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}$ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent.
-/
lemma iIndepFun.iIndepFun_process {T : S → Type*} {𝓧 : (i : S) → (j : T i) → Type*}
    [∀ i j, MeasurableSpace (𝓧 i j)] {X : (i : S) → (j : T i) → Ω → 𝓧 i j}
    (hX : ∀ i j, Measurable (X i j))
    (h : ∀ (I : Finset S) (J : (i : I) → Finset (T i)),
      iIndepFun (fun i ω (j : J i) ↦ X i j ω) κ P) :
    iIndepFun (fun i ω j ↦ X i j ω) κ P := by
  obtain rfl | hμ := eq_or_ne P 0
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[P] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel (h ∅ fun _ ↦ ∅).ae_isProbabilityMeasure hμ
  apply iIndepFun.congr (Filter.EventuallyEq.symm η_eq)
  let π i := {s : Set Ω | ∃ t ∈ squareCylinders (fun j ↦ {s : Set (𝓧 i j) | MeasurableSet s}),
    (fun ω j ↦ X i j ω) ⁻¹' t = s}
  have π_pi i : IsPiSystem (π i) :=
    (isPiSystem_squareCylinders (fun _ ↦ isPiSystem_measurableSet) (by simp)).comap _
  have π_gen i : (MeasurableSpace.pi.comap fun ω j ↦ X i j ω) = generateFrom (π i) := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    rfl
  refine iIndepSets.iIndep _ (fun i ↦ (measurable_pi_iff.2 (hX i)).comap_le) π π_pi π_gen
    fun I s hs ↦ ?_
  simp only [squareCylinders, Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, forall_const,
    ↓existsAndEq, and_true, π] at hs
  choose! J t ht hs using hs
  simp_rw [Set.iInter₂_congr (fun i hi ↦ (hs i hi).symm),
    I.prod_congr rfl (fun i hi ↦ congrArg _ (hs i hi).symm)]
  have : (⋂ i ∈ I, (fun ω j ↦ X i j ω) ⁻¹' .pi (J i) (t i)) =
      (⋂ i ∈ (.univ : Finset I), (fun ω (j : J i) ↦ X i j ω) ⁻¹'
        .pi (SetLike.coe Finset.univ) (fun j ↦ t i j)) := by
    ext; simp
  have h' (i : I) (hi : i ∈ Finset.univ) :
      MeasurableSet <| (SetLike.coe Finset.univ).pi fun (j : J i) ↦ t i j :=
    .pi (Finset.countable_toSet _) (fun _ _ ↦ ht _ i.2 _)
  filter_upwards [(h I (fun i ↦ J i)).measure_inter_preimage_eq_mul _ _ .univ h',
    η_eq] with ω hω hη
  rw [this, ← hη, hω, ← I.prod_coe_sort]
  congrm ∏ _, κ ω ?_
  ext; simp

/-- Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}$ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent.

This version only requires a.e.-measurability. -/
/-
**ProbabilityTheory.Kernel.iIndepFun.iIndepFun_process** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.Kernel.iIndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {m
α : MeasurableSpace α}   {κ : ProbabilityTheory.Kernel α Ω} {P : MeasureTheory.M
easure α} {T : S → Type u_5} {𝓧 : (i : S) → T i → Type u_6}   [inst : (i : S) → 
(j : T i) → MeasurableSpace (𝓧 i j)] {X : (i : S) → (j : T i) → Ω → 𝓧 i j},   (∀
 (i : S) (j : T i), Measurable (X i j)) →     (∀ (I : Finset S) (J : (i : ↥I) → 
Finset (T ↑i)),         ProbabilityTheory.Kernel.iIndepFun (fun i ω j => X (↑i) 
(↑j) ω) κ P) →       ProbabilityTheory.Kernel.iIndepFun (fun i ω j => X i j ω) κ
 P
参数：i : S；i : S；j : T i；𝓧 i j；i : S；j : T i；∀ (i : S) (j : T i), Measurable (X i 
j)；∀ (I : Finset S) (J : (i : ↥I) → Finset (T ↑i)),         ProbabilityTheory.Ke
rnel.iIndepFun (fun i ω j => X (↑i) (↑j) ω) κ P；fun i ω j => X i j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.Kernel.exists_ae_eq_isMarkovKernel`：exists_ae_eq_isMar
kovKernel {μ : Measure α} (h : forallᵐ a ∂μ, IsProbabilityMeasure (κ a)) (h' : μ
 != 0) : exists (η : Kernel α β), (κ =ᵐ[μ]…
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.ae_isProbabilityMeasure`：∀ {α : Type 
u_1} {Ω : Type u_2} {ι : Type u_3} {β : ι → Type u_8} {mβ : (i : ι) → Measurable
Space (β i)}   {_mα : MeasurableSpace α} {_mΩ : …
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.congr`：∀ {α : Type u_1} {Ω : Type u_2
} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ η : Pr
obabilityTheory.Kernel α Ω} {μ…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `IsPiSystem.comap`：IsPiSystem.comap {α β} {S : Set (Set β)} (h_pi : IsPiS
ystem S) (f : α -> β) : IsPiSystem { s : Set α | exists t in S, f ⁻¹' t = s }
· 使用定理 `MeasureTheory.isPiSystem_squareCylinders`：isPiSystem_squareCylinders {C 
: forall i, Set (Set (α i))} (hC : forall i, IsPiSystem (C i)) (hC_univ : forall
 i, univ in C i) : IsPiSystem …
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.generateFrom_squareCylinders`：generateFrom_squareCylinders
 [forall i, MeasurableSpace (α i)] : MeasurableSpace.generateFrom (squareCylinde
rs fun i => {s : Set (α i) | Mea…
· 使用定理 `MeasurableSpace.comap_generateFrom`：comap_generateFrom {f : α -> β} {s :
 Set (Set β)} : (generateFrom s).comap f = generateFrom (preimage f '' s)
· 使用定理 `ProbabilityTheory.Kernel.iIndepSets.iIndep`：∀ {α : Type u_1} {Ω : Type u
_2} {ι : Type u_3} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}   {κ : Pr
obabilityTheory.Kernel α Ω} {μ :…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.iInter₂_congr`：iInter₂_congr {s t : forall i, κ i -> Set α} (h : for
all i j, s i j = t i j) : ⋂ (i) (j), s i j = ⋂ (i) (j), t i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.coe_attach`：coe_attach (s : Finset α) : (s.attach : Set s) = Set.
univ
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent 
if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}$ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent.

This version only requires a.e.-measurability.
-/
lemma iIndepFun.iIndepFun_process₀ {T : S → Type*} {𝓧 : (i : S) → (j : T i) → Type*}
    [∀ i j, MeasurableSpace (𝓧 i j)] {X : (i : S) → (j : T i) → Ω → 𝓧 i j}
    (hX : ∀ i j, AEMeasurable (X i j) (κ ∘ₘ P))
    (h : ∀ (I : Finset S) (J : (i : I) → Finset (T i)),
      iIndepFun (fun i ω (j : J i) ↦ X i j ω) κ P) :
    iIndepFun (fun i ω j ↦ X i j ω) κ P := by
  refine process_congr ?_ (fun i j ↦ Measure.ae_ae_of_ae_comp (hX i j).ae_eq_mk.symm)
  refine iIndepFun_process (fun i j ↦ (hX i j).measurable_mk) fun I J ↦ ?_
  exact (h I J).process_congr (fun i j ↦ Measure.ae_ae_of_ae_comp (hX i j).ae_eq_mk)

end Kernel

variable {P : Measure Ω}

/-- If `X` is a process independent from `Y` and for all `i`, `X' i` is almost everywhere equal
to `X i`, then `X'` is also independent from `Y`. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable. -/
/-
**ProbabilityTheory.IndepFun.process_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {𝓧 : S → Type u_4} {𝓨 : Type u_5}   [inst : (i : S) → MeasurableSpa
ce (𝓧 i)] [inst_1 : MeasurableSpace 𝓨] {X X' : (i : S) → Ω → 𝓧 i} {Y : Ω → 𝓨},  
 ProbabilityTheory.IndepFun (fun ω i => X i ω) Y P →     (∀ (i : S), X i =ᵐ[P] X
' i) → ProbabilityTheory.IndepFun (fun ω i => X' i ω) Y P
参数：i : S；𝓧 i；i : S；fun ω i => X i ω；∀ (i : S), X i =ᵐ[P] X' i；fun ω i => X' i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_congr_left`：∀ {S : Type u_1} {
Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}  
 {κ : ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}

--- 原说明 ---
If `X` is a process independent from `Y` and for all `i`, `X' i` is almost every
where equal
to `X i`, then `X'` is also independent from `Y`. This implies that independence
 results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable.
-/
lemma IndepFun.process_congr_left {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X X' : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (h1 : (fun ω i ↦ X i ω) ⟂ᵢ[P] Y) (h2 : ∀ i, X i =ᵐ[P] X' i) :
    (fun ω i ↦ X' i ω) ⟂ᵢ[P] Y :=
  Kernel.IndepFun.process_congr_left h1 (by simpa)

/-- If `X` is a process independent from `Y` and for all `i`, `X' i` is almost everywhere equal
to `X i`, then `X'` is also independent from `Y`. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable. -/
/-
**ProbabilityTheory.IndepFun.process_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {𝓧 : S → Type u_4} {𝓨 : Type u_5}   [inst : (i : S) → MeasurableSpa
ce (𝓧 i)] [inst_1 : MeasurableSpace 𝓨] {X X' : (i : S) → Ω → 𝓧 i} {Y : Ω → 𝓨},  
 ProbabilityTheory.IndepFun Y (fun ω i => X i ω) P →     (∀ (i : S), X i =ᵐ[P] X
' i) → ProbabilityTheory.IndepFun Y (fun ω i => X' i ω) P
参数：i : S；𝓧 i；i : S；fun ω i => X i ω；∀ (i : S), X i =ᵐ[P] X' i；fun ω i => X' i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_congr_right`：∀ {S : Type u_1} 
{Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α} 
  {κ : ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}

--- 原说明 ---
If `X` is a process independent from `Y` and for all `i`, `X' i` is almost every
where equal
to `X i`, then `X'` is also independent from `Y`. This implies that independence
 results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable.
-/
lemma IndepFun.process_congr_right {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X X' : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (h1 : Y ⟂ᵢ[P] (fun ω i ↦ X i ω)) (h2 : ∀ i, X i =ᵐ[P] X' i) :
    Y ⟂ᵢ[P] (fun ω i ↦ X' i ω) :=
  Kernel.IndepFun.process_congr_right h1 (by simpa)

/-- If `X` and `Y` are two independent processes and for all `i`, `X' i` is almost everywhere equal
to `X i`, and for all `j`, `Y' j` is almost everywhere equal to `Y j`,
then `X'` is independent from `Y'`. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable. -/
/-
**ProbabilityTheory.IndepFun.process_congr** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IndepFun`。
形式化陈述：∀ {S : Type u_1} {T : Type u_2} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P
 : MeasureTheory.Measure Ω} {𝓧 : S → Type u_4}   {𝓨 : T → Type u_5} [inst : (i :
 S) → MeasurableSpace (𝓧 i)] [inst_1 : (j : T) → MeasurableSpace (𝓨 j)]   {X X' 
: (i : S) → Ω → 𝓧 i} {Y Y' : (j : T) → Ω → 𝓨 j},   ProbabilityTheory.IndepFun (f
un ω i => X i ω) (fun ω j => Y j ω) P →     (∀ (i : S), X i =ᵐ[P] X' i) →       
(∀ (j : T), Y j =ᵐ[P] Y' j) → ProbabilityTheory.IndepFun (fun ω i => X' i ω) (fu
n ω j => Y' j ω) P
参数：i : S；𝓧 i；j : T；𝓨 j；i : S；j : T；fun ω i => X i ω；fun ω j => Y j ω；∀ (i : S), 
X i =ᵐ[P] X' i；∀ (j : T), Y j =ᵐ[P] Y' j；fun ω i => X' i ω；fun ω j => Y' j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_congr`：∀ {S : Type u_1} {T : T
ype u_2} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : Measurable
Space α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}

--- 原说明 ---
If `X` and `Y` are two independent processes and for all `i`, `X' i` is almost e
verywhere equal
to `X i`, and for all `j`, `Y' j` is almost everywhere equal to `Y j`,
then `X'` is independent from `Y'`. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable.
-/
lemma IndepFun.process_congr {𝓧 : S → Type*} {𝓨 : T → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [∀ j, MeasurableSpace (𝓨 j)] {X X' : (i : S) → Ω → 𝓧 i}
    {Y Y' : (j : T) → Ω → (𝓨 j)} (hXY : (fun ω i ↦ X i ω) ⟂ᵢ[P] (fun ω j ↦ Y j ω))
    (hX : ∀ i, X i =ᵐ[P] X' i) (hY : ∀ j, Y j =ᵐ[P] Y' j) :
    (fun ω i ↦ X' i ω) ⟂ᵢ[P] (fun ω j ↦ Y' j ω) :=
  Kernel.IndepFun.process_congr hXY (by simpa) (by simpa)

/-- A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$ if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independent from $Y$. -/
/-
**ProbabilityTheory.IndepFun.process_indepFun** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {𝓧 : S → Type u_4} {𝓨 : Type u_5}   [inst : (i : S) → MeasurableSpa
ce (𝓧 i)] [inst_1 : MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i} {Y : Ω → 𝓨},   (∀
 (i : S), Measurable (X i)) →     Measurable Y →       (∀ (I : Finset S), Probab
ilityTheory.IndepFun (fun ω i => X (↑i) ω) Y P) →         ∀ [MeasureTheory.IsZer
oOrProbabilityMeasure P], ProbabilityTheory.IndepFun (fun ω i => X i ω) Y P
参数：i : S；𝓧 i；i : S；∀ (i : S), Measurable (X i)；∀ (I : Finset S), ProbabilityTheo
ry.IndepFun (fun ω i => X (↑i) ω) Y P；fun ω i => X i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_indepFun`：∀ {S : Type u_1} {Ω 
: Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}   {
κ : ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…

--- 原说明 ---
A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$
 if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independen
t from $Y$.
-/
lemma IndepFun.process_indepFun {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (hX : ∀ i, Measurable (X i)) (hY : Measurable Y)
    (h : ∀ (I : Finset S), (fun ω (i : I) ↦ X i ω) ⟂ᵢ[P] Y) [IsZeroOrProbabilityMeasure P] :
    IndepFun (fun ω i ↦ X i ω) Y P :=
  Kernel.IndepFun.process_indepFun hX hY h

/-- A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$ if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independent from $Y$.

This version only requires a.e.-measurability. -/
/-
**ProbabilityTheory.IndepFun.process_indepFun** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {𝓧 : S → Type u_4} {𝓨 : Type u_5}   [inst : (i : S) → MeasurableSpa
ce (𝓧 i)] [inst_1 : MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i} {Y : Ω → 𝓨},   (∀
 (i : S), Measurable (X i)) →     Measurable Y →       (∀ (I : Finset S), Probab
ilityTheory.IndepFun (fun ω i => X (↑i) ω) Y P) →         ∀ [MeasureTheory.IsZer
oOrProbabilityMeasure P], ProbabilityTheory.IndepFun (fun ω i => X i ω) Y P
参数：i : S；𝓧 i；i : S；∀ (i : S), Measurable (X i)；∀ (I : Finset S), ProbabilityTheo
ry.IndepFun (fun ω i => X (↑i) ω) Y P；fun ω i => X i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_indepFun`：∀ {S : Type u_1} {Ω 
: Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}   {
κ : ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…

--- 原说明 ---
A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$
 if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independen
t from $Y$.

This version only requires a.e.-measurability.
-/
lemma IndepFun.process_indepFun₀ {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (hX : ∀ i, AEMeasurable (X i) P) (hY : AEMeasurable Y P)
    (h : ∀ (I : Finset S), (fun ω (i : I) ↦ X i ω) ⟂ᵢ[P] Y) [IsZeroOrProbabilityMeasure P] :
    IndepFun (fun ω i ↦ X i ω) Y P :=
  Kernel.IndepFun.process_indepFun₀ (by simpa) (by simpa) h

/-- A random variable $X$ is independent from a stochastic process $(Y_s)_{s \in S}$  if
for all $s_1, ..., s_p \in S$ the variable $Y$ is independent from the family
$(X_{s_1}, ..., X_{s_p})$. -/
/-
**ProbabilityTheory.IndepFun.indepFun_process** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {𝓧 : Type u_4} {𝓨 : S → Type u_5}   [inst : MeasurableSpace 𝓧] [ins
t_1 : (i : S) → MeasurableSpace (𝓨 i)] {X : Ω → 𝓧} {Y : (i : S) → Ω → 𝓨 i},   Me
asurable X →     (∀ (i : S), Measurable (Y i)) →       (∀ (I : Finset S), Probab
ilityTheory.IndepFun X (fun ω i => Y (↑i) ω) P) →         ∀ [MeasureTheory.IsZer
oOrProbabilityMeasure P], ProbabilityTheory.IndepFun X (fun ω i => Y i ω) P
参数：i : S；𝓨 i；i : S；∀ (i : S), Measurable (Y i)；∀ (I : Finset S), ProbabilityTheo
ry.IndepFun X (fun ω i => Y (↑i) ω) P；fun ω i => Y i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.indepFun_process`：∀ {S : Type u_1} {Ω 
: Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}   {
κ : ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…

--- 原说明 ---
A random variable $X$ is independent from a stochastic process $(Y_s)_{s \in S}$
  if
for all $s_1, ..., s_p \in S$ the variable $Y$ is independent from the family
$(X_{s_1}, ..., X_{s_p})$.
-/
lemma IndepFun.indepFun_process {𝓧 : Type*} {𝓨 : S → Type*}
    [MeasurableSpace 𝓧] [∀ i, MeasurableSpace (𝓨 i)] {X : Ω → 𝓧}
    {Y : (i : S) → Ω → 𝓨 i} (hX : Measurable X) (hY : ∀ i, Measurable (Y i))
    (h : ∀ (I : Finset S), X ⟂ᵢ[P] (fun ω (i : I) ↦ Y i ω)) [IsZeroOrProbabilityMeasure P] :
    IndepFun X (fun ω i ↦ Y i ω) P :=
  Kernel.IndepFun.indepFun_process hX hY h

/-- A random variable $X$ is independent from a stochastic process $(Y_s)_{s \in S}$  if
for all $s_1, ..., s_p \in S$ the variable $Y$ is independent from the family
$(X_{s_1}, ..., X_{s_p})$.

This version only requires a.e.-measurability. -/
/-
**ProbabilityTheory.IndepFun.indepFun_process** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {𝓧 : Type u_4} {𝓨 : S → Type u_5}   [inst : MeasurableSpace 𝓧] [ins
t_1 : (i : S) → MeasurableSpace (𝓨 i)] {X : Ω → 𝓧} {Y : (i : S) → Ω → 𝓨 i},   Me
asurable X →     (∀ (i : S), Measurable (Y i)) →       (∀ (I : Finset S), Probab
ilityTheory.IndepFun X (fun ω i => Y (↑i) ω) P) →         ∀ [MeasureTheory.IsZer
oOrProbabilityMeasure P], ProbabilityTheory.IndepFun X (fun ω i => Y i ω) P
参数：i : S；𝓨 i；i : S；∀ (i : S), Measurable (Y i)；∀ (I : Finset S), ProbabilityTheo
ry.IndepFun X (fun ω i => Y (↑i) ω) P；fun ω i => Y i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.indepFun_process`：∀ {S : Type u_1} {Ω 
: Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}   {
κ : ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…

--- 原说明 ---
A random variable $X$ is independent from a stochastic process $(Y_s)_{s \in S}$
  if
for all $s_1, ..., s_p \in S$ the variable $Y$ is independent from the family
$(X_{s_1}, ..., X_{s_p})$.

This version only requires a.e.-measurability.
-/
lemma IndepFun.indepFun_process₀ {𝓧 : Type*} {𝓨 : S → Type*}
    [MeasurableSpace 𝓧] [∀ i, MeasurableSpace (𝓨 i)] {X : Ω → 𝓧}
    {Y : (i : S) → Ω → 𝓨 i} (hX : AEMeasurable X P) (hY : ∀ i, AEMeasurable (Y i) P)
    (h : ∀ (I : Finset S), X ⟂ᵢ[P] (fun ω (i : I) ↦ Y i ω)) [IsZeroOrProbabilityMeasure P] :
    IndepFun X (fun ω i ↦ Y i ω) P :=
  Kernel.IndepFun.indepFun_process₀ (by simpa) (by simpa) h

/-- Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent. -/
/-
**ProbabilityTheory.IndepFun.process_indepFun_process** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {T : Type u_4} {𝓧 : S → Type u_5}   {𝓨 : T → Type u_6} [inst : (i :
 S) → MeasurableSpace (𝓧 i)] [inst_1 : (j : T) → MeasurableSpace (𝓨 j)]   {X : (
i : S) → Ω → 𝓧 i} {Y : (j : T) → Ω → 𝓨 j},   (∀ (i : S), Measurable (X i)) →    
 (∀ (j : T), Measurable (Y j)) →       (∀ (I : Finset S) (J : Finset T), Probabi
lityTheory.IndepFun (fun ω i => X (↑i) ω) (fun ω j => Y (↑j) ω) P) →         ∀ [
MeasureTheory.IsZeroOrProbabilityMeasure P],           ProbabilityTheory.IndepFu
n (fun ω i => X i ω) (fun ω j => Y j ω) P
参数：i : S；𝓧 i；j : T；𝓨 j；i : S；j : T；∀ (i : S), Measurable (X i)；∀ (j : T), Measur
able (Y j)；∀ (I : Finset S) (J : Finset T), ProbabilityTheory.IndepFun (fun ω i 
=> X (↑i) ω) (fun ω j => Y (↑j) ω) P；fun ω i => X i ω；fun ω j => Y j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_indepFun_process`：∀ {S : Type 
u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpac
e α}   {κ : ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…

--- 原说明 ---
Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent
 if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent.
-/
lemma IndepFun.process_indepFun_process {T : Type*} {𝓧 : S → Type*} {𝓨 : T → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [∀ j, MeasurableSpace (𝓨 j)] {X : (i : S) → Ω → 𝓧 i}
    {Y : (j : T) → Ω → 𝓨 j} (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (h : ∀ (I : Finset S) (J : Finset T),
      (fun ω (i : I) ↦ X i ω) ⟂ᵢ[P] (fun ω (j : J) ↦ Y j ω)) [IsZeroOrProbabilityMeasure P] :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P :=
  Kernel.IndepFun.process_indepFun_process hX hY h

/-- Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent.

This version only requires a.e.-measurability. -/
/-
**ProbabilityTheory.IndepFun.process_indepFun_process** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {T : Type u_4} {𝓧 : S → Type u_5}   {𝓨 : T → Type u_6} [inst : (i :
 S) → MeasurableSpace (𝓧 i)] [inst_1 : (j : T) → MeasurableSpace (𝓨 j)]   {X : (
i : S) → Ω → 𝓧 i} {Y : (j : T) → Ω → 𝓨 j},   (∀ (i : S), Measurable (X i)) →    
 (∀ (j : T), Measurable (Y j)) →       (∀ (I : Finset S) (J : Finset T), Probabi
lityTheory.IndepFun (fun ω i => X (↑i) ω) (fun ω j => Y (↑j) ω) P) →         ∀ [
MeasureTheory.IsZeroOrProbabilityMeasure P],           ProbabilityTheory.IndepFu
n (fun ω i => X i ω) (fun ω j => Y j ω) P
参数：i : S；𝓧 i；j : T；𝓨 j；i : S；j : T；∀ (i : S), Measurable (X i)；∀ (j : T), Measur
able (Y j)；∀ (I : Finset S) (J : Finset T), ProbabilityTheory.IndepFun (fun ω i 
=> X (↑i) ω) (fun ω j => Y (↑j) ω) P；fun ω i => X i ω；fun ω j => Y j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IndepFun.process_indepFun_process`：∀ {S : Type 
u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpac
e α}   {κ : ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsZeroOrMarkovKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : Measure
Theory.Measure β}   [hμβ : MeasureTheory.IsZe…

--- 原说明 ---
Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent
 if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent.

This version only requires a.e.-measurability.
-/
lemma IndepFun.process_indepFun_process₀ {T : Type*} {𝓧 : S → Type*} {𝓨 : T → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [∀ j, MeasurableSpace (𝓨 j)] {X : (i : S) → Ω → 𝓧 i}
    {Y : (j : T) → Ω → 𝓨 j} (hX : ∀ i, AEMeasurable (X i) P) (hY : ∀ j, AEMeasurable (Y j) P)
    (h : ∀ (I : Finset S) (J : Finset T),
      (fun ω (i : I) ↦ X i ω) ⟂ᵢ[P] (fun ω (j : J) ↦ Y j ω)) [IsZeroOrProbabilityMeasure P] :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P :=
  Kernel.IndepFun.process_indepFun_process₀ (by simpa) (by simpa) h

/-- If stochastic processes `X : (i : S) → (j : T i) → Ω → 𝓧 i j` are independent and
for all `i j`, `X' i j` is almost everywhere equal to `X i j`,
then `X'` are also independent. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable. -/
/-
**ProbabilityTheory.iIndepFun.process_congr** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.iIndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {T : S → Type u_4}   {𝓧 : (i : S) → T i → Type u_5} [inst : (i : S)
 → (j : T i) → MeasurableSpace (𝓧 i j)]   {X X' : (i : S) → (j : T i) → Ω → 𝓧 i 
j},   ProbabilityTheory.iIndepFun (fun i ω j => X i j ω) P →     (∀ (i : S) (j :
 T i), X i j =ᵐ[P] X' i j) → ProbabilityTheory.iIndepFun (fun i ω j => X' i j ω)
 P
参数：i : S；i : S；j : T i；𝓧 i j；i : S；j : T i；fun i ω j => X i j ω；∀ (i : S) (j : T
 i), X i j =ᵐ[P] X' i j；fun i ω j => X' i j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.process_congr`：∀ {S : Type u_1} {Ω : 
Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}   {κ 
: ProbabilityTheory.Kernel α Ω} {P : M…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_dirac_eq`：ae_dirac_eq [MeasurableSingletonClass α] (a :
 α) : ae (dirac a) = pure a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}

--- 原说明 ---
If stochastic processes `X : (i : S) → (j : T i) → Ω → 𝓧 i j` are independent an
d
for all `i j`, `X' i j` is almost everywhere equal to `X i j`,
then `X'` are also independent. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only a.e.-measurable.
-/
lemma iIndepFun.process_congr {T : S → Type*} {𝓧 : (i : S) → (j : T i) → Type*}
    [∀ i j, MeasurableSpace (𝓧 i j)] {X X' : (i : S) → (j : T i) → Ω → 𝓧 i j}
    (h1 : iIndepFun (fun i ω j ↦ X i j ω) P) (h2 : ∀ i j, X i j =ᵐ[P] X' i j) :
    iIndepFun (fun i ω j ↦ X' i j ω) P :=
  Kernel.iIndepFun.process_congr h1 (by simpa)

/-- Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}$ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent. -/
/-
**ProbabilityTheory.iIndepFun.iIndepFun_process** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.iIndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {T : S → Type u_4}   {𝓧 : (i : S) → T i → Type u_5} [inst : (i : S)
 → (j : T i) → MeasurableSpace (𝓧 i j)]   {X : (i : S) → (j : T i) → Ω → 𝓧 i j},
   (∀ (i : S) (j : T i), Measurable (X i j)) →     (∀ (I : Finset S) (J : (i : ↥
I) → Finset (T ↑i)), ProbabilityTheory.iIndepFun (fun i ω j => X (↑i) (↑j) ω) P)
 →       ProbabilityTheory.iIndepFun (fun i ω j => X i j ω) P
参数：i : S；i : S；j : T i；𝓧 i j；i : S；j : T i；∀ (i : S) (j : T i), Measurable (X i 
j)；∀ (I : Finset S) (J : (i : ↥I) → Finset (T ↑i)), ProbabilityTheory.iIndepFun 
(fun i ω j => X (↑i) (↑j) ω) P；fun i ω j => X i j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.iIndepFun_process`：∀ {S : Type u_1} {
Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}  
 {κ : ProbabilityTheory.Kernel α Ω} {P : M…

--- 原说明 ---
Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent 
if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}$ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent.
-/
lemma iIndepFun.iIndepFun_process {T : S → Type*} {𝓧 : (i : S) → (j : T i) → Type*}
    [∀ i j, MeasurableSpace (𝓧 i j)] {X : (i : S) → (j : T i) → Ω → 𝓧 i j}
    (hX : ∀ i j, Measurable (X i j))
    (h : ∀ (I : Finset S) (J : (i : I) → Finset (T i)), iIndepFun (fun i ω (j : J i) ↦ X i j ω) P) :
    iIndepFun (fun i ω j ↦ X i j ω) P :=
  Kernel.iIndepFun.iIndepFun_process hX h

/-- Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}$ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent.

This version only requires a.e.-measurability. -/
/-
**ProbabilityTheory.iIndepFun.iIndepFun_process** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.iIndepFun`。
形式化陈述：∀ {S : Type u_1} {Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} {T : S → Type u_4}   {𝓧 : (i : S) → T i → Type u_5} [inst : (i : S)
 → (j : T i) → MeasurableSpace (𝓧 i j)]   {X : (i : S) → (j : T i) → Ω → 𝓧 i j},
   (∀ (i : S) (j : T i), Measurable (X i j)) →     (∀ (I : Finset S) (J : (i : ↥
I) → Finset (T ↑i)), ProbabilityTheory.iIndepFun (fun i ω j => X (↑i) (↑j) ω) P)
 →       ProbabilityTheory.iIndepFun (fun i ω j => X i j ω) P
参数：i : S；i : S；j : T i；𝓧 i j；i : S；j : T i；∀ (i : S) (j : T i), Measurable (X i 
j)；∀ (I : Finset S) (J : (i : ↥I) → Finset (T ↑i)), ProbabilityTheory.iIndepFun 
(fun i ω j => X (↑i) (↑j) ω) P；fun i ω j => X i j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.iIndepFun.iIndepFun_process`：∀ {S : Type u_1} {
Ω : Type u_3} {mΩ : MeasurableSpace Ω} {α : Type u_4} {mα : MeasurableSpace α}  
 {κ : ProbabilityTheory.Kernel α Ω} {P : M…

--- 原说明 ---
Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent 
if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}$ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent.

This version only requires a.e.-measurability.
-/
lemma iIndepFun.iIndepFun_process₀ {T : S → Type*} {𝓧 : (i : S) → (j : T i) → Type*}
    [∀ i j, MeasurableSpace (𝓧 i j)] {X : (i : S) → (j : T i) → Ω → 𝓧 i j}
    (hX : ∀ i j, AEMeasurable (X i j) P)
    (h : ∀ (I : Finset S) (J : (i : I) → Finset (T i)), iIndepFun (fun i ω (j : J i) ↦ X i j ω) P) :
    iIndepFun (fun i ω j ↦ X i j ω) P :=
  Kernel.iIndepFun.iIndepFun_process₀ (by simpa) h

end ProbabilityTheory

