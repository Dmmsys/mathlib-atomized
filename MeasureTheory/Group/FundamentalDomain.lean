/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Fundamental domain of a group action

A set `s` is said to be a *fundamental domain* of an action of a group `G` on a measurable space `α`
with respect to a measure `μ` if

* `s` is a measurable set;

* the sets `g • s` over all `g : G` cover almost all points of the whole space;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure-preserving action, any two
fundamental domains have the same measure, and for a `G`-invariant function, its integrals over any
two fundamental domains are equal to each other.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.

* We define the `HasFundamentalDomain` typeclass, in particular to be able to define the `covolume`
  of a quotient of `α` by a group `G`, which under reasonable conditions does not depend on the
  choice of fundamental domain.

* We define the `QuotientMeasureEqMeasurePreimage` typeclass to describe a situation in which a
  measure `μ` on `α ⧸ G` can be computed by taking a measure `ν` on `α` of the intersection of the
  pullback with a fundamental domain.

## Main declarations

* `MeasureTheory.IsFundamentalDomain`: Predicate for a set to be a fundamental domain of the
  action of a group
* `MeasureTheory.fundamentalFrontier`: Fundamental frontier of a set under the action of a group.
  Elements of `s` that belong to some other translate of `s`.
* `MeasureTheory.fundamentalInterior`: Fundamental interior of a set under the action of a group.
  Elements of `s` that do not belong to any other translate of `s`.
-/

@[expose] public section


open scoped ENNReal Pointwise Topology NNReal ENNReal MeasureTheory

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Filter

namespace MeasureTheory

/-- A measurable set `s` is a *fundamental domain* for an additive action of an additive group `G`
on a measurable space `α` with respect to a measure `μ` if the sets `g +ᵥ s`, `g : G`, are pairwise
a.e. disjoint and cover the whole space. -/
/-
**MeasureTheory.IsAddFundamentalDomain** 是 Mathlib 中的一个结构，位于命名空间 `MeasureTheory`
。
形式化陈述：IsAddFundamentalDomain (G : Type*) {α : Type*} [Zero G] [VAdd G α] [Measur
ableSpace α] (s : Set α) (μ : Measure α
参数：G : Type*；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measurable set `s` is a *fundamental domain* for an additive action of an addi
tive group `G`
on a measurable space `α` with respect to a measure `μ` if the sets `g +ᵥ s`, `g
 : G`, are pairwise
a.e. disjoint and cover the whole space.
-/
structure IsAddFundamentalDomain (G : Type*) {α : Type*} [Zero G] [VAdd G α] [MeasurableSpace α]
    (s : Set α) (μ : Measure α := by volume_tac) : Prop where
  protected nullMeasurableSet : NullMeasurableSet s μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ s
  protected aedisjoint : Pairwise <| (AEDisjoint μ on fun g : G => g +ᵥ s)

/-- A measurable set `s` is a *fundamental domain* for an action of a group `G` on a measurable
space `α` with respect to a measure `μ` if the sets `g • s`, `g : G`, are pairwise a.e. disjoint and
cover the whole space. -/
@[to_additive IsAddFundamentalDomain]
/-
**MeasureTheory.IsFundamentalDomain** 是 Mathlib 中的一个结构，位于命名空间 `MeasureTheory`。
形式化陈述：IsFundamentalDomain (G : Type*) {α : Type*} [One G] [SMul G α] [Measurable
Space α] (s : Set α) (μ : Measure α
参数：G : Type*；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measurable set `s` is a *fundamental domain* for an action of a group `G` on a
 measurable
space `α` with respect to a measure `μ` if the sets `g • s`, `g : G`, are pairwi
se a.e. disjoint and
cover the whole space.
-/
structure IsFundamentalDomain (G : Type*) {α : Type*} [One G] [SMul G α] [MeasurableSpace α]
    (s : Set α) (μ : Measure α := by volume_tac) : Prop where
  protected nullMeasurableSet : NullMeasurableSet s μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s
  protected aedisjoint : Pairwise <| (AEDisjoint μ on fun g : G => g • s)

variable {G H α β E : Type*}

namespace IsFundamentalDomain

variable [Group G] [Group H] [MulAction G α] [MeasurableSpace α] [MulAction H β] [MeasurableSpace β]
  [NormedAddCommGroup E] {s t : Set α} {μ : Measure α}

/-- If for each `x : α`, exactly one of `g • x`, `g : G`, belongs to a measurable set `s`, then `s`
is a fundamental domain for the action of `G` on `α`. -/
@[to_additive /-- If for each `x : α`, exactly one of `g +ᵥ x`, `g : G`, belongs to a measurable set
`s`, then `s` is a fundamental domain for the additive action of `G` on `α`. -/]
/-
**MeasureTheory.IsFundamentalDomain.mk'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.IsFundamentalDomain`。
形式化陈述：mk' (h_meas : NullMeasurableSet s μ) (h_exists : forall x : α, exists! g :
 G, g • x in s) : IsFundamentalDomain G s μ where nullMeasurableSet
参数：h_meas : NullMeasurableSet s μ；h_exists : forall x : α, exists! g : G, g • x 
in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
theorem mk' (h_meas : NullMeasurableSet s μ) (h_exists : ∀ x : α, ∃! g : G, g • x ∈ s) :
    IsFundamentalDomain G s μ where
  nullMeasurableSet := h_meas
  ae_covers := Eventually.of_forall fun x => (h_exists x).exists
  aedisjoint a b hab := Disjoint.aedisjoint <| disjoint_left.2 fun x hxa hxb => by
    rw [mem_smul_set_iff_inv_smul_mem] at hxa hxb
    exact hab (inv_injective <| (h_exists x).unique hxa hxb)

/-- For `s` to be a fundamental domain, it's enough to check
`MeasureTheory.AEDisjoint (g • s) s` for `g ≠ 1`. -/
@[to_additive /-- For `s` to be a fundamental domain, it's enough to check
  `MeasureTheory.AEDisjoint (g +ᵥ s) s` for `g ≠ 0`. -/]
/-
**MeasureTheory.IsFundamentalDomain.mk''** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IsFundamentalDomain`。
形式化陈述：mk'' (h_meas : NullMeasurableSet s μ) (h_ae_covers : forallᵐ x ∂μ, exists 
g : G, g • x in s) (h_ae_disjoint : forall g, g != (1 : G) -> AEDisjoint μ (g • 
s) s) (h_qmp : forall g : G, QuasiMeasurePreserving ((g • ·) : α -> α) μ μ) : Is
FundamentalDomain G s μ where nullMeasurableSet
参数：h_meas : NullMeasurableSet s μ；h_ae_covers : forallᵐ x ∂μ, exists g : G, g • 
x in s；h_ae_disjoint : forall g, g != (1 : G) -> AEDisjoint μ (g • s) s；h_qmp : 
forall g : G, QuasiMeasurePreserving ((g • ·) : α -> α) μ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.pairwise_aedisjoint_of_aedisjoint_forall_ne_one`：p
airwise_aedisjoint_of_aedisjoint_forall_ne_one {G α : Type*} [Group G] [MulActio
n G α] {_ : MeasurableSpace α} {μ : Measure α} {s : Set α} …
-/
theorem mk'' (h_meas : NullMeasurableSet s μ) (h_ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s)
    (h_ae_disjoint : ∀ g, g ≠ (1 : G) → AEDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving ((g • ·) : α → α) μ μ) :
    IsFundamentalDomain G s μ where
  nullMeasurableSet := h_meas
  ae_covers := h_ae_covers
  aedisjoint := pairwise_aedisjoint_of_aedisjoint_forall_ne_one h_ae_disjoint h_qmp

/-- If a measurable space has a finite measure `μ` and a countable group `G` acts
quasi-measure-preservingly, then to show that a set `s` is a fundamental domain, it is sufficient
to check that its translates `g • s` are (almost) disjoint and that the sum `∑' g, μ (g • s)` is
sufficiently large. -/
@[to_additive
  /-- If a measurable space has a finite measure `μ` and a countable additive group `G` acts
  quasi-measure-preservingly, then to show that a set `s` is a fundamental domain, it is sufficient
  to check that its translates `g +ᵥ s` are (almost) disjoint and that the sum `∑' g, μ (g +ᵥ s)` is
  sufficiently large. -/]
/-
**MeasureTheory.IsFundamentalDomain.mk_of_measure_univ_le** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：mk_of_measure_univ_le [IsFiniteMeasure μ] [Countable G] (h_meas : NullMeas
urableSet s μ) (h_ae_disjoint : forall g != (1 : G), AEDisjoint μ (g • s) s) (h_
qmp : forall g : G, QuasiMeasurePreserving (g • · : α -> α) μ μ) (h_measure_univ
_le : μ (univ : Set α) <= ∑' g : G, μ (g • s)) : IsFundamentalDomain G s μ
参数：h_meas : NullMeasurableSet s μ；h_ae_disjoint : forall g != (1 : G), AEDisjoin
t μ (g • s) s；h_qmp : forall g : G, QuasiMeasurePreserving (g • · : α -> α) μ μ；
h_measure_univ_le : μ (univ : Set α) <= ∑' g : G, μ (g • s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.pairwise_aedisjoint_of_aedisjoint_forall_ne_one`：p
airwise_aedisjoint_of_aedisjoint_forall_ne_one {G α : Type*} [Group G] [MulActio
n G α] {_ : MeasurableSpace α} {μ : Measure α} {s : Set α} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `Set.iUnion_smul_eq_ofPred_exists`：iUnion_smul_eq_ofPred_exists {s : Set 
β} : ⋃ g : α, g • s = { a | exists g : α, g • a in s }
· 使用定理 `MeasureTheory.NullMeasurableSet.iUnion`：∀ {α : Type u_2} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} {ι : Sort u_5} [Countable ι] {s : ι → Se
t α},   (∀ (i : ι), MeasureT…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_iff_measure_eq`：ae_iff_measure_eq [IsFiniteMeasure μ] {
p : α -> Prop} (hp : NullMeasurableSet { a | p a } μ) : (forallᵐ a ∂μ, p a) ↔ μ 
{ a | p a } = μ univ
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasureTheory.measure_iUnion₀`：measure_iUnion₀ [Countable ι] {f : ι -> S
et α} (hd : Pairwise (AEDisjoint μ on f)) (h : forall i, NullMeasurableSet (f i)
 μ) : μ (⋃ i, f i) …
-/
theorem mk_of_measure_univ_le [IsFiniteMeasure μ] [Countable G] (h_meas : NullMeasurableSet s μ)
    (h_ae_disjoint : ∀ g ≠ (1 : G), AEDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving (g • · : α → α) μ μ)
    (h_measure_univ_le : μ (univ : Set α) ≤ ∑' g : G, μ (g • s)) : IsFundamentalDomain G s μ :=
  have aedisjoint : Pairwise (AEDisjoint μ on fun g : G => g • s) :=
    pairwise_aedisjoint_of_aedisjoint_forall_ne_one h_ae_disjoint h_qmp
  { nullMeasurableSet := h_meas
    aedisjoint
    ae_covers := by
      replace h_meas : ∀ g : G, NullMeasurableSet (g • s) μ := fun g => by
        rw [← inv_inv g, ← preimage_smul]; exact h_meas.preimage (h_qmp g⁻¹)
      have h_meas' : NullMeasurableSet {a | ∃ g : G, g • a ∈ s} μ := by
        rw [← iUnion_smul_eq_ofPred_exists]; exact .iUnion h_meas
      rw [ae_iff_measure_eq h_meas', ← iUnion_smul_eq_ofPred_exists]
      refine le_antisymm (measure_mono <| subset_univ _) ?_
      rw [measure_iUnion₀ aedisjoint h_meas]
      exact h_measure_univ_le }

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.iUnion_smul_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.IsFundamentalDomain`。
形式化陈述：iUnion_smul_ae_eq (h : IsFundamentalDomain G s μ) : ⋃ g : G, g • s =ᵐ[μ] u
niv
参数：h : IsFundamentalDomain G s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.eventuallyEq_univ`：eventuallyEq_univ {s : Set α} {l : Filter α} :
 s =ᶠ[l] univ ↔ s in l
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.IsFundamentalDomain.ae_covers`：∀ {G : Type u_1} {α : Type 
u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s : Set α}
   {μ : autoParam (MeasureTheory.…
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
theorem iUnion_smul_ae_eq (h : IsFundamentalDomain G s μ) : ⋃ g : G, g • s =ᵐ[μ] univ :=
  eventuallyEq_univ.2 <| h.ae_covers.mono fun _ ⟨g, hg⟩ =>
    mem_iUnion.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.measure_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.IsFundamentalDomain`。
形式化陈述：measure_ne_zero [Countable G] [SMulInvariantMeasure G α μ] (hμ : μ != 0) (
h : IsFundamentalDomain G s μ) : μ s != 0
参数：hμ : μ != 0；h : IsFundamentalDomain G s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_pos`：measure_univ_pos : 0 < μ univ ↔ 
μ != 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IsFundamentalDomain.iUnion_smul_ae_eq`：iUnion_smul_ae_eq (
h : IsFundamentalDomain G s μ) : ⋃ g : G, g • s =ᵐ[μ] univ
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_smul`：measure_smul (c : G) (s : Set α) : μ (c • s)
 = μ s
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem measure_ne_zero [Countable G] [SMulInvariantMeasure G α μ]
    (hμ : μ ≠ 0) (h : IsFundamentalDomain G s μ) : μ s ≠ 0 := by
  have hc := measure_univ_pos.mpr hμ
  contrapose! hc
  rw [← measure_congr h.iUnion_smul_ae_eq]
  refine le_trans (measure_iUnion_le _) ?_
  simp_rw [measure_smul, hc, tsum_zero, le_refl]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IsFundamentalDomain`。
形式化陈述：mono (h : IsFundamentalDomain G s μ) {ν : Measure α} (hle : ν ≪ μ) : IsFun
damentalDomain G s ν
参数：h : IsFundamentalDomain G s μ；hle : ν ≪ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.mono_ac`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.NullMeas
urableSet s μ → ν.AbsolutelyC…
· 使用定理 `MeasureTheory.IsFundamentalDomain.nullMeasurableSet`：∀ {G : Type u_1} {α
 : Type u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s 
: Set α}   {μ : autoParam (MeasureTheory.…
· 使用定理 `MeasureTheory.IsFundamentalDomain.ae_covers`：∀ {G : Type u_1} {α : Type 
u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s : Set α}
   {μ : autoParam (MeasureTheory.…
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `MeasureTheory.IsFundamentalDomain.aedisjoint`：∀ {G : Type u_1} {α : Type
 u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s : Set α
}   {μ : autoParam (MeasureTheory.…
-/
theorem mono (h : IsFundamentalDomain G s μ) {ν : Measure α} (hle : ν ≪ μ) :
    IsFundamentalDomain G s ν :=
  ⟨h.1.mono_ac hle, hle h.2, h.aedisjoint.mono fun _ _ h => hle h⟩

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.preimage_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.IsFundamentalDomain`。
形式化陈述：preimage_of_equiv {ν : Measure β} (h : IsFundamentalDomain G s μ) {f : β -
> α} (hf : QuasiMeasurePreserving f ν μ) {e : G -> H} (he : Bijective e) (hef : 
forall g, Semiconj f (e g • ·) (g • ·)) : IsFundamentalDomain H (f ⁻¹' s) ν wher
e nullMeasurableSet
参数：h : IsFundamentalDomain G s μ；hf : QuasiMeasurePreserving f ν μ；he : Bijectiv
e e；hef : forall g, Semiconj f (e g • ·) (g • ·)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.IsFundamentalDomain.nullMeasurableSet`：∀ {G : Type u_1} {α
 : Type u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s 
: Set α}   {μ : autoParam (MeasureTheory.…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.ae`：ae (h : QuasiMeasurePre
serving f μa μb) {p : β -> Prop} (hg : forallᵐ x ∂μb, p x) : forallᵐ x ∂μa, p (f
 x)
· 使用定理 `MeasureTheory.IsFundamentalDomain.ae_covers`：∀ {G : Type u_1} {α : Type 
u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s : Set α}
   {μ : autoParam (MeasureTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Equiv.instCanLiftForallCoeBijective`：∀ {α : Sort u_1} {β : Sort u_4}, Ca
nLift (α → β) (α ≃ β) DFunLike.coe Function.Bijective
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.AEDisjoint.preimage`：∀ {α : Type u_1} {β : Type u_2} {mα :
 MeasurableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α}   {ν 
: MeasureTheory.Measure…
· 使用定理 `MeasureTheory.IsFundamentalDomain.aedisjoint`：∀ {G : Type u_1} {α : Type
 u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s : Set α
}   {μ : autoParam (MeasureTheory.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem preimage_of_equiv {ν : Measure β} (h : IsFundamentalDomain G s μ) {f : β → α}
    (hf : QuasiMeasurePreserving f ν μ) {e : G → H} (he : Bijective e)
    (hef : ∀ g, Semiconj f (e g • ·) (g • ·)) : IsFundamentalDomain H (f ⁻¹' s) ν where
  nullMeasurableSet := h.nullMeasurableSet.preimage hf
  ae_covers := (hf.ae h.ae_covers).mono fun x ⟨g, hg⟩ => ⟨e g, by rwa [mem_preimage, hef g x]⟩
  aedisjoint a b hab := by
    lift e to G ≃ H using he
    have : (e.symm a⁻¹)⁻¹ ≠ (e.symm b⁻¹)⁻¹ := by simp [hab]
    have := (h.aedisjoint this).preimage hf
    simp only [Semiconj] at hef
    simpa only [onFun, ← preimage_smul_inv, preimage_preimage, ← hef, e.apply_symm_apply, inv_inv]
      using this

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.image_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.IsFundamentalDomain`。
形式化陈述：image_of_equiv {ν : Measure β} (h : IsFundamentalDomain G s μ) (f : α ≃ β)
 (hf : QuasiMeasurePreserving f.symm ν μ) (e : H ≃ G) (hef : forall g, Semiconj 
f (e g • ·) (g • ·)) : IsFundamentalDomain H (f '' s) ν
参数：h : IsFundamentalDomain G s μ；f : α ≃ β；hf : QuasiMeasurePreserving f.symm ν 
μ；e : H ≃ G；hef : forall g, Semiconj f (e g • ·) (g • ·)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `MeasureTheory.IsFundamentalDomain.preimage_of_equiv`：preimage_of_equiv {
ν : Measure β} (h : IsFundamentalDomain G s μ) {f : β -> α} (hf : QuasiMeasurePr
eserving f ν μ) {e : G -> H} (he : Biject…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem image_of_equiv {ν : Measure β} (h : IsFundamentalDomain G s μ) (f : α ≃ β)
    (hf : QuasiMeasurePreserving f.symm ν μ) (e : H ≃ G)
    (hef : ∀ g, Semiconj f (e g • ·) (g • ·)) : IsFundamentalDomain H (f '' s) ν := by
  rw [f.image_eq_preimage_symm]
  refine h.preimage_of_equiv hf e.symm.bijective fun g x => ?_
  rcases f.surjective x with ⟨x, rfl⟩
  rw [← hef _ _, f.symm_apply_apply, f.symm_apply_apply, e.apply_symm_apply]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.pairwise_aedisjoint_of_ac** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：pairwise_aedisjoint_of_ac {ν} (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ)
 : Pairwise fun g₁ g₂ : G => AEDisjoint ν (g₁ • s) (g₂ • s)
参数：h : IsFundamentalDomain G s μ；hν : ν ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `MeasureTheory.IsFundamentalDomain.aedisjoint`：∀ {G : Type u_1} {α : Type
 u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s : Set α
}   {μ : autoParam (MeasureTheory.…
-/
theorem pairwise_aedisjoint_of_ac {ν} (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) :
    Pairwise fun g₁ g₂ : G => AEDisjoint ν (g₁ • s) (g₂ • s) :=
  h.aedisjoint.mono fun _ _ H => hν H

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.smul_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IsFundamentalDomain`。
形式化陈述：smul_of_comm {G' : Type*} [Group G'] [MulAction G' α] [MeasurableConstSMul
 G' α] [SMulInvariantMeasure G' α μ] [SMulCommClass G' G α] (h : IsFundamentalDo
main G s μ) (g : G') : IsFundamentalDomain G (g • s) μ
参数：h : IsFundamentalDomain G s μ；g : G'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.image_of_equiv`：image_of_equiv {ν : Me
asure β} (h : IsFundamentalDomain G s μ) (f : α ≃ β) (hf : QuasiMeasurePreservin
g f.symm ν μ) (e : H ≃ G) (hef : foral…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
theorem smul_of_comm {G' : Type*} [Group G'] [MulAction G' α]
    [MeasurableConstSMul G' α] [SMulInvariantMeasure G' α μ] [SMulCommClass G' G α]
    (h : IsFundamentalDomain G s μ) (g : G') : IsFundamentalDomain G (g • s) μ :=
  h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
    (Equiv.refl _) <| smul_comm g

variable [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.nullMeasurableSet_smul** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：nullMeasurableSet_smul (h : IsFundamentalDomain G s μ) (g : G) : NullMeasu
rableSet (g • s) μ
参数：h : IsFundamentalDomain G s μ；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.smul`：∀ {G : Type u} {α : Type w} {m : M
easurableSpace α} [inst : Group G] [inst_1 : MulAction G α]   {μ : MeasureTheory
.Measure α} [MeasureTheory…
· 使用定理 `MeasureTheory.IsFundamentalDomain.nullMeasurableSet`：∀ {G : Type u_1} {α
 : Type u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s 
: Set α}   {μ : autoParam (MeasureTheory.…
-/
theorem nullMeasurableSet_smul (h : IsFundamentalDomain G s μ) (g : G) :
    NullMeasurableSet (g • s) μ :=
  h.nullMeasurableSet.smul g

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.restrict_restrict** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.IsFundamentalDomain`。
形式化陈述：restrict_restrict (h : IsFundamentalDomain G s μ) (g : G) (t : Set α) : (μ
.restrict t).restrict (g • s) = μ.restrict (g • s inter t)
参数：h : IsFundamentalDomain G s μ；g : G；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_restrict₀`：restrict_restrict₀ (hs : NullM
easurableSet s (μ.restrict t)) : (μ.restrict t).restrict s = μ.restrict (s inter
 t)
· 使用定理 `MeasureTheory.NullMeasurableSet.mono`：∀ {α : Type u_1} {mα : MeasurableS
pace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.NullMeasura
bleSet s μ → ν ≤ μ → Measu…
· 使用定理 `MeasureTheory.IsFundamentalDomain.nullMeasurableSet_smul`：nullMeasurable
Set_smul (h : IsFundamentalDomain G s μ) (g : G) : NullMeasurableSet (g • s) μ
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
theorem restrict_restrict (h : IsFundamentalDomain G s μ) (g : G) (t : Set α) :
    (μ.restrict t).restrict (g • s) = μ.restrict (g • s ∩ t) :=
  restrict_restrict₀ ((h.nullMeasurableSet_smul g).mono restrict_le_self)

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IsFundamentalDomain`。
形式化陈述：smul (h : IsFundamentalDomain G s μ) (g : G) : IsFundamentalDomain G (g • 
s) μ
参数：h : IsFundamentalDomain G s μ；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.image_of_equiv`：image_of_equiv {ν : Me
asure β} (h : IsFundamentalDomain G s μ) (f : α ≃ β) (hf : QuasiMeasurePreservin
g f.symm ν μ) (e : H ≃ G) (hef : foral…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `MulAction.toPerm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α]
 [inst_1 : MulAction α β] (a : α) (x : β),   (MulAction.toPerm a) x = a • x
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
theorem smul (h : IsFundamentalDomain G s μ) (g : G) : IsFundamentalDomain G (g • s) μ :=
  h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
    ⟨fun g' => g⁻¹ * g' * g, fun g' => g * g' * g⁻¹, fun g' => by simp [mul_assoc], fun g' => by
      simp [mul_assoc]⟩
    fun g' x => by simp [smul_smul, mul_assoc]

variable [Countable G] {ν : Measure α}

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.sum_restrict_of_ac** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：sum_restrict_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) : (sum fun
 g : G => ν.restrict (g • s)) = ν
参数：h : IsFundamentalDomain G s μ；hν : ν ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_ae`：restrict_iUnion_ae [Countable 
ι] {s : ι -> Set α} (hd : Pairwise (AEDisjoint μ on s)) (hm : forall i, NullMeas
urableSet (s i) μ) : μ.restric…
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `MeasureTheory.IsFundamentalDomain.aedisjoint`：∀ {G : Type u_1} {α : Type
 u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s : Set α
}   {μ : autoParam (MeasureTheory.…
· 使用定理 `MeasureTheory.NullMeasurableSet.mono_ac`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.NullMeas
urableSet s μ → ν.AbsolutelyC…
· 使用定理 `MeasureTheory.IsFundamentalDomain.nullMeasurableSet_smul`：nullMeasurable
Set_smul (h : IsFundamentalDomain G s μ) (g : G) : NullMeasurableSet (g • s) μ
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.IsFundamentalDomain.iUnion_smul_ae_eq`：iUnion_smul_ae_eq (
h : IsFundamentalDomain G s μ) : ⋃ g : G, g • s =ᵐ[μ] univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
theorem sum_restrict_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) :
    (sum fun g : G => ν.restrict (g • s)) = ν := by
  rw [← restrict_iUnion_ae (h.aedisjoint.mono fun i j h => hν h) fun g =>
      (h.nullMeasurableSet_smul g).mono_ac hν,
    restrict_congr_set (hν h.iUnion_smul_ae_eq), restrict_univ]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum_of_ac** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：lintegral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : 
α -> Real>=0∞) : ∫⁻ x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν
参数：h : IsFundamentalDomain G s μ；hν : ν ≪ μ；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
· 使用定理 `MeasureTheory.IsFundamentalDomain.sum_restrict_of_ac`：sum_restrict_of_ac
 (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) : (sum fun g : G => ν.restrict (g 
• s)) = ν
-/
theorem lintegral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν := by
  rw [← lintegral_sum_measure, h.sum_restrict_of_ac hν]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.sum_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.IsFundamentalDomain`。
形式化陈述：sum_restrict (h : IsFundamentalDomain G s μ) : (sum fun g : G => μ.restric
t (g • s)) = μ
参数：h : IsFundamentalDomain G s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.sum_restrict_of_ac`：sum_restrict_of_ac
 (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) : (sum fun g : G => ν.restrict (g 
• s)) = ν
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem sum_restrict (h : IsFundamentalDomain G s μ) : (sum fun g : G => μ.restrict (g • s)) = μ :=
  h.sum_restrict_of_ac (refl _)

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.IsFundamentalDomain`。
形式化陈述：lintegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) : ∫⁻
 x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ
参数：h : IsFundamentalDomain G s μ；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum_of_ac`：lintegral_eq_
tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α -> Real>=0∞) : ∫⁻
 x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem lintegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ :=
  h.lintegral_eq_tsum_of_ac (refl _) f

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum'** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：lintegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) : ∫
⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ
参数：h : IsFundamentalDomain G s μ；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum`：lintegral_eq_tsum (
h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻
 x in g • s, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `MeasureTheory.MeasurePreserving.setLIntegral_comp_emb`：setLIntegral_comp
_emb (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) (s : Set α) : ∫⁻ a in s, 
f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `measurableEmbedding_const_smul`：∀ {G : Type u_1} {α : Type u_3} [inst : 
MeasurableSpace α] [inst_1 : Group G] [inst_2 : MulAction G α]   [MeasurableCons
tSMul G α] (c : G), …
-/
theorem lintegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ := h.lintegral_eq_tsum f
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm <|
      (measurePreserving_smul g⁻¹ μ).setLIntegral_comp_emb (measurableEmbedding_const_smul _) _ _
/-
**MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum''** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α] {s : Set α}   {μ : MeasureTheory.Measure α} [Measur
ableConstSMul G α] [MeasureTheory.SMulInvariantMeasure G α μ] [Countable G],   M
easureTheory.IsFundamentalDomain G s μ →     ∀ (f : α → ENNReal), ∫⁻ (x : α), f 
x ∂μ = ∑' (g : G), ∫⁻ (x : α) in s, f (g • x) ∂μ
参数：f : α → ENNReal；x : α；g : G；x : α；g • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum'`：lintegral_eq_tsum'
 (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ = ∑' g : G, 
∫⁻ x in s, f (g⁻¹ • x) ∂μ
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
-/
@[to_additive] lemma lintegral_eq_tsum'' (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in s, f (g • x) ∂μ :=
  (lintegral_eq_tsum' h f).trans ((Equiv.inv G).tsum_eq (fun g ↦ ∫⁻ (x : α) in s, f (g • x) ∂μ))

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.setLIntegral_eq_tsum** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：setLIntegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) (
t : Set α) : ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t inter g • s, f x ∂μ
参数：h : IsFundamentalDomain G s μ；f : α -> Real>=0∞；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum_of_ac`：lintegral_eq_
tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α -> Real>=0∞) : ∫⁻
 x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsFundamentalDomain.restrict_restrict`：restrict_restrict (
h : IsFundamentalDomain G s μ) (g : G) (t : Set α) : (μ.restrict t).restrict (g 
• s) = μ.restrict (g • s inter t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setLIntegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :=
  calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ.restrict t :=
      h.lintegral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous _
    _ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := by simp only [h.restrict_restrict, inter_comm]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.setLIntegral_eq_tsum'** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：setLIntegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) 
(t : Set α) : ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • t inter s, f (g⁻¹ • x) ∂
μ
参数：h : IsFundamentalDomain G s μ；f : α -> Real>=0∞；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.setLIntegral_eq_tsum`：setLIntegral_eq_
tsum (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) (t : Set α) : ∫⁻ x in t
, f x ∂μ = ∑' g : G, ∫⁻ x in t inter g • s, …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.smul_set_inter`：smul_set_inter : a • (s inter t) = a • s inter a • t
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `MeasureTheory.MeasurePreserving.setLIntegral_comp_emb`：setLIntegral_comp
_emb (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) (s : Set α) : ∫⁻ a in s, 
f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `measurableEmbedding_const_smul`：∀ {G : Type u_1} {α : Type u_3} [inst : 
MeasurableSpace α] [inst_1 : Group G] [inst_2 : MulAction G α]   [MeasurableCons
tSMul G α] (c : G), …
-/
theorem setLIntegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := h.setLIntegral_eq_tsum f t
    _ = ∑' g : G, ∫⁻ x in t ∩ g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • (g • t ∩ s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm <|
      (measurePreserving_smul g⁻¹ μ).setLIntegral_comp_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.measure_eq_tsum_of_ac** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：measure_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (t : Se
t α) : ν t = ∑' g : G, ν (t inter g • s)
参数：h : IsFundamentalDomain G s μ；hν : ν ≪ μ；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_one`：setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ =
 μ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply₀`：restrict_apply₀ (ht : NullMeasura
bleSet t (μ.restrict s)) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.NullMeasurableSet.mono_ac`：∀ {α : Type u_1} {mα : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.NullMeas
urableSet s μ → ν.AbsolutelyC…
· 使用定理 `MeasureTheory.IsFundamentalDomain.nullMeasurableSet_smul`：nullMeasurable
Set_smul (h : IsFundamentalDomain G s μ) (g : G) : NullMeasurableSet (g • s) μ
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum_of_ac`：lintegral_eq_
tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α -> Real>=0∞) : ∫⁻
 x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν
-/
theorem measure_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (t : Set α) :
    ν t = ∑' g : G, ν (t ∩ g • s) := by
  have H : ν.restrict t ≪ μ := Measure.restrict_le_self.absolutelyContinuous.trans hν
  simpa only [setLIntegral_one, Pi.one_def,
    Measure.restrict_apply₀ ((h.nullMeasurableSet_smul _).mono_ac H), inter_comm] using
    h.lintegral_eq_tsum_of_ac H 1

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.measure_eq_tsum'** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.IsFundamentalDomain`。
形式化陈述：measure_eq_tsum' (h : IsFundamentalDomain G s μ) (t : Set α) : μ t = ∑' g 
: G, μ (t inter g • s)
参数：h : IsFundamentalDomain G s μ；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_eq_tsum_of_ac`：measure_eq_tsum
_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (t : Set α) : ν t = ∑' g : G
, ν (t inter g • s)
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
-/
theorem measure_eq_tsum' (h : IsFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (t ∩ g • s) :=
  h.measure_eq_tsum_of_ac AbsolutelyContinuous.rfl t

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.measure_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.IsFundamentalDomain`。
形式化陈述：measure_eq_tsum (h : IsFundamentalDomain G s μ) (t : Set α) : μ t = ∑' g :
 G, μ (g • t inter s)
参数：h : IsFundamentalDomain G s μ；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_one`：setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ =
 μ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsFundamentalDomain.setLIntegral_eq_tsum'`：setLIntegral_eq
_tsum' (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) (t : Set α) : ∫⁻ x in
 t, f x ∂μ = ∑' g : G, ∫⁻ x in g • t inter s,…
-/
theorem measure_eq_tsum (h : IsFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (g • t ∩ s) := by
  simpa only [setLIntegral_one] using h.setLIntegral_eq_tsum' (fun _ => 1) t

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.measure_zero_of_invariant** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：measure_zero_of_invariant (h : IsFundamentalDomain G s μ) (t : Set α) (ht 
: forall g : G, g • t = t) (hts : μ (t inter s) = 0) : μ t = 0
参数：h : IsFundamentalDomain G s μ；t : Set α；ht : forall g : G, g • t = t；hts : μ 
(t inter s) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_eq_tsum`：measure_eq_tsum (h : 
IsFundamentalDomain G s μ) (t : Set α) : μ t = ∑' g : G, μ (g • t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measure_zero_of_invariant (h : IsFundamentalDomain G s μ) (t : Set α)
    (ht : ∀ g : G, g • t = t) (hts : μ (t ∩ s) = 0) : μ t = 0 := by
  rw [measure_eq_tsum h]; simp [ht, hts]

/-- Given a measure space with an action of a finite group `G`, the measure of any `G`-invariant set
is determined by the measure of its intersection with a fundamental domain for the action of `G`. -/
@[to_additive measure_eq_card_smul_of_vadd_ae_eq_self /-- Given a measure space with an action of a
  finite additive group `G`, the measure of any `G`-invariant set is determined by the measure of
  its intersection with a fundamental domain for the action of `G`. -/]
/-
**MeasureTheory.IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self** 是 
Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：measure_eq_card_smul_of_smul_ae_eq_self [Finite G] (h : IsFundamentalDomai
n G s μ) (t : Set α) (ht : forall g : G, (g • t : Set α) =ᵐ[μ] t) : μ t = Nat.ca
rd G • μ (t inter s)
参数：h : IsFundamentalDomain G s μ；t : Set α；ht : forall g : G, (g • t : Set α) =ᵐ
[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_eq_tsum`：measure_eq_tsum (h : 
IsFundamentalDomain G s μ) (t : Set α) : μ t = ∑' g : G, μ (g • t inter s)
· 使用定理 `MeasureTheory.ae_eq_set_inter`：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measure_eq_card_smul_of_smul_ae_eq_self [Finite G] (h : IsFundamentalDomain G s μ)
    (t : Set α) (ht : ∀ g : G, (g • t : Set α) =ᵐ[μ] t) : μ t = Nat.card G • μ (t ∩ s) := by
  have : Fintype G := Fintype.ofFinite G
  rw [h.measure_eq_tsum]
  replace ht : ∀ g : G, (g • t ∩ s : Set α) =ᵐ[μ] (t ∩ s : Set α) := fun g =>
    ae_eq_set_inter (ht g) (ae_eq_refl s)
  simp_rw [measure_congr (ht _), tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card,
    Finset.card_univ]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.setLIntegral_eq** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α] {s t : Set α}   {μ : MeasureTheory.Measure α} [Meas
urableConstSMul G α] [MeasureTheory.SMulInvariantMeasure G α μ] [Countable G],  
 MeasureTheory.IsFundamentalDomain G s μ →     MeasureTheory.IsFundamentalDomain
 G t μ →       ∀ (f : α → ENNReal), (∀ (g : G) (x : α), f (g • x) = f x) → ∫⁻ (x
 : α) in s, f x ∂μ = ∫⁻ (x : α) in t, f x ∂μ
参数：f : α → ENNReal；∀ (g : G) (x : α), f (g • x) = f x；x : α；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.setLIntegral_eq_tsum`：setLIntegral_eq_
tsum (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) (t : Set α) : ∫⁻ x in t
, f x ∂μ = ∑' g : G, ∫⁻ x in t inter g • s, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsFundamentalDomain.setLIntegral_eq_tsum'`：setLIntegral_eq
_tsum' (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) (t : Set α) : ∫⁻ x in
 t, f x ∂μ = ∑' g : G, ∫⁻ x in g • t inter s,…
-/
protected theorem setLIntegral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    (f : α → ℝ≥0∞) (hf : ∀ (g : G) (x), f (g • x) = f x) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ :=
  calc
    ∫⁻ x in s, f x ∂μ = ∑' g : G, ∫⁻ x in s ∩ g • t, f x ∂μ := ht.setLIntegral_eq_tsum _ _
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
    _ = ∫⁻ x in t, f x ∂μ := (hs.setLIntegral_eq_tsum' _ _).symm

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.measure_set_eq** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.IsFundamentalDomain`。
形式化陈述：measure_set_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain 
G t μ) {A : Set α} (hA₀ : MeasurableSet A) (hA : forall g : G, (fun x => g • x) 
⁻¹' A = A) : μ (A inter s) = μ (A inter t)
参数：hs : IsFundamentalDomain G s μ；ht : IsFundamentalDomain G t μ；hA₀ : Measurabl
eSet A；hA : forall g : G, (fun x => g • x) ⁻¹' A = A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.setLIntegral_eq`：∀ {G : Type u_1} {α :
 Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpace α
] {s t : Set α}   {μ : MeasureTheory.Me…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_comp_right`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_3}
 [inst : Zero M] {s : Set α} (f : β → α) {g : α → M} {x : β},   (f ⁻¹' s).indica
tor (g ∘ f) x …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem measure_set_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) {A : Set α}
    (hA₀ : MeasurableSet A) (hA : ∀ g : G, (fun x => g • x) ⁻¹' A = A) : μ (A ∩ s) = μ (A ∩ t) := by
  have : ∫⁻ x in s, A.indicator 1 x ∂μ = ∫⁻ x in t, A.indicator 1 x ∂μ := by
    refine hs.setLIntegral_eq ht (Set.indicator A fun _ => 1) fun g x ↦ ?_
    convert! (Set.indicator_comp_right (g • · : α → α) (g := fun _ ↦ (1 : ℝ≥0∞))).symm
    rw [hA g]
  simpa [Measure.restrict_apply hA₀, lintegral_indicator hA₀] using this

/-- If `s` and `t` are two fundamental domains of the same action, then their measures are equal. -/
@[to_additive /-- If `s` and `t` are two fundamental domains of the same action, then their measures
  are equal. -/]
/-
**MeasureTheory.IsFundamentalDomain.measure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α] {s t : Set α}   {μ : MeasureTheory.Measure α} [Meas
urableConstSMul G α] [MeasureTheory.SMulInvariantMeasure G α μ] [Countable G],  
 MeasureTheory.IsFundamentalDomain G s μ → MeasureTheory.IsFundamentalDomain G t
 μ → μ s = μ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_one`：setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ =
 μ s
· 使用定理 `MeasureTheory.IsFundamentalDomain.setLIntegral_eq`：∀ {G : Type u_1} {α :
 Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpace α
] {s t : Set α}   {μ : MeasureTheory.Me…
-/
protected theorem measure_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) :
    μ s = μ t := by
  simpa only [setLIntegral_one] using hs.setLIntegral_eq ht (fun _ => 1) fun _ _ => rfl

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.aestronglyMeasurable_on_iff** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α] {s t : Set α}   {μ : MeasureTheory.Measure α} [Meas
urableConstSMul G α] [MeasureTheory.SMulInvariantMeasure G α μ] [Countable G]   
{β : Type u_6} [inst_6 : TopologicalSpace β] [TopologicalSpace.PseudoMetrizableS
pace β],   MeasureTheory.IsFundamentalDomain G s μ →     MeasureTheory.IsFundame
ntalDomain G t μ →       ∀ {f : α → β},         (∀ (g : G) (x : α), f (g • x) = 
f x) →           (MeasureTheory.AEStronglyMeasurable f (μ.restrict s) ↔ MeasureT
heory.AEStronglyMeasurable f (μ.restrict t))
参数：∀ (g : G) (x : α), f (g • x) = f x；MeasureTheory.AEStronglyMeasurable f (μ.re
strict s) ↔ MeasureTheory.AEStronglyMeasurable f (μ.restrict t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsFundamentalDomain.restrict_restrict`：restrict_restrict (
h : IsFundamentalDomain G s μ) (g : G) (t : Set α) : (μ.restrict t).restrict (g 
• s) = μ.restrict (g • s inter t)
· 使用定理 `MeasureTheory.IsFundamentalDomain.sum_restrict_of_ac`：sum_restrict_of_ac
 (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) : (sum fun g : G => ν.restrict (g 
• s)) = ν
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.smul_set_inter`：smul_set_inter : a • (s inter t) = a • s inter a • t
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `inv_surjective`：inv_surjective : Function.Surjective (Inv.inv : G -> G)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `measurableEmbedding_const_smul`：∀ {G : Type u_1} {α : Type u_3} [inst : 
MeasurableSpace α] [inst_1 : Group G] [inst_2 : MulAction G α]   [MeasurableCons
tSMul G α] (c : G), …
· 使用定理 `Set.image_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : S
et β} {a : α}, (fun x => a • x) '' t = a • t
· 使用定理 `MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff`：MeasureTh
eory.MeasurePreserving.aestronglyMeasurable_comp_iff {β : Type*} {f : α -> β} {m
α : MeasurableSpace α} {μa : Measure α} {mβ : Measu…
· 使用定理 `MeasureTheory.MeasurePreserving.restrict_image_emb`：restrict_image_emb {
f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) (s : S
et α) : MeasurePreserving f (μa.restrict…
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
-/
protected theorem aestronglyMeasurable_on_iff {β : Type*} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α → β} (hf : ∀ (g : G) (x), f (g • x) = f x) :
    AEStronglyMeasurable f (μ.restrict s) ↔ AEStronglyMeasurable f (μ.restrict t) :=
  calc
    AEStronglyMeasurable f (μ.restrict s) ↔
        AEStronglyMeasurable f (Measure.sum fun g : G => μ.restrict (g • t ∩ s)) := by
      simp only [← ht.restrict_restrict,
        ht.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]
    _ ↔ ∀ g : G, AEStronglyMeasurable f (μ.restrict (g • (g⁻¹ • s ∩ t))) := by
      simp only [smul_set_inter, inter_comm, smul_inv_smul, aestronglyMeasurable_sum_measure_iff]
    _ ↔ ∀ g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g⁻¹⁻¹ • s ∩ t))) :=
      inv_surjective.forall
    _ ↔ ∀ g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g • s ∩ t))) := by simp only [inv_inv]
    _ ↔ ∀ g : G, AEStronglyMeasurable f (μ.restrict (g • s ∩ t)) := by
      refine forall_congr' fun g => ?_
      have he : MeasurableEmbedding (g⁻¹ • · : α → α) := measurableEmbedding_const_smul _
      rw [← image_smul, ← ((measurePreserving_smul g⁻¹ μ).restrict_image_emb he
        _).aestronglyMeasurable_comp_iff he]
      simp only [Function.comp_def, hf]
    _ ↔ AEStronglyMeasurable f (μ.restrict t) := by
      simp only [← aestronglyMeasurable_sum_measure_iff, ← hs.restrict_restrict,
        hs.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.hasFiniteIntegral_on_iff** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} {E : Type u_5} [inst : Group G] [inst_1 : 
MulAction G α] [inst_2 : MeasurableSpace α]   [inst_3 : NormedAddCommGroup E] {s
 t : Set α} {μ : MeasureTheory.Measure α} [MeasurableConstSMul G α]   [MeasureTh
eory.SMulInvariantMeasure G α μ] [Countable G],   MeasureTheory.IsFundamentalDom
ain G s μ →     MeasureTheory.IsFundamentalDomain G t μ →       ∀ {f : α → E},  
       (∀ (g : G) (x : α), f (g • x) = f x) →           (MeasureTheory.HasFinite
Integral f (μ.restrict s) ↔ MeasureTheory.HasFiniteIntegral f (μ.restrict t))
参数：∀ (g : G) (x : α), f (g • x) = f x；MeasureTheory.HasFiniteIntegral f (μ.restr
ict s) ↔ MeasureTheory.HasFiniteIntegral f (μ.restrict t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.setLIntegral_eq`：∀ {G : Type u_1} {α :
 Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpace α
] {s t : Set α}   {μ : MeasureTheory.Me…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem hasFiniteIntegral_on_iff (hs : IsFundamentalDomain G s μ)
    (ht : IsFundamentalDomain G t μ) {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) :
    HasFiniteIntegral f (μ.restrict s) ↔ HasFiniteIntegral f (μ.restrict t) := by
  dsimp only [HasFiniteIntegral]
  rw [hs.setLIntegral_eq ht]
  intro g x; rw [hf]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.integrableOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} {E : Type u_5} [inst : Group G] [inst_1 : 
MulAction G α] [inst_2 : MeasurableSpace α]   [inst_3 : NormedAddCommGroup E] {s
 t : Set α} {μ : MeasureTheory.Measure α} [MeasurableConstSMul G α]   [MeasureTh
eory.SMulInvariantMeasure G α μ] [Countable G],   MeasureTheory.IsFundamentalDom
ain G s μ →     MeasureTheory.IsFundamentalDomain G t μ →       ∀ {f : α → E},  
       (∀ (g : G) (x : α), f (g • x) = f x) → (MeasureTheory.IntegrableOn f s μ 
↔ MeasureTheory.IntegrableOn f t μ)
参数：∀ (g : G) (x : α), f (g • x) = f x；MeasureTheory.IntegrableOn f s μ ↔ Measure
Theory.IntegrableOn f t μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `MeasureTheory.IsFundamentalDomain.aestronglyMeasurable_on_iff`：∀ {G : Ty
pe u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : Measu
rableSpace α] {s t : Set α}   {μ : MeasureTheory.Me…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IsFundamentalDomain.hasFiniteIntegral_on_iff`：∀ {G : Type 
u_1} {α : Type u_3} {E : Type u_5} [inst : Group G] [inst_1 : MulAction G α] [in
st_2 : MeasurableSpace α]   [inst_3 : NormedAddC…
-/
protected theorem integrableOn_iff (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) : IntegrableOn f s μ ↔ IntegrableOn f t μ :=
  and_congr (hs.aestronglyMeasurable_on_iff ht hf) (hs.hasFiniteIntegral_on_iff ht hf)

variable [NormedSpace ℝ E]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.integral_eq_tsum_of_ac** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：integral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α
 -> E) (hf : Integrable f ν) : ∫ x, f x ∂ν = ∑' g : G, ∫ x in g • s, f x ∂ν
参数：h : IsFundamentalDomain G s μ；hν : ν ≪ μ；f : α -> E；hf : Integrable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_sum_measure`：integral_sum_measure (hf : Integrabl
e f (Measure.sum μ)) : ∫ x, f x ∂Measure.sum μ = ∑' i, ∫ x, f x ∂μ i
· 使用定理 `MeasureTheory.IsFundamentalDomain.sum_restrict_of_ac`：sum_restrict_of_ac
 (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) : (sum fun g : G => ν.restrict (g 
• s)) = ν
-/
theorem integral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α → E)
    (hf : Integrable f ν) : ∫ x, f x ∂ν = ∑' g : G, ∫ x in g • s, f x ∂ν := by
  rw [← MeasureTheory.integral_sum_measure, h.sum_restrict_of_ac hν]
  rw [h.sum_restrict_of_ac hν]
  exact hf

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.integral_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.IsFundamentalDomain`。
形式化陈述：integral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α -> E) (hf : Integr
able f μ) : ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ
参数：h : IsFundamentalDomain G s μ；f : α -> E；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.integral_eq_tsum_of_ac`：integral_eq_ts
um_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α -> E) (hf : Integra
ble f ν) : ∫ x, f x ∂ν = ∑' g : G, ∫ x in g • …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.refl`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α), μ.AbsolutelyContinuous μ
-/
theorem integral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → E) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ :=
  integral_eq_tsum_of_ac h (by rfl) f hf

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.integral_eq_tsum'** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.IsFundamentalDomain`。
形式化陈述：integral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α -> E) (hf : Integ
rable f μ) : ∫ x, f x ∂μ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ
参数：h : IsFundamentalDomain G s μ；f : α -> E；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.integral_eq_tsum`：integral_eq_tsum (h 
: IsFundamentalDomain G s μ) (f : α -> E) (hf : Integrable f μ) : ∫ x, f x ∂μ = 
∑' g : G, ∫ x in g • s, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `MeasureTheory.MeasurePreserving.setIntegral_image_emb`：∀ {X : Type u_1} 
{E : Type u_3} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E] [inst_1 : 
NormedSpace ℝ E]   {μ : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `measurableEmbedding_const_smul`：∀ {G : Type u_1} {α : Type u_3} [inst : 
MeasurableSpace α] [inst_1 : Group G] [inst_2 : MulAction G α]   [MeasurableCons
tSMul G α] (c : G), …
-/
theorem integral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α → E) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ := h.integral_eq_tsum f hf
    _ = ∑' g : G, ∫ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g =>
      (measurePreserving_smul g⁻¹ μ).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _
/-
**MeasureTheory.IsFundamentalDomain.integral_eq_tsum''** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} {E : Type u_5} [inst : Group G] [inst_1 : 
MulAction G α] [inst_2 : MeasurableSpace α]   [inst_3 : NormedAddCommGroup E] {s
 : Set α} {μ : MeasureTheory.Measure α} [MeasurableConstSMul G α]   [MeasureTheo
ry.SMulInvariantMeasure G α μ] [Countable G] [inst_7 : NormedSpace ℝ E],   Measu
reTheory.IsFundamentalDomain G s μ →     ∀ (f : α → E), MeasureTheory.Integrable
 f μ → ∫ (x : α), f x ∂μ = ∑' (g : G), ∫ (x : α) in s, f (g • x) ∂μ
参数：f : α → E；x : α；g : G；x : α；g • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.IsFundamentalDomain.integral_eq_tsum'`：integral_eq_tsum' (
h : IsFundamentalDomain G s μ) (f : α -> E) (hf : Integrable f μ) : ∫ x, f x ∂μ 
= ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
-/
@[to_additive] lemma integral_eq_tsum'' (h : IsFundamentalDomain G s μ)
    (f : α → E) (hf : Integrable f μ) : ∫ x, f x ∂μ = ∑' g : G, ∫ x in s, f (g • x) ∂μ :=
  (integral_eq_tsum' h f hf).trans ((Equiv.inv G).tsum_eq (fun g ↦ ∫ (x : α) in s, f (g • x) ∂μ))

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.setIntegral_eq_tsum** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：setIntegral_eq_tsum (h : IsFundamentalDomain G s μ) {f : α -> E} {t : Set 
α} (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t inter g • s
, f x ∂μ
参数：h : IsFundamentalDomain G s μ；hf : IntegrableOn f t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.integral_eq_tsum_of_ac`：integral_eq_ts
um_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α -> E) (hf : Integra
ble f ν) : ∫ x, f x ∂ν = ∑' g : G, ∫ x in g • …
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsFundamentalDomain.restrict_restrict`：restrict_restrict (
h : IsFundamentalDomain G s μ) (g : G) (t : Set α) : (μ.restrict t).restrict (g 
• s) = μ.restrict (g • s inter t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_eq_tsum (h : IsFundamentalDomain G s μ) {f : α → E} {t : Set α}
    (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ :=
  calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ.restrict t :=
      h.integral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous f hf
    _ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ := by
      simp only [h.restrict_restrict, inter_comm]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.setIntegral_eq_tsum'** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：setIntegral_eq_tsum' (h : IsFundamentalDomain G s μ) {f : α -> E} {t : Set
 α} (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • t inter 
s, f (g⁻¹ • x) ∂μ
参数：h : IsFundamentalDomain G s μ；hf : IntegrableOn f t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.setIntegral_eq_tsum`：setIntegral_eq_ts
um (h : IsFundamentalDomain G s μ) {f : α -> E} {t : Set α} (hf : IntegrableOn f
 t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.smul_set_inter`：smul_set_inter : a • (s inter t) = a • s inter a • t
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `MeasureTheory.MeasurePreserving.setIntegral_image_emb`：∀ {X : Type u_1} 
{E : Type u_3} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E] [inst_1 : 
NormedSpace ℝ E]   {μ : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `measurableEmbedding_const_smul`：∀ {G : Type u_1} {α : Type u_3} [inst : 
MeasurableSpace α] [inst_1 : Group G] [inst_2 : MulAction G α]   [MeasurableCons
tSMul G α] (c : G), …
-/
theorem setIntegral_eq_tsum' (h : IsFundamentalDomain G s μ) {f : α → E} {t : Set α}
    (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t ∩ g • s, f x ∂μ := h.setIntegral_eq_tsum hf
    _ = ∑' g : G, ∫ x in t ∩ g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in g⁻¹ • (g • t ∩ s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
    _ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
      tsum_congr fun g =>
        (measurePreserving_smul g⁻¹ μ).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.setIntegral_eq** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} {E : Type u_5} [inst : Group G] [inst_1 : 
MulAction G α] [inst_2 : MeasurableSpace α]   [inst_3 : NormedAddCommGroup E] {s
 t : Set α} {μ : MeasureTheory.Measure α} [MeasurableConstSMul G α]   [MeasureTh
eory.SMulInvariantMeasure G α μ] [Countable G] [inst_7 : NormedSpace ℝ E],   Mea
sureTheory.IsFundamentalDomain G s μ →     MeasureTheory.IsFundamentalDomain G t
 μ →       ∀ {f : α → E}, (∀ (g : G) (x : α), f (g • x) = f x) → ∫ (x : α) in s,
 f x ∂μ = ∫ (x : α) in t, f x ∂μ
参数：∀ (g : G) (x : α), f (g • x) = f x；x : α；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.integrableOn_iff`：∀ {G : Type u_1} {α 
: Type u_3} {E : Type u_5} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : M
easurableSpace α]   [inst_3 : NormedAddC…
· 使用定理 `MeasureTheory.IsFundamentalDomain.setIntegral_eq_tsum`：setIntegral_eq_ts
um (h : IsFundamentalDomain G s μ) {f : α -> E} {t : Set α} (hf : IntegrableOn f
 t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsFundamentalDomain.setIntegral_eq_tsum'`：setIntegral_eq_t
sum' (h : IsFundamentalDomain G s μ) {f : α -> E} {t : Set α} (hf : IntegrableOn
 f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x i…
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
-/
protected theorem setIntegral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  by_cases hfs : IntegrableOn f s μ
  · have hft : IntegrableOn f t μ := by rwa [ht.integrableOn_iff hs hf]
    calc
      ∫ x in s, f x ∂μ = ∑' g : G, ∫ x in s ∩ g • t, f x ∂μ := ht.setIntegral_eq_tsum hfs
      _ = ∑' g : G, ∫ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
      _ = ∫ x in t, f x ∂μ := (hs.setIntegral_eq_tsum' hft).symm
  · rw [integral_undef hfs, integral_undef]
    rwa [hs.integrableOn_iff ht hf] at hfs

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` such that the sets `g • t ∩ s` are pairwise a.e.-disjoint
has measure at most `μ s`. -/
@[to_additive /-- If the additive action of a countable group `G` admits an invariant measure `μ`
  with a fundamental domain `s`, then every null-measurable set `t` such that the sets `g +ᵥ t ∩ s`
  are pairwise a.e.-disjoint has measure at most `μ s`. -/]
/-
**MeasureTheory.IsFundamentalDomain.measure_le_of_pairwise_disjoint** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：measure_le_of_pairwise_disjoint (hs : IsFundamentalDomain G s μ) (ht : Nul
lMeasurableSet t μ) (hd : Pairwise (AEDisjoint μ on fun g : G => g • t inter s))
 : μ t <= μ s
参数：hs : IsFundamentalDomain G s μ；ht : NullMeasurableSet t μ；hd : Pairwise (AEDi
sjoint μ on fun g : G => g • t inter s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_eq_tsum`：measure_eq_tsum (h : 
IsFundamentalDomain G s μ) (t : Set α) : μ t = ∑' g : G, μ (g • t inter s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_iUnion₀`：measure_iUnion₀ [Countable ι] {f : ι -> S
et α} (hd : Pairwise (AEDisjoint μ on f)) (h : forall i, NullMeasurableSet (f i)
 μ) : μ (⋃ i, f i) …
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.smul`：∀ {G : Type u} {α : Type w} {m : M
easurableSpace α} [inst : Group G] [inst_1 : MulAction G α]   {μ : MeasureTheory
.Measure α} [MeasureTheory…
· 使用定理 `MeasureTheory.IsFundamentalDomain.nullMeasurableSet`：∀ {G : Type u_1} {α
 : Type u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s 
: Set α}   {μ : autoParam (MeasureTheory.…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem measure_le_of_pairwise_disjoint (hs : IsFundamentalDomain G s μ)
    (ht : NullMeasurableSet t μ) (hd : Pairwise (AEDisjoint μ on fun g : G => g • t ∩ s)) :
    μ t ≤ μ s :=
  calc
    μ t = ∑' g : G, μ (g • t ∩ s) := hs.measure_eq_tsum t
    _ = μ (⋃ g : G, g • t ∩ s) := Eq.symm <| measure_iUnion₀ hd fun _ =>
      (ht.smul _).inter hs.nullMeasurableSet
    _ ≤ μ s := measure_mono (iUnion_subset fun _ => inter_subset_right)

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` of measure strictly greater than `μ s` contains two
points `x y` such that `g • x = y` for some `g ≠ 1`. -/
@[to_additive /-- If the additive action of a countable group `G` admits an invariant measure `μ`
  with a fundamental domain `s`, then every null-measurable set `t` of measure strictly greater than
  `μ s` contains two points `x y` such that `g +ᵥ x = y` for some `g ≠ 0`. -/]
/-
**MeasureTheory.IsFundamentalDomain.exists_ne_one_smul_eq** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：exists_ne_one_smul_eq (hs : IsFundamentalDomain G s μ) (htm : NullMeasurab
leSet t μ) (ht : μ s < μ t) : exists x in t, exists y in t, exists g, g != (1 : 
G) ∧ g • x = y
参数：hs : IsFundamentalDomain G s μ；htm : NullMeasurableSet t μ；ht : μ s < μ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_le_of_pairwise_disjoint`：measu
re_le_of_pairwise_disjoint (hs : IsFundamentalDomain G s μ) (ht : NullMeasurable
Set t μ) (hd : Pairwise (AEDisjoint μ on fun g : G => g…
· 使用定理 `Pairwise.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {f : ι → Set α},   Pairwise (Function.onFun D
isjoint f…
· 使用定理 `Disjoint.inf_right`：Disjoint.inf_right (h : Disjoint a b) : Disjoint a (
b ⊓ c)
· 使用定理 `Disjoint.inf_left`：Disjoint.inf_left (h : Disjoint a b) : Disjoint (a ⊓ 
c) b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_mul_eq_one`：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
theorem exists_ne_one_smul_eq (hs : IsFundamentalDomain G s μ) (htm : NullMeasurableSet t μ)
    (ht : μ s < μ t) : ∃ x ∈ t, ∃ y ∈ t, ∃ g, g ≠ (1 : G) ∧ g • x = y := by
  contrapose! ht
  refine hs.measure_le_of_pairwise_disjoint htm (Pairwise.aedisjoint fun g₁ g₂ hne => ?_)
  dsimp [Function.onFun]
  refine (Disjoint.inf_left _ ?_).inf_right _
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy : g₂ • y = g₁ • x⟩
  refine ht x hx y hy (g₂⁻¹ * g₁) (mt inv_mul_eq_one.1 hne.symm) ?_
  rw [mul_smul, ← hxy, inv_smul_smul]

/-- If `f` is invariant under the action of a countable group `G`, and `μ` is a `G`-invariant
  measure with a fundamental domain `s`, then the `essSup` of `f` restricted to `s` is the same as
  that of `f` on all of its domain. -/
@[to_additive /-- If `f` is invariant under the action of a countable additive group `G`, and `μ`
  is a `G`-invariant measure with a fundamental domain `s`, then the `essSup` of `f` restricted to
  `s` is the same as that of `f` on all of its domain. -/]
/-
**MeasureTheory.IsFundamentalDomain.essSup_measure_restrict** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：essSup_measure_restrict (hs : IsFundamentalDomain G s μ) {f : α -> Real>=0
∞} (hf : forall γ : G, forall x : α, f (γ • x) = f x) : essSup f (μ.restrict s) 
= essSup f μ
参数：hs : IsFundamentalDomain G s μ；hf : forall γ : G, forall x : α, f (γ • x) = f
 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `essSup_mono_measure'`：essSup_mono_measure' {f : α -> β} (hμν : ν <= μ) (
hνf : IsCoboundedUnder (· <= ·) (ae ν) f
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `essSup_eq_sInf`：essSup_eq_sInf {m : MeasurableSpace α} (μ : Measure α) (
f : α -> β) : essSup f μ = sInf { a | μ { x | a < f x } = 0 }
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_zero_of_invariant`：measure_zer
o_of_invariant (h : IsFundamentalDomain G s μ) (t : Set α) (ht : forall g : G, g
 • t = t) (hts : μ (t inter s) = 0) : μ t = 0
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.Measure.restrict_apply₀'`：restrict_apply₀' (hs : NullMeasu
rableSet s μ) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.IsFundamentalDomain.nullMeasurableSet`：∀ {G : Type u_1} {α
 : Type u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s 
: Set α}   {μ : autoParam (MeasureTheory.…
-/
theorem essSup_measure_restrict (hs : IsFundamentalDomain G s μ) {f : α → ℝ≥0∞}
    (hf : ∀ γ : G, ∀ x : α, f (γ • x) = f x) : essSup f (μ.restrict s) = essSup f μ := by
  refine le_antisymm (essSup_mono_measure' Measure.restrict_le_self) ?_
  rw [essSup_eq_sInf (μ.restrict s) f, essSup_eq_sInf μ f]
  refine sInf_le_sInf ?_
  rintro a (ha : (μ.restrict s) {x : α | a < f x} = 0)
  rw [Measure.restrict_apply₀' hs.nullMeasurableSet] at ha
  refine measure_zero_of_invariant hs _ ?_ ha
  intro γ
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  simp only [mem_ofPred_eq, hf γ⁻¹ x]

end IsFundamentalDomain

/-! ### Interior/frontier of a fundamental domain -/

section MeasurableSpace

variable (G) [Group G] [MulAction G α] (s : Set α) {x : α}

/-- The boundary of a fundamental domain, those points of the domain that also lie in a nontrivial
translate. -/
@[to_additive MeasureTheory.addFundamentalFrontier /-- The boundary of a fundamental domain, those
  points of the domain that also lie in a nontrivial translate. -/]
/-
**MeasureTheory.fundamentalFrontier** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：fundamentalFrontier : Set α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fundamentalFrontier : Set α :=
  s ∩ ⋃ (g : G) (_ : g ≠ 1), g • s

/-- The interior of a fundamental domain, those points of the domain not lying in any translate. -/
@[to_additive MeasureTheory.addFundamentalInterior /-- The interior of a fundamental domain, those
  points of the domain not lying in any translate. -/]
/-
**MeasureTheory.fundamentalInterior** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：fundamentalInterior : Set α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fundamentalInterior : Set α :=
  s \ ⋃ (g : G) (_ : g ≠ 1), g • s

variable {G s}

@[to_additive (attr := simp) MeasureTheory.mem_addFundamentalFrontier]
/-
**MeasureTheory.mem_fundamentalFrontier** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：mem_fundamentalFrontier : x in fundamentalFrontier G s ↔ x in s ∧ exists g
 : G, g != 1 ∧ x in g • s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_fundamentalFrontier :
    x ∈ fundamentalFrontier G s ↔ x ∈ s ∧ ∃ g : G, g ≠ 1 ∧ x ∈ g • s := by
  simp [fundamentalFrontier]

@[to_additive (attr := simp) MeasureTheory.mem_addFundamentalInterior]
/-
**MeasureTheory.mem_fundamentalInterior** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：mem_fundamentalInterior : x in fundamentalInterior G s ↔ x in s ∧ forall g
 : G, g != 1 -> x ∉ g • s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_fundamentalInterior :
    x ∈ fundamentalInterior G s ↔ x ∈ s ∧ ∀ g : G, g ≠ 1 → x ∉ g • s := by
  simp [fundamentalInterior]

@[to_additive MeasureTheory.addFundamentalFrontier_subset]
/-
**MeasureTheory.fundamentalFrontier_subset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：fundamentalFrontier_subset : fundamentalFrontier G s subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem fundamentalFrontier_subset : fundamentalFrontier G s ⊆ s :=
  inter_subset_left

@[to_additive MeasureTheory.addFundamentalInterior_subset]
/-
**MeasureTheory.fundamentalInterior_subset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：fundamentalInterior_subset : fundamentalInterior G s subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
theorem fundamentalInterior_subset : fundamentalInterior G s ⊆ s :=
  sdiff_subset

variable (G s)

@[to_additive MeasureTheory.disjoint_addFundamentalInterior_addFundamentalFrontier]
/-
**MeasureTheory.disjoint_fundamentalInterior_fundamentalFrontier** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：disjoint_fundamentalInterior_fundamentalFrontier : Disjoint (fundamentalIn
terior G s) (fundamentalFrontier G s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
-/
theorem disjoint_fundamentalInterior_fundamentalFrontier :
    Disjoint (fundamentalInterior G s) (fundamentalFrontier G s) :=
  disjoint_sdiff_self_left.mono_right inf_le_right

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_union_addFundamentalFrontier]
/-
**MeasureTheory.fundamentalInterior_union_fundamentalFrontier** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：fundamentalInterior_union_fundamentalFrontier : fundamentalInterior G s un
ion fundamentalFrontier G s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
-/
theorem fundamentalInterior_union_fundamentalFrontier :
    fundamentalInterior G s ∪ fundamentalFrontier G s = s :=
  sdiff_union_inter _ _

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_union_addFundamentalInterior]
/-
**MeasureTheory.fundamentalFrontier_union_fundamentalInterior** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：fundamentalFrontier_union_fundamentalInterior : fundamentalFrontier G s un
ion fundamentalInterior G s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
-/
theorem fundamentalFrontier_union_fundamentalInterior :
    fundamentalFrontier G s ∪ fundamentalInterior G s = s :=
  inter_union_sdiff _ _

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalInterior]
/-
**MeasureTheory.sdiff_fundamentalInterior** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：sdiff_fundamentalInterior : s \ fundamentalInterior G s = fundamentalFront
ier G s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
-/
theorem sdiff_fundamentalInterior : s \ fundamentalInterior G s = fundamentalFrontier G s :=
  sdiff_sdiff_right_self

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalFrontier]
/-
**MeasureTheory.sdiff_fundamentalFrontier** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：sdiff_fundamentalFrontier : s \ fundamentalFrontier G s = fundamentalInter
ior G s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
-/
theorem sdiff_fundamentalFrontier : s \ fundamentalFrontier G s = fundamentalInterior G s :=
  sdiff_self_inter

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_vadd]
/-
**MeasureTheory.fundamentalFrontier_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：fundamentalFrontier_smul [Group H] [MulAction H α] [SMulCommClass H G α] (
g : H) : fundamentalFrontier G (g • s) = g • fundamentalFrontier G s
参数：g : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_inter`：smul_set_inter : a • (s inter t) = a • s inter a • t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.smul_set_iUnion`：smul_set_iUnion (a : α) (s : ι -> Set β) : a • ⋃ i,
 s i = ⋃ i, a • s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fundamentalFrontier_smul [Group H] [MulAction H α] [SMulCommClass H G α] (g : H) :
    fundamentalFrontier G (g • s) = g • fundamentalFrontier G s := by
  simp_rw [fundamentalFrontier, smul_set_inter, smul_set_iUnion, smul_comm g (_ : G) (_ : Set α)]

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_vadd]
/-
**MeasureTheory.fundamentalInterior_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：fundamentalInterior_smul [Group H] [MulAction H α] [SMulCommClass H G α] (
g : H) : fundamentalInterior G (g • s) = g • fundamentalInterior G s
参数：g : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_sdiff`：smul_set_sdiff : a • (s \ t) = a • s \ a • t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.smul_set_iUnion`：smul_set_iUnion (a : α) (s : ι -> Set β) : a • ⋃ i,
 s i = ⋃ i, a • s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fundamentalInterior_smul [Group H] [MulAction H α] [SMulCommClass H G α] (g : H) :
    fundamentalInterior G (g • s) = g • fundamentalInterior G s := by
  simp_rw [fundamentalInterior, smul_set_sdiff, smul_set_iUnion, smul_comm g (_ : G) (_ : Set α)]

@[to_additive MeasureTheory.pairwise_disjoint_addFundamentalInterior]
/-
**MeasureTheory.pairwise_disjoint_fundamentalInterior** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：pairwise_disjoint_fundamentalInterior : Pairwise (Disjoint on fun g : G =>
 g • fundamentalInterior G s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.mem_fundamentalInterior`：mem_fundamentalInterior : x in fu
ndamentalInterior G s ↔ x in s ∧ forall g : G, g != 1 -> x ∉ g • s
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `inv_mul_eq_iff_eq_mul`：inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem pairwise_disjoint_fundamentalInterior :
    Pairwise (Disjoint on fun g : G => g • fundamentalInterior G s) := by
  refine fun a b hab => disjoint_left.2 ?_
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  rw [mem_fundamentalInterior] at hx hy
  refine hx.2 (a⁻¹ * b) ?_ ?_
  · rwa [Ne, inv_mul_eq_iff_eq_mul, mul_one, eq_comm]
  · simpa [mul_smul, ← hxy, mem_inv_smul_set_iff] using hy.1

variable [Countable G] [MeasurableSpace α] [MeasurableConstSMul G α]
  {μ : Measure α} [SMulInvariantMeasure G α μ]

@[to_additive MeasureTheory.NullMeasurableSet.addFundamentalFrontier]
/-
**MeasureTheory.NullMeasurableSet.fundamentalFrontier** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.NullMeasurableSet`。
形式化陈述：∀ (G : Type u_1) {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
(s : Set α) [Countable G]   [inst_3 : MeasurableSpace α] [MeasurableConstSMul G 
α] {μ : MeasureTheory.Measure α}   [MeasureTheory.SMulInvariantMeasure G α μ],  
 MeasureTheory.NullMeasurableSet s μ → MeasureTheory.NullMeasurableSet (MeasureT
heory.fundamentalFrontier G s) μ
参数：G : Type u_1；s : Set α；MeasureTheory.fundamentalFrontier G s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.iUnion`：∀ {α : Type u_2} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} {ι : Sort u_5} [Countable ι] {s : ι → Se
t α},   (∀ (i : ι), MeasureT…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `MeasureTheory.NullMeasurableSet.smul`：∀ {G : Type u} {α : Type w} {m : M
easurableSpace α} [inst : Group G] [inst_1 : MulAction G α]   {μ : MeasureTheory
.Measure α} [MeasureTheory…
-/
protected theorem NullMeasurableSet.fundamentalFrontier (hs : NullMeasurableSet s μ) :
    NullMeasurableSet (fundamentalFrontier G s) μ :=
  hs.inter <| .iUnion fun _ => .iUnion fun _ => hs.smul _

@[to_additive MeasureTheory.NullMeasurableSet.addFundamentalInterior]
/-
**MeasureTheory.NullMeasurableSet.fundamentalInterior** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.NullMeasurableSet`。
形式化陈述：∀ (G : Type u_1) {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
(s : Set α) [Countable G]   [inst_3 : MeasurableSpace α] [MeasurableConstSMul G 
α] {μ : MeasureTheory.Measure α}   [MeasureTheory.SMulInvariantMeasure G α μ],  
 MeasureTheory.NullMeasurableSet s μ → MeasureTheory.NullMeasurableSet (MeasureT
heory.fundamentalInterior G s) μ
参数：G : Type u_1；s : Set α；MeasureTheory.fundamentalInterior G s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.diff`：∀ {α : Type u_2} {m0 : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasura
bleSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.iUnion`：∀ {α : Type u_2} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} {ι : Sort u_5} [Countable ι] {s : ι → Se
t α},   (∀ (i : ι), MeasureT…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `MeasureTheory.NullMeasurableSet.smul`：∀ {G : Type u} {α : Type w} {m : M
easurableSpace α} [inst : Group G] [inst_1 : MulAction G α]   {μ : MeasureTheory
.Measure α} [MeasureTheory…
-/
protected theorem NullMeasurableSet.fundamentalInterior (hs : NullMeasurableSet s μ) :
    NullMeasurableSet (fundamentalInterior G s) μ :=
  hs.diff <| .iUnion fun _ => .iUnion fun _ => hs.smul _

end MeasurableSpace

namespace IsFundamentalDomain

variable [Countable G] [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α} {s : Set α}
  (hs : IsFundamentalDomain G s μ)
include hs

section Group


@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalFrontier]
/-
**MeasureTheory.IsFundamentalDomain.measure_fundamentalFrontier** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：measure_fundamentalFrontier : μ (fundamentalFrontier G s) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.iUnion₂_inter`：iUnion₂_inter (s : forall i, κ i -> Set α) (t : Set α
) : (⋃ (i) (j), s i j) inter t = ⋃ (i) (j), s i j inter t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.IsFundamentalDomain.aedisjoint`：∀ {G : Type u_1} {α : Type
 u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s : Set α
}   {μ : autoParam (MeasureTheory.…
-/
theorem measure_fundamentalFrontier : μ (fundamentalFrontier G s) = 0 := by
  simpa only [fundamentalFrontier, iUnion₂_inter, one_smul, measure_iUnion_null_iff, inter_comm s,
    Function.onFun] using! fun g (hg : g ≠ 1) => hs.aedisjoint hg

@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalInterior]
/-
**MeasureTheory.IsFundamentalDomain.measure_fundamentalInterior** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：measure_fundamentalInterior : μ (fundamentalInterior G s) = μ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_sdiff_null'`：measure_sdiff_null' (h : μ (s₁ inter 
s₂) = 0) : μ (s₁ \ s₂) = μ s₁
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_fundamentalFrontier`：measure_f
undamentalFrontier : μ (fundamentalFrontier G s) = 0
-/
theorem measure_fundamentalInterior : μ (fundamentalInterior G s) = μ s :=
  measure_sdiff_null' hs.measure_fundamentalFrontier

end Group

variable [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]

/-
**MeasureTheory.IsFundamentalDomain.fundamentalInterior** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [Countable G] [inst : Group G] [inst_1 : M
ulAction G α] [inst_2 : MeasurableSpace α]   {μ : MeasureTheory.Measure α} {s : 
Set α},   MeasureTheory.IsFundamentalDomain G s μ →     ∀ [MeasurableConstSMul G
 α] [MeasureTheory.SMulInvariantMeasure G α μ],       MeasureTheory.IsFundamenta
lDomain G (MeasureTheory.fundamentalInterior G s) μ
参数：MeasureTheory.fundamentalInterior G s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.fundamentalInterior`：∀ (G : Type u_1) {α
 : Type u_3} [inst : Group G] [inst_1 : MulAction G α] (s : Set α) [Countable G]
   [inst_3 : MeasurableSpace α] [Measurab…
· 使用定理 `MeasureTheory.IsFundamentalDomain.nullMeasurableSet`：∀ {G : Type u_1} {α
 : Type u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s 
: Set α}   {μ : autoParam (MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.smul_set_union`：smul_set_union : a • (t₁ union t₂) = a • t₁ union a 
• t₂
· 使用定理 `MeasureTheory.fundamentalFrontier_union_fundamentalInterior`：fundamental
Frontier_union_fundamentalInterior : fundamentalFrontier G s union fundamentalIn
terior G s = s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iUnion_inv_smul`：iUnion_inv_smul : ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s
· 使用定理 `Set.iUnion_smul_eq_ofPred_exists`：iUnion_smul_eq_ofPred_exists {s : Set 
β} : ⋃ g : α, g • s = { a | exists g : α, g • a in s }
· 使用定理 `Set.compl_sdiff`：compl_sdiff : (t \ s)ᶜ = s union tᶜ
· 使用定理 `MeasureTheory.measure_union_null`：measure_union_null (hs : μ s = 0) (ht 
: μ t = 0) : μ (s union t) = 0
· 使用定理 `MeasureTheory.measure_iUnion_null`：∀ {α : Type u_1} {F : Type u_3} [inst
 : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass F α] {μ : F}   {ι
 : Sort u_4} [Countable…
· 使用定理 `MeasureTheory.measure_smul_null`：measure_smul_null {s} (h : μ s = 0) (c 
: G) : μ (c • s) = 0
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_fundamentalFrontier`：measure_f
undamentalFrontier : μ (fundamentalFrontier G s) = 0
· 使用定理 `MeasureTheory.IsFundamentalDomain.ae_covers`：∀ {G : Type u_1} {α : Type 
u_2} [inst : One G] [inst_1 : SMul G α] [inst_2 : MeasurableSpace α] {s : Set α}
   {μ : autoParam (MeasureTheory.…
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `MeasureTheory.pairwise_disjoint_fundamentalInterior`：pairwise_disjoint_f
undamentalInterior : Pairwise (Disjoint on fun g : G => g • fundamentalInterior 
G s)
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
-/
protected theorem fundamentalInterior : IsFundamentalDomain G (fundamentalInterior G s) μ where
  nullMeasurableSet := hs.nullMeasurableSet.fundamentalInterior _ _
  ae_covers := by
    simp_rw [ae_iff, not_exists, ← mem_inv_smul_set_iff, ofPred_forall, ← compl_ofPred,
      ofPred_mem_eq, ← compl_iUnion]
    have :
      ((⋃ g : G, g⁻¹ • s) \ ⋃ g : G, g⁻¹ • fundamentalFrontier G s) ⊆
        ⋃ g : G, g⁻¹ • fundamentalInterior G s := by
      simp_rw [sdiff_subset_iff, ← iUnion_union_distrib, ← smul_set_union (α := G) (β := α),
        fundamentalFrontier_union_fundamentalInterior]; rfl
    refine eq_bot_mono (μ.mono <| compl_subset_compl.2 this) ?_
    simp only [iUnion_inv_smul, compl_sdiff, ENNReal.bot_eq_zero,
      @iUnion_smul_eq_ofPred_exists _ _ _ _ s]
    exact measure_union_null
      (measure_iUnion_null fun _ => measure_smul_null hs.measure_fundamentalFrontier _) hs.ae_covers
  aedisjoint := (pairwise_disjoint_fundamentalInterior _ _).mono fun _ _ => Disjoint.aedisjoint

end IsFundamentalDomain

section FundamentalDomainMeasure

variable (G) [Group G] [MulAction G α] [MeasurableSpace α]
  (μ : Measure α)

local notation "α_mod_G" => MulAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

variable {G}

@[to_additive addMeasure_map_restrict_apply]
/-
**MeasureTheory.measure_map_restrict_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measure_map_restrict_apply (s : Set α) {U : Set (Quotient α_mod_G)} (meas_
U : MeasurableSet U) : (μ.restrict s).map π U = μ ((π ⁻¹' U) inter s)
参数：s : Set α；Quotient α_mod_G；meas_U : MeasurableSet U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `measurableSet_quotient`：measurableSet_quotient {s : Setoid α} {t : Set (
Quotient s)} : MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t)
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
-/
lemma measure_map_restrict_apply (s : Set α) {U : Set (Quotient α_mod_G)}
    (meas_U : MeasurableSet U) :
    (μ.restrict s).map π U = μ ((π ⁻¹' U) ∩ s) := by
  rw [map_apply (f := π) (fun V hV ↦ measurableSet_quotient.mp hV) meas_U,
    Measure.restrict_apply (t := (Quotient.mk α_mod_G ⁻¹' U)) (measurableSet_quotient.mp meas_U)]

@[to_additive]
/-
**MeasureTheory.IsFundamentalDomain.quotientMeasure_eq** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   (μ : MeasureTheory.Measure α) [Countable G] {s t 
: Set α} [MeasureTheory.SMulInvariantMeasure G α μ]   [MeasurableConstSMul G α],
   MeasureTheory.IsFundamentalDomain G s μ →     MeasureTheory.IsFundamentalDoma
in G t μ →       MeasureTheory.Measure.map (Quotient.mk (MulAction.orbitRel G α)
) (μ.restrict s) =         MeasureTheory.Measure.map (Quotient.mk (MulAction.orb
itRel G α)) (μ.restrict t)
参数：μ : MeasureTheory.Measure α；Quotient.mk (MulAction.orbitRel G α)；μ.restrict s
；Quotient.mk (MulAction.orbitRel G α)；μ.restrict t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.measure_map_restrict_apply`：measure_map_restrict_apply (s 
: Set α) {U : Set (Quotient α_mod_G)} (meas_U : MeasurableSet U) : (μ.restrict s
).map π U = μ ((π ⁻¹' U) inter…
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_set_eq`：measure_set_eq (hs : I
sFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) {A : Set α} (hA₀ : Me
asurableSet A) (hA : forall g : G, (fu…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `measurableSet_quotient`：measurableSet_quotient {s : Setoid α} {t : Set (
Quotient s)} : MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsFundamentalDomain.quotientMeasure_eq [Countable G] {s t : Set α}
    [SMulInvariantMeasure G α μ] [MeasurableConstSMul G α] (fund_dom_s : IsFundamentalDomain G s μ)
    (fund_dom_t : IsFundamentalDomain G t μ) :
    (μ.restrict s).map π = (μ.restrict t).map π := by
  ext U meas_U
  rw [measure_map_restrict_apply (meas_U := meas_U), measure_map_restrict_apply (meas_U := meas_U)]
  apply MeasureTheory.IsFundamentalDomain.measure_set_eq fund_dom_s fund_dom_t
  · exact measurableSet_quotient.mp meas_U
  · intro g
    ext x
    have : Quotient.mk α_mod_G (g • x) = Quotient.mk α_mod_G x := by
      apply Quotient.sound
      use g
    simp only [mem_preimage, this]

end FundamentalDomainMeasure

/-! ## `HasFundamentalDomain` typeclass

We define `HasFundamentalDomain` in order to be able to define the `covolume` of a quotient of `α`
by a group `G`, which under reasonable conditions does not depend on the choice of fundamental
domain. Even though any "sensible" action should have a fundamental domain, this is a rather
delicate question which was recently addressed by Misha Kapovich: https://arxiv.org/abs/2301.05325

TODO: Formalize the existence of a Dirichlet domain as in Kapovich's paper.

-/

section HasFundamentalDomain

/-- We say a quotient of `α` by `G` `HasAddFundamentalDomain` if there is a measurable set
  `s` for which `IsAddFundamentalDomain G s` holds. -/
/-
**MeasureTheory.HasAddFundamentalDomain** 是 Mathlib 中的一个类，位于命名空间 `MeasureTheory`
。
形式化陈述：HasAddFundamentalDomain (G α : Type*) [Zero G] [VAdd G α] [MeasurableSpace
 α] (ν : Measure α
参数：G α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say a quotient of `α` by `G` `HasAddFundamentalDomain` if there is a measurab
le set
  `s` for which `IsAddFundamentalDomain G s` holds.
-/
class HasAddFundamentalDomain (G α : Type*) [Zero G] [VAdd G α] [MeasurableSpace α]
    (ν : Measure α := by volume_tac) : Prop where
  ExistsIsAddFundamentalDomain : ∃ s : Set α, IsAddFundamentalDomain G s ν

/-- We say a quotient of `α` by `G` `HasFundamentalDomain` if there is a measurable set `s` for
  which `IsFundamentalDomain G s` holds. -/
/-
**MeasureTheory.HasFundamentalDomain** 是 Mathlib 中的一个类，位于命名空间 `MeasureTheory`。
形式化陈述：HasFundamentalDomain (G : Type*) (α : Type*) [One G] [SMul G α] [Measurabl
eSpace α] (ν : Measure α
参数：G : Type*；α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say a quotient of `α` by `G` `HasFundamentalDomain` if there is a measurable 
set `s` for
  which `IsFundamentalDomain G s` holds.
-/
class HasFundamentalDomain (G : Type*) (α : Type*) [One G] [SMul G α] [MeasurableSpace α]
    (ν : Measure α := by volume_tac) : Prop where
  ExistsIsFundamentalDomain : ∃ (s : Set α), IsFundamentalDomain G s ν

attribute [to_additive existing] MeasureTheory.HasFundamentalDomain

open scoped Classical in
/-- The `covolume` of an action of `G` on `α` the volume of some fundamental domain, or `0` if
none exists. -/
@[to_additive addCovolume /-- The `addCovolume` of an action of `G` on `α` is the volume of some
fundamental domain, or `0` if none exists. -/]
/-
**MeasureTheory.covolume** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：covolume (G α : Type*) [One G] [SMul G α] [MeasurableSpace α] (ν : Measure
 α
参数：G α : Type*。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFundamentalDomain.ExistsIsFundamentalDomain`：∀ {G : Typ
e u_6} {α : Type u_7} {inst : One G} {inst_1 : SMul G α} {inst_2 : MeasurableSpa
ce α}   {ν : autoParam (MeasureTheory.Measure α) M…
-/
noncomputable def covolume (G α : Type*) [One G] [SMul G α] [MeasurableSpace α]
    (ν : Measure α := by volume_tac) : ℝ≥0∞ :=
  if funDom : HasFundamentalDomain G α ν then ν funDom.ExistsIsFundamentalDomain.choose else 0

variable [Group G] [MulAction G α] [MeasurableSpace α]

/-- If there is a fundamental domain `s`, then `HasFundamentalDomain` holds. -/
@[to_additive /-- If there is an additive fundamental domain `s`, then `HasAddFundamentalDomain`
holds. -/]
/-
**MeasureTheory.IsFundamentalDomain.hasFundamentalDomain** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   (ν : MeasureTheory.Measure α) {s : Set α},   Meas
ureTheory.IsFundamentalDomain G s ν → MeasureTheory.HasFundamentalDomain G α ν
参数：ν : MeasureTheory.Measure α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsFundamentalDomain.hasFundamentalDomain (ν : Measure α) {s : Set α}
    (fund_dom_s : IsFundamentalDomain G s ν) :
    HasFundamentalDomain G α ν := ⟨⟨s, fund_dom_s⟩⟩

/-- The `covolume` can be computed by taking the `volume` of any given fundamental domain `s`. -/
@[to_additive /-- The `addCovolume` can be computed by taking the `volume` of any given additive
fundamental domain `s`. -/]
/-
**MeasureTheory.IsFundamentalDomain.covolume_eq_volume** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   (ν : MeasureTheory.Measure α) [Countable G] [Meas
urableConstSMul G α] [MeasureTheory.SMulInvariantMeasure G α ν]   {s : Set α}, M
easureTheory.IsFundamentalDomain G s ν → MeasureTheory.covolume G α ν = ν s
参数：ν : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFundamentalDomain.ExistsIsFundamentalDomain`：∀ {G : Typ
e u_6} {α : Type u_7} {inst : One G} {inst_1 : SMul G α} {inst_2 : MeasurableSpa
ce α}   {ν : autoParam (MeasureTheory.Measure α) M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.IsFundamentalDomain.hasFundamentalDomain`：∀ {G : Type u_1}
 {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSp
ace α]   (ν : MeasureTheory.Measure α) {s : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_eq`：∀ {G : Type u_1} {α : Type
 u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpace α] {s 
t : Set α}   {μ : MeasureTheory.Me…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma IsFundamentalDomain.covolume_eq_volume (ν : Measure α) [Countable G]
    [MeasurableConstSMul G α] [SMulInvariantMeasure G α ν] {s : Set α}
    (fund_dom_s : IsFundamentalDomain G s ν) : covolume G α ν = ν s := by
  dsimp [covolume]
  simp only [(fund_dom_s.hasFundamentalDomain ν), ↓reduceDIte]
  rw [fund_dom_s.measure_eq]
  exact (fund_dom_s.hasFundamentalDomain ν).ExistsIsFundamentalDomain.choose_spec

end HasFundamentalDomain

/-! ## `QuotientMeasureEqMeasurePreimage` typeclass

This typeclass describes a situation in which a measure `μ` on `α ⧸ G` can be computed by
taking a measure `ν` on `α` of the intersection of the pullback with a fundamental domain.

It's curious that in measure theory, measures can be pushed forward, while in geometry, volumes can
be pulled back. And yet here, we are describing a situation involving measures in a geometric way.

Another viewpoint is that if a set is small enough to fit in a single fundamental domain, then its
`ν` measure in `α` is the same as the `μ` measure of its pushforward in `α ⧸ G`.

-/

section QuotientMeasureEqMeasurePreimage

section additive

variable [AddGroup G] [AddAction G α] [MeasurableSpace α]

local notation "α_mod_G" => AddAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

/-- A measure `μ` on the `AddQuotient` of `α` mod `G` satisfies
  `AddQuotientMeasureEqMeasurePreimage` if: for any fundamental domain `t`, and any measurable
  subset `U` of the quotient, `μ U = volume ((π ⁻¹' U) ∩ t)`. -/
/-
**MeasureTheory.AddQuotientMeasureEqMeasurePreimage** 是 Mathlib 中的一个类，位于命名空间 `Me
asureTheory`。
形式化陈述：AddQuotientMeasureEqMeasurePreimage (ν : Measure α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` on the `AddQuotient` of `α` mod `G` satisfies
  `AddQuotientMeasureEqMeasurePreimage` if: for any fundamental domain `t`, and 
any measurable
  subset `U` of the quotient, `μ U = volume ((π ⁻¹' U) ∩ t)`.
-/
class AddQuotientMeasureEqMeasurePreimage (ν : Measure α := by volume_tac)
    (μ : Measure (Quotient α_mod_G)) : Prop where
  addProjection_respects_measure' : ∀ (t : Set α) (_ : IsAddFundamentalDomain G t ν),
    μ = (ν.restrict t).map π

end additive

variable [Group G] [MulAction G α] [MeasurableSpace α]

local notation "α_mod_G" => MulAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

/-- Measures `ν` on `α` and `μ` on the `Quotient` of `α` mod `G` satisfy
  `QuotientMeasureEqMeasurePreimage` if: for any fundamental domain `t`, and any measurable subset
  `U` of the quotient, `μ U = ν ((π ⁻¹' U) ∩ t)`. -/
/-
**MeasureTheory.QuotientMeasureEqMeasurePreimage** 是 Mathlib 中的一个类，位于命名空间 `Measu
reTheory`。
形式化陈述：QuotientMeasureEqMeasurePreimage (ν : Measure α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Measures `ν` on `α` and `μ` on the `Quotient` of `α` mod `G` satisfy
  `QuotientMeasureEqMeasurePreimage` if: for any fundamental domain `t`, and any
 measurable subset
  `U` of the quotient, `μ U = ν ((π ⁻¹' U) ∩ t)`.
-/
class QuotientMeasureEqMeasurePreimage (ν : Measure α := by volume_tac)
    (μ : Measure (Quotient α_mod_G)) : Prop where
  projection_respects_measure' (t : Set α) : IsFundamentalDomain G t ν → μ = (ν.restrict t).map π

attribute [to_additive]
  MeasureTheory.QuotientMeasureEqMeasurePreimage

@[to_additive addProjection_respects_measure]
/-
**MeasureTheory.IsFundamentalDomain.projection_respects_measure** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} (μ : MeasureTheory.
Measure (Quotient (MulAction.orbitRel G α)))   [i : MeasureTheory.QuotientMeasur
eEqMeasurePreimage ν μ] {t : Set α},   MeasureTheory.IsFundamentalDomain G t ν →
     μ = MeasureTheory.Measure.map (Quotient.mk (MulAction.orbitRel G α)) (ν.res
trict t)
参数：μ : MeasureTheory.Measure (Quotient (MulAction.orbitRel G α))；Quotient.mk (Mu
lAction.orbitRel G α)；ν.restrict t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.QuotientMeasureEqMeasurePreimage.projection_respects_measu
re'`：∀ {G : Type u_1} {α : Type u_3} {inst : Group G} {inst_1 : MulAction G α} {
inst_2 : MeasurableSpace α}   {ν : autoParam (MeasureTheory.Measu…
-/
lemma IsFundamentalDomain.projection_respects_measure {ν : Measure α}
    (μ : Measure (Quotient α_mod_G)) [i : QuotientMeasureEqMeasurePreimage ν μ] {t : Set α}
    (fund_dom_t : IsFundamentalDomain G t ν) : μ = (ν.restrict t).map π :=
  i.projection_respects_measure' t fund_dom_t

@[to_additive addProjection_respects_measure_apply]
/-
**MeasureTheory.IsFundamentalDomain.projection_respects_measure_apply** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} (μ : MeasureTheory.
Measure (Quotient (MulAction.orbitRel G α)))   [i : MeasureTheory.QuotientMeasur
eEqMeasurePreimage ν μ] {t : Set α},   MeasureTheory.IsFundamentalDomain G t ν →
     ∀ {U : Set (Quotient (MulAction.orbitRel G α))},       MeasurableSet U → μ 
U = ν (Quotient.mk (MulAction.orbitRel G α) ⁻¹' U ∩ t)
参数：μ : MeasureTheory.Measure (Quotient (MulAction.orbitRel G α))；Quotient (MulAc
tion.orbitRel G α)；Quotient.mk (MulAction.orbitRel G α) ⁻¹' U ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.projection_respects_measure`：∀ {G : Ty
pe u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : Measu
rableSpace α]   {ν : MeasureTheory.Measure α} (μ : …
· 使用引理 `MeasureTheory.measure_map_restrict_apply`：measure_map_restrict_apply (s 
: Set α) {U : Set (Quotient α_mod_G)} (meas_U : MeasurableSet U) : (μ.restrict s
).map π U = μ ((π ⁻¹' U) inter…
-/
lemma IsFundamentalDomain.projection_respects_measure_apply {ν : Measure α}
    (μ : Measure (Quotient α_mod_G)) [i : QuotientMeasureEqMeasurePreimage ν μ] {t : Set α}
    (fund_dom_t : IsFundamentalDomain G t ν) {U : Set (Quotient α_mod_G)}
    (meas_U : MeasurableSet U) : μ U = ν (π ⁻¹' U ∩ t) := by
  rw [fund_dom_t.projection_respects_measure (μ := μ), measure_map_restrict_apply ν t meas_U]

variable {ν : Measure α}

/-- Any two measures satisfying `QuotientMeasureEqMeasurePreimage` are equal. -/
@[to_additive /-- Any two measures satisfying `AddQuotientMeasureEqMeasurePreimage` are equal. -/]
/-
**MeasureTheory.QuotientMeasureEqMeasurePreimage.unique** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.QuotientMeasureEqMeasurePreimage`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} [hasFun : MeasureTh
eory.HasFundamentalDomain G α ν]   (μ μ' : MeasureTheory.Measure (Quotient (MulA
ction.orbitRel G α)))   [MeasureTheory.QuotientMeasureEqMeasurePreimage ν μ] [Me
asureTheory.QuotientMeasureEqMeasurePreimage ν μ'], μ = μ'
参数：μ μ' : MeasureTheory.Measure (Quotient (MulAction.orbitRel G α))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFundamentalDomain.ExistsIsFundamentalDomain`：∀ {G : Typ
e u_6} {α : Type u_7} {inst : One G} {inst_1 : SMul G α} {inst_2 : MeasurableSpa
ce α}   {ν : autoParam (MeasureTheory.Measure α) M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.projection_respects_measure`：∀ {G : Ty
pe u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : Measu
rableSpace α]   {ν : MeasureTheory.Measure α} (μ : …

--- 原说明 ---
Any two measures satisfying `QuotientMeasureEqMeasurePreimage` are equal.
-/
lemma QuotientMeasureEqMeasurePreimage.unique
    [hasFun : HasFundamentalDomain G α ν] (μ μ' : Measure (Quotient α_mod_G))
    [QuotientMeasureEqMeasurePreimage ν μ] [QuotientMeasureEqMeasurePreimage ν μ'] :
    μ = μ' := by
  obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
  rw [h𝓕.projection_respects_measure (μ := μ), h𝓕.projection_respects_measure (μ := μ')]

/-- The quotient map to `α ⧸ G` is measure-preserving between the restriction of `volume` to a
  fundamental domain in `α` and a related measure satisfying `QuotientMeasureEqMeasurePreimage`. -/
@[to_additive IsAddFundamentalDomain.measurePreserving_add_quotient_mk /-- The quotient map to
the additive quotient of `α` by `G` is measure-preserving between the restriction of `volume` to
an additive fundamental domain in `α` and a related measure satisfying
`AddQuotientMeasureEqMeasurePreimage`. -/]
/-
**MeasureTheory.IsFundamentalDomain.measurePreserving_quotient_mk** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} {𝓕 : Set α},   Meas
ureTheory.IsFundamentalDomain G 𝓕 ν →     ∀ (μ : MeasureTheory.Measure (Quotient
 (MulAction.orbitRel G α)))       [MeasureTheory.QuotientMeasureEqMeasurePreimag
e ν μ],       MeasureTheory.MeasurePreserving (Quotient.mk (MulAction.orbitRel G
 α)) (ν.restrict 𝓕) μ
参数：μ : MeasureTheory.Measure (Quotient (MulAction.orbitRel G α))；Quotient.mk (Mu
lAction.orbitRel G α)；ν.restrict 𝓕。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_quotient_mk'`：measurable_quotient_mk' [s : Setoid α] : Measur
able (Quotient.mk' : α -> Quotient s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.projection_respects_measure`：∀ {G : Ty
pe u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : Measu
rableSpace α]   {ν : MeasureTheory.Measure α} (μ : …
-/
theorem IsFundamentalDomain.measurePreserving_quotient_mk
    {𝓕 : Set α} (h𝓕 : IsFundamentalDomain G 𝓕 ν)
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ] :
    MeasurePreserving π (ν.restrict 𝓕) μ where
  measurable := measurable_quotient_mk' (s := α_mod_G)
  map_eq := by
    have : HasFundamentalDomain G α ν := ⟨𝓕, h𝓕⟩
    rw [h𝓕.projection_respects_measure (μ := μ)]

variable [SMulInvariantMeasure G α ν] [Countable G] [MeasurableConstSMul G α]

/-- Given a measure upstairs (i.e., on `α`), and a choice `s` of fundamental domain, there's always
an artificial way to generate a measure downstairs such that the pair satisfies the
`QuotientMeasureEqMeasurePreimage` typeclass. -/
@[to_additive /-- Given a measure upstairs (i.e., on `α`), and a choice `s` of additive
fundamental domain, there's always an artificial way to generate a measure downstairs such that
the pair satisfies the `AddQuotientMeasureEqMeasurePreimage` typeclass. -/]
/-
**MeasureTheory.IsFundamentalDomain.quotientMeasureEqMeasurePreimage_quotientMea
sure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} [MeasureTheory.SMul
InvariantMeasure G α ν] [Countable G] [MeasurableConstSMul G α]   {s : Set α},  
 MeasureTheory.IsFundamentalDomain G s ν →     MeasureTheory.QuotientMeasureEqMe
asurePreimage ν       (MeasureTheory.Measure.map (Quotient.mk (MulAction.orbitRe
l G α)) (ν.restrict s))
参数：MeasureTheory.Measure.map (Quotient.mk (MulAction.orbitRel G α)) (ν.restrict 
s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.quotientMeasure_eq`：∀ {G : Type u_1} {
α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpac
e α]   (μ : MeasureTheory.Measure α) [Coun…
-/
lemma IsFundamentalDomain.quotientMeasureEqMeasurePreimage_quotientMeasure
    {s : Set α} (fund_dom_s : IsFundamentalDomain G s ν) :
    QuotientMeasureEqMeasurePreimage ν ((ν.restrict s).map π) where
  projection_respects_measure' t fund_dom_t := by rw [fund_dom_s.quotientMeasure_eq _ fund_dom_t]

/-- One can prove `QuotientMeasureEqMeasurePreimage` by checking behavior with respect to a single
fundamental domain. -/
@[to_additive /-- One can prove `AddQuotientMeasureEqMeasurePreimage` by checking behavior with
respect to a single additive fundamental domain. -/]
/-
**MeasureTheory.IsFundamentalDomain.quotientMeasureEqMeasurePreimage** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} [MeasureTheory.SMul
InvariantMeasure G α ν] [Countable G] [MeasurableConstSMul G α]   {μ : MeasureTh
eory.Measure (Quotient (MulAction.orbitRel G α))} {s : Set α},   MeasureTheory.I
sFundamentalDomain G s ν →     μ = MeasureTheory.Measure.map (Quotient.mk (MulAc
tion.orbitRel G α)) (ν.restrict s) →       MeasureTheory.QuotientMeasureEqMeasur
ePreimage ν μ
参数：Quotient (MulAction.orbitRel G α)；Quotient.mk (MulAction.orbitRel G α)；ν.rest
rict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.quotientMeasureEqMeasurePreimage_quoti
entMeasure`：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction
 G α] [inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} [Meas…
-/
lemma IsFundamentalDomain.quotientMeasureEqMeasurePreimage {μ : Measure (Quotient α_mod_G)}
    {s : Set α} (fund_dom_s : IsFundamentalDomain G s ν) (h : μ = (ν.restrict s).map π) :
    QuotientMeasureEqMeasurePreimage ν μ := by
  simpa [h] using fund_dom_s.quotientMeasureEqMeasurePreimage_quotientMeasure


/-- If a fundamental domain has volume 0, then `QuotientMeasureEqMeasurePreimage` holds. -/
@[to_additive /-- If an additive fundamental domain has volume 0, then
`AddQuotientMeasureEqMeasurePreimage` holds. -/]
/-
**MeasureTheory.IsFundamentalDomain.quotientMeasureEqMeasurePreimage_of_zero** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.IsFundamentalDomain`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} [MeasureTheory.SMul
InvariantMeasure G α ν] [Countable G] [MeasurableConstSMul G α]   {s : Set α}, M
easureTheory.IsFundamentalDomain G s ν → ν s = 0 → MeasureTheory.QuotientMeasure
EqMeasurePreimage ν 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.quotientMeasureEqMeasurePreimage`：∀ {G
 : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : 
MeasurableSpace α]   {ν : MeasureTheory.Measure α} [Meas…
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.measure_map_restrict_apply`：measure_map_restrict_apply (s 
: Set α) {U : Set (Quotient α_mod_G)} (meas_U : MeasurableSet U) : (μ.restrict s
).map π U = μ ((π ⁻¹' U) inter…
· 使用定理 `MeasureTheory.measure_inter_null_of_null_right`：measure_inter_null_of_nu
ll_right (S : Set α) {T : Set α} (h : μ T = 0) : μ (S inter T) = 0
-/
theorem IsFundamentalDomain.quotientMeasureEqMeasurePreimage_of_zero
    {s : Set α} (fund_dom_s : IsFundamentalDomain G s ν)
    (vol_s : ν s = 0) :
    QuotientMeasureEqMeasurePreimage ν (0 : Measure (Quotient α_mod_G)) := by
  apply fund_dom_s.quotientMeasureEqMeasurePreimage
  ext U meas_U
  simp only [Measure.coe_zero, Pi.zero_apply]
  convert! (measure_inter_null_of_null_right (h := vol_s) (Quotient.mk α_mod_G ⁻¹' U)).symm
  rw [measure_map_restrict_apply (meas_U := meas_U)]

/-- If a measure `μ` on a quotient satisfies `QuotientMeasureEqMeasurePreimage` with respect to a
sigma-finite measure `ν`, then it is itself `SigmaFinite`. -/
@[to_additive /-- If a measure `μ` on a quotient satisfies `AddQuotientMeasureEqMeasurePreimage`
with respect to a sigma-finite measure `ν`, then it is itself `SigmaFinite`. -/]
/-
**MeasureTheory.QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.QuotientMeasureEqMeasurePreimage`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} [MeasureTheory.SMul
InvariantMeasure G α ν] [Countable G] [MeasurableConstSMul G α]   [i : MeasureTh
eory.SigmaFinite ν] [i' : MeasureTheory.HasFundamentalDomain G α ν]   (μ : Measu
reTheory.Measure (Quotient (MulAction.orbitRel G α))) [MeasureTheory.QuotientMea
sureEqMeasurePreimage ν μ],   MeasureTheory.SigmaFinite μ
参数：μ : MeasureTheory.Measure (Quotient (MulAction.orbitRel G α))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.sigmaFinite_iff`：sigmaFinite_iff : SigmaFinite μ ↔ Nonempt
y (μ.FiniteSpanningSetsIn univ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MulAction.quotient_preimage_image_eq_union_mul`：quotient_preimage_image_
eq_union_mul (U : Set α) : letI
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `measurableSet_quotient`：measurableSet_quotient {s : Setoid α} {t : Set (
Quotient s)} : MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t)
· 使用定理 `Quotient.mk''_eq_mk`：∀ {α : Sort u_1} {s : Setoid α}, Quotient.mk'' = Qu
otient.mk s
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `MeasurableSet.const_smul`：MeasurableSet.const_smul {G α : Type*} [Group 
G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α] {s : Set α} (hs
 : MeasurableS…
· 使用定理 `MeasureTheory.IsFundamentalDomain.projection_respects_measure_apply`：∀ {
G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 :
 MeasurableSpace α]   {ν : MeasureTheory.Measure α} (μ : …
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_eq_tsum`：measure_eq_tsum (h : 
IsFundamentalDomain G s μ) (t : Set α) : μ t = ∑' g : G, μ (g • t inter s)
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Quotient.mk'_surjective`：∀ {α : Sort u_1} [s : Setoid α], Function.Surje
ctive Quotient.mk'
-/
lemma QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient
    [i : SigmaFinite ν] [i' : HasFundamentalDomain G α ν]
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ] :
    SigmaFinite μ := by
  rw [sigmaFinite_iff]
  obtain ⟨A, hA_meas, hA, hA'⟩ := Measure.toFiniteSpanningSetsIn (h := i)
  simp only [mem_ofPred_eq] at hA_meas
  refine ⟨⟨fun n ↦ π '' (A n), by simp, fun n ↦ ?_, ?_⟩⟩
  · obtain ⟨s, fund_dom_s⟩ := i'
    have : π ⁻¹' π '' (A n) = _ := MulAction.quotient_preimage_image_eq_union_mul (A n) (G := G)
    have measπAn : MeasurableSet (π '' A n) := by
      rw [measurableSet_quotient, Quotient.mk''_eq_mk, this]
      apply MeasurableSet.iUnion
      exact fun g ↦ MeasurableSet.const_smul (hA_meas n) g
    rw [fund_dom_s.projection_respects_measure_apply (μ := μ) measπAn, this, iUnion_inter]
    refine lt_of_le_of_lt ?_ (hA n)
    rw [fund_dom_s.measure_eq_tsum (A n)]
    exact measure_iUnion_le _
  · rw [← image_iUnion, hA']
    refine image_univ_of_surjective (by convert! Quotient.mk'_surjective)

/-- A measure `μ` on `α ⧸ G` satisfying `QuotientMeasureEqMeasurePreimage` and having finite
covolume is a finite measure. -/
@[to_additive /-- A measure `μ` on the additive quotient of `α` by `G` satisfying
`AddQuotientMeasureEqMeasurePreimage` and having finite covolume is a finite measure. -/]
/-
**MeasureTheory.QuotientMeasureEqMeasurePreimage.isFiniteMeasure_quotient** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.QuotientMeasureEqMeasurePreimage`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} [MeasureTheory.SMul
InvariantMeasure G α ν] [Countable G] [MeasurableConstSMul G α]   (μ : MeasureTh
eory.Measure (Quotient (MulAction.orbitRel G α))) [MeasureTheory.QuotientMeasure
EqMeasurePreimage ν μ]   [hasFun : MeasureTheory.HasFundamentalDomain G α ν],   
MeasureTheory.covolume G α ν ≠ ⊤ → MeasureTheory.IsFiniteMeasure μ
参数：μ : MeasureTheory.Measure (Quotient (MulAction.orbitRel G α))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFundamentalDomain.ExistsIsFundamentalDomain`：∀ {G : Typ
e u_6} {α : Type u_7} {inst : One G} {inst_1 : SMul G α} {inst_2 : MeasurableSpa
ce α}   {ν : autoParam (MeasureTheory.Measure α) M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.projection_respects_measure`：∀ {G : Ty
pe u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : Measu
rableSpace α]   {ν : MeasureTheory.Measure α} (μ : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsFundamentalDomain.covolume_eq_volume`：∀ {G : Type u_1} {
α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpac
e α]   (ν : MeasureTheory.Measure α) [Coun…
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
-/
theorem QuotientMeasureEqMeasurePreimage.isFiniteMeasure_quotient
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ]
    [hasFun : HasFundamentalDomain G α ν] (h : covolume G α ν ≠ ∞) :
    IsFiniteMeasure μ := by
  obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
  rw [h𝓕.projection_respects_measure (μ := μ)]
  have : Fact (ν 𝓕 < ∞) := by
    apply Fact.mk
    convert! Ne.lt_top h
    exact (h𝓕.covolume_eq_volume ν).symm
  infer_instance

/-- A finite measure `μ` on `α ⧸ G` satisfying `QuotientMeasureEqMeasurePreimage` has finite
covolume. -/
@[to_additive /-- A finite measure `μ` on the additive quotient of `α` by `G` satisfying
`AddQuotientMeasureEqMeasurePreimage` has finite covolume. -/]
/-
**MeasureTheory.QuotientMeasureEqMeasurePreimage.covolume_ne_top** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.QuotientMeasureEqMeasurePreimage`。
形式化陈述：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} [MeasureTheory.SMul
InvariantMeasure G α ν] [Countable G] [MeasurableConstSMul G α]   (μ : MeasureTh
eory.Measure (Quotient (MulAction.orbitRel G α))) [MeasureTheory.QuotientMeasure
EqMeasurePreimage ν μ]   [MeasureTheory.IsFiniteMeasure μ], MeasureTheory.covolu
me G α ν < ⊤
参数：μ : MeasureTheory.Measure (Quotient (MulAction.orbitRel G α))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFundamentalDomain.ExistsIsFundamentalDomain`：∀ {G : Typ
e u_6} {α : Type u_7} {inst : One G} {inst_1 : SMul G α} {inst_2 : MeasurableSpa
ce α}   {ν : autoParam (MeasureTheory.Measure α) M…
· 使用定理 `MeasureTheory.IsFiniteMeasure.measure_univ_lt_top`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsFinit
eMeasure μ],   μ Set.univ < ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.covolume_eq_volume`：∀ {G : Type u_1} {
α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpac
e α]   (ν : MeasureTheory.Measure α) [Coun…
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.IsFundamentalDomain.projection_respects_measure_apply`：∀ {
G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 :
 MeasurableSpace α]   {ν : MeasureTheory.Measure α} (μ : …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem QuotientMeasureEqMeasurePreimage.covolume_ne_top
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ] [IsFiniteMeasure μ] :
    covolume G α ν < ∞ := by
  by_cases hasFun : HasFundamentalDomain G α ν
  · obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
    have H : μ univ < ∞ := IsFiniteMeasure.measure_univ_lt_top
    rw [h𝓕.projection_respects_measure_apply (μ := μ) MeasurableSet.univ] at H
    simpa [h𝓕.covolume_eq_volume ν] using H
  · simp [covolume, hasFun]

end QuotientMeasureEqMeasurePreimage

section QuotientMeasureEqMeasurePreimage


variable [Group G] [MulAction G α] [MeasureSpace α] [Countable G]
  [SMulInvariantMeasure G α volume] [MeasurableConstSMul G α]

local notation "α_mod_G" => MulAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

/-- If a measure `μ` on a quotient satisfies `QuotientMeasureEqMeasurePreimage` with respect to a
sigma-finite measure, then it is itself `SigmaFinite`. -/
@[to_additive MeasureTheory.instSigmaFiniteAddQuotientOrbitRelInstMeasurableSpaceToMeasurableSpace
/-- If a measure `μ` on a quotient satisfies `AddQuotientMeasureEqMeasurePreimage` with respect to a
sigma-finite measure, then it is itself `SigmaFinite`. -/]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SigmaFinite (volume : Measure α)] [HasFundamentalDomain G α]
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage volume μ] :
    SigmaFinite μ :=
  QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient (ν := (volume : Measure α)) (μ := μ)

end QuotientMeasureEqMeasurePreimage

end MeasureTheory

