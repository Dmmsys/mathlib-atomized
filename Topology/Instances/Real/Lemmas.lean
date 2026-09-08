/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Algebra.Ring.Real

import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Topological properties of ℝ
-/

public section

assert_not_exists UniformOnFun

noncomputable section

open Filter Int Metric Set TopologicalSpace Bornology
open scoped Topology Uniformity Interval

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-
**Real.isTopologicalBasis_Ioo_rat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.isTopologicalBasis_Ioo_rat : @IsTopologicalBasis Real _ (⋃ (a : Rat) 
(b : Rat) (_ : a < b), {Ioo (a : Real) b})
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff_exists_Ioo_subset`：mem_nhds_iff_exists_Ioo_subset [NoMaxOrd
er α] [NoMinOrder α] {a : α} {s : Set α} : s in 𝓝 a ↔ exists l u, a in Ioo l u ∧
 Ioo l u subseteq s
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `Rat.cast_lt`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p < ↑q ↔ p < q
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem Real.isTopologicalBasis_Ioo_rat :
    @IsTopologicalBasis ℝ _ (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) b}) :=
  isTopologicalBasis_of_isOpen_of_nhds (by simp +contextual [isOpen_Ioo])
    fun a _ hav hv =>
    let ⟨_, _, ⟨hl, hu⟩, h⟩ := mem_nhds_iff_exists_Ioo_subset.mp (IsOpen.mem_nhds hv hav)
    let ⟨q, hlq, hqa⟩ := exists_rat_btwn hl
    let ⟨p, hap, hpu⟩ := exists_rat_btwn hu
    ⟨Ioo q p, by
      simp only [mem_iUnion]
      exact ⟨q, p, Rat.cast_lt.1 <| hqa.trans hap, rfl⟩, ⟨hqa, hap⟩, fun _ ⟨hqa', ha'p⟩ =>
      h ⟨hlq.trans hqa', ha'p.trans hpu⟩⟩

/- TODO(Mario): Prove that these are uniform isomorphisms instead of uniform embeddings
lemma uniform_embedding_add_rat {r : ℚ} : uniform_embedding (fun p : ℚ => p + r) :=
_

lemma uniform_embedding_mul_rat {q : ℚ} (hq : q ≠ 0) : uniform_embedding ((*) q) :=
_ -/
/-
**Real.mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.mem_closure_iff {s : Set Real} {x : Real} : x in closure s ↔ forall ε
 > 0, exists y in s, |y - x| < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhds_basis`：mem_closure_iff_nhds_basis {p : ι -> Prop} {
s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> exi
sts y in t, y in…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
TODO(Mario): Prove that these are uniform isomorphisms instead of uniform embedd
ings
lemma uniform_embedding_add_rat {r : ℚ} : uniform_embedding (fun p : ℚ => p + r)
 :=
_

lemma uniform_embedding_mul_rat {q : ℚ} (hq : q ≠ 0) : uniform_embedding ((*) q)
 :=
_
-/
theorem Real.mem_closure_iff {s : Set ℝ} {x : ℝ} :
    x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, |y - x| < ε := by
  simp [mem_closure_iff_nhds_basis nhds_basis_ball, Real.dist_eq]
/-
**Real.uniformContinuous_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.uniformContinuous_inv (s : Set Real) {r : Real} (r0 : 0 < r) (H : for
all x in s, r <= |x|) : UniformContinuous fun p : s => p.1⁻¹
参数：s : Set Real；r0 : 0 < r；H : forall x in s, r <= |x|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.uniformContinuous_iff`：uniformContinuous_iff [PseudoMetricSpace β
] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b :
 α⦄, dist a b < δ …
· 使用定理 `rat_inv_continuous_lemma`：rat_inv_continuous_lemma {β : Type*} [Division
Ring β] (abv : β -> α) [IsAbsoluteValue abv] {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K)
 : exists δ > …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Real.uniformContinuous_inv (s : Set ℝ) {r : ℝ} (r0 : 0 < r) (H : ∀ x ∈ s, r ≤ |x|) :
    UniformContinuous fun p : s => p.1⁻¹ :=
  Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0
    ⟨δ, δ0, fun {a b} h => Hδ (H _ a.2) (H _ b.2) h⟩
/-
**Real.uniformContinuous_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.uniformContinuous_abs : UniformContinuous (abs : Real -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.uniformContinuous_iff`：uniformContinuous_iff [PseudoMetricSpace β
] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b :
 α⦄, dist a b < δ …
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `abs_abs_sub_abs_le_abs_sub`：∀ {G : Type u_1} [inst : AddCommGroup G] [in
st_1 : LinearOrder G] [IsOrderedAddMonoid G] (a b : G),   ||a| - |b|| ≤ |a - b|
-/
theorem Real.uniformContinuous_abs : UniformContinuous (abs : ℝ → ℝ) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun _ _ ↦ lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _)⟩
/-
**Real.continuous_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.continuous_inv : Continuous fun a : { r : Real // r != 0 } => a.val⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `continuousOn_inv₀`：continuousOn_inv₀ : ContinuousOn (Inv.inv : G₀ -> G₀)
 {0}ᶜ
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
-/
theorem Real.continuous_inv : Continuous fun a : { r : ℝ // r ≠ 0 } => a.val⁻¹ :=
  continuousOn_inv₀.domRestrict
/-
**Real.uniformContinuous_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.uniformContinuous_mul (s : Set (Real × Real)) {r₁ r₂ : Real} (H : for
all x in s, |(x : Real × Real).1| < r₁ ∧ |x.2| < r₂) : UniformContinuous fun p :
 s => p.1.1 * p.1.2
参数：s : Set (Real × Real)；H : forall x in s, |(x : Real × Real).1| < r₁ ∧ |x.2| <
 r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.uniformContinuous_iff`：uniformContinuous_iff [PseudoMetricSpace β
] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b :
 α⦄, dist a b < δ …
· 使用定理 `rat_mul_continuous_lemma`：rat_mul_continuous_lemma {ε K₁ K₂ : α} (ε0 : 0
 < ε) : exists δ > 0, forall {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ -> abv b₂ < K₂ -> ab
v (a₁ - b₁) < …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Real.uniformContinuous_mul (s : Set (ℝ × ℝ)) {r₁ r₂ : ℝ}
    (H : ∀ x ∈ s, |(x : ℝ × ℝ).1| < r₁ ∧ |x.2| < r₂) :
    UniformContinuous fun p : s => p.1.1 * p.1.2 :=
  Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0
    ⟨δ, δ0, fun {a b} h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩
/-
**Real.totallyBounded_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.totallyBounded_ball (x ε : Real) : TotallyBounded (ball x ε)
参数：x ε : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ball_eq_Ioo`：Real.ball_eq_Ioo (x r : Real) : ball x r = Ioo (x - r)
 (x + r)
· 使用引理 `totallyBounded_Ioo`：totallyBounded_Ioo (a b : α) : TotallyBounded (Ioo a
 b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem Real.totallyBounded_ball (x ε : ℝ) : TotallyBounded (ball x ε) := by
  rw [Real.ball_eq_Ioo]; apply totallyBounded_Ioo
/-
**Real.subfield_eq_of_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.subfield_eq_of_closed {K : Subfield Real} (hc : IsClosed (K : Set Rea
l)) : K = ⊤
参数：hc : IsClosed (K : Set Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Subfield.coe_top`：coe_top : ((⊤ : Subfield K) : Set K) = Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用引理 `SubfieldClass.ratCast_mem`：ratCast_mem (s : S) (q : Rat) : (q : K) in s
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `Rat.denseRange_cast`：Rat.denseRange_cast {𝕜} [Field 𝕜] [LinearOrder 𝕜] [
IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜] : 
DenseRang…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem Real.subfield_eq_of_closed {K : Subfield ℝ} (hc : IsClosed (K : Set ℝ)) : K = ⊤ := by
  rw [SetLike.ext'_iff, Subfield.coe_top, ← hc.closure_eq]
  refine Rat.denseRange_cast.mono ?_ |>.closure_eq
  rintro - ⟨_, rfl⟩
  exact SubfieldClass.ratCast_mem K _
/-
**Real.exists_seq_rat_strictMono_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.exists_seq_rat_strictMono_tendsto (x : Real) : exists u : Nat -> Rat,
 StrictMono u ∧ (forall n, u n < x) ∧ Tendsto (u · : Nat -> Real) atTop (𝓝 x)
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.exists_seq_strictMono_tendsto`：DenseRange.exists_seq_strictMo
no_tendsto {β : Type*} [LinearOrder β] [DenselyOrdered α] [NoMinOrder α] [FirstC
ountableTopology α] {f : β -> …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Rat.denseRange_cast`：Rat.denseRange_cast {𝕜} [Field 𝕜] [LinearOrder 𝕜] [
IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜] : 
DenseRang…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Rat.cast_strictMono`：cast_strictMono : StrictMono ((↑) : Rat -> K)
-/
theorem Real.exists_seq_rat_strictMono_tendsto (x : ℝ) :
    ∃ u : ℕ → ℚ, StrictMono u ∧ (∀ n, u n < x) ∧ Tendsto (u · : ℕ → ℝ) atTop (𝓝 x) :=
  Rat.denseRange_cast.exists_seq_strictMono_tendsto Rat.cast_strictMono.monotone x
/-
**Real.exists_seq_rat_strictAnti_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.exists_seq_rat_strictAnti_tendsto (x : Real) : exists u : Nat -> Rat,
 StrictAnti u ∧ (forall n, x < u n) ∧ Tendsto (u · : Nat -> Real) atTop (𝓝 x)
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.exists_seq_strictAnti_tendsto`：DenseRange.exists_seq_strictAn
ti_tendsto {β : Type*} [LinearOrder β] [DenselyOrdered α] [NoMaxOrder α] [FirstC
ountableTopology α] {f : β -> …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Rat.denseRange_cast`：Rat.denseRange_cast {𝕜} [Field 𝕜] [LinearOrder 𝕜] [
IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜] : 
DenseRang…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Rat.cast_strictMono`：cast_strictMono : StrictMono ((↑) : Rat -> K)
-/
theorem Real.exists_seq_rat_strictAnti_tendsto (x : ℝ) :
    ∃ u : ℕ → ℚ, StrictAnti u ∧ (∀ n, x < u n) ∧ Tendsto (u · : ℕ → ℝ) atTop (𝓝 x) :=
  Rat.denseRange_cast.exists_seq_strictAnti_tendsto Rat.cast_strictMono.monotone x

section

/-
**closure_ordConnected_inter_rat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_ordConnected_inter_rat {s : Set Real} (conn : s.OrdConnected) (nt 
: s.Nontrivial) : closure (s inter .range Rat.cast) = closure s
参数：conn : s.OrdConnected；nt : s.Nontrivial。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Real.mem_closure_iff`：Real.mem_closure_iff {s : Set Real} {x : Real} : x
 in closure s ↔ forall ε > 0, exists y in s, |y - x| < ε
· 使用定理 `Set.Nontrivial.exists_ne`：∀ {α : Type u} {s : Set α}, s.Nontrivial → ∀ (
z : α), ∃ x ∈ s, x ≠ z
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `sub_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] (a : α) {b : α}, 0 < b → a - b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
（共 37 条，此处仅展示前 30 条）
-/
theorem closure_ordConnected_inter_rat {s : Set ℝ} (conn : s.OrdConnected) (nt : s.Nontrivial) :
    closure (s ∩ .range Rat.cast) = closure s :=
  (closure_mono inter_subset_left).antisymm <| isClosed_closure.closure_subset_iff.mpr fun x hx ↦
    Real.mem_closure_iff.mpr fun ε ε_pos ↦ by
      have ⟨z, hz, ne⟩ := nt.exists_ne x
      refine ne.lt_or_gt.elim (fun lt ↦ ?_) fun lt ↦ ?_
      · have ⟨q, h₁, h₂⟩ := exists_rat_btwn (max_lt lt (sub_lt_self x ε_pos))
        rw [max_lt_iff] at h₁
        refine ⟨q, ⟨conn.out hz hx ⟨h₁.1.le, h₂.le⟩, q, rfl⟩, ?_⟩
        simpa only [abs_sub_comm, abs_of_pos (sub_pos.mpr h₂), sub_lt_comm] using h₁.2
      · have ⟨q, h₁, h₂⟩ := exists_rat_btwn (lt_min lt (lt_add_of_pos_right x ε_pos))
        rw [lt_min_iff] at h₂
        refine ⟨q, ⟨conn.out hx hz ⟨h₁.le, h₂.1.le⟩, q, rfl⟩, ?_⟩
        simpa only [abs_of_pos (sub_pos.2 h₁), sub_lt_iff_lt_add'] using h₂.2
/-
**closure_of_rat_image_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_of_rat_image_lt {q : Rat} : closure (((↑) : Rat -> Real) '' { x | 
q < x }) = { r | ↑q <= r }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `closure_Ioi`：closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici 
a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `closure_ordConnected_inter_rat`：closure_ordConnected_inter_rat {s : Set 
Real} (conn : s.OrdConnected) (nt : s.Nontrivial) : closure (s inter .range Rat.
cast) = closure s
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
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
（共 68 条，此处仅展示前 30 条）
-/
theorem closure_of_rat_image_lt {q : ℚ} :
    closure (((↑) : ℚ → ℝ) '' { x | q < x }) = { r | ↑q ≤ r } := by
  convert! closure_ordConnected_inter_rat (ordConnected_Ioi (a := (q : ℝ))) _ using 1
  · congr!; aesop
  · exact (closure_Ioi _).symm
  · exact ⟨q + 1, show (q : ℝ) < _ by linarith, q + 2, show (q : ℝ) < _ by linarith, by simp⟩

@[deprecated (since := "2026-04-07")]
alias Real.cobounded_eq := IsOrderBornology.cobounded_eq

/- TODO(Mario): Put these back only if needed later
lemma closure_of_rat_image_le_eq {q : ℚ} : closure ((coe : ℚ → ℝ) '' {x | q ≤ x}) = {r | ↑q ≤ r} :=
  _

lemma closure_of_rat_image_le_le_eq {a b : ℚ} (hab : a ≤ b) :
    closure (of_rat '' {q:ℚ | a ≤ q ∧ q ≤ b}) = {r:ℝ | of_rat a ≤ r ∧ r ≤ of_rat b} :=
  _
-/

end

section Periodic

namespace Function

/-- A continuous, periodic function has compact range. -/
/-
**Function.Periodic.compact_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Function.Pe
riodic`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] {f : ℝ → α} {c : ℝ},   Function
.Periodic f c → c ≠ 0 → Continuous f → IsCompact (Set.range f)
参数：Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Periodic.image_uIcc`：∀ {α : Type u_1} {β : Type u_2} {f : α → β
} {c : α} [inst : AddCommGroup α] [inst_1 : LinearOrder α]   [IsOrderedAddMonoid
 α] [Archimedean α…
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ

--- 原说明 ---
A continuous, periodic function has compact range.
-/
theorem Periodic.compact_of_continuous [TopologicalSpace α] {f : ℝ → α} {c : ℝ} (hp : Periodic f c)
    (hc : c ≠ 0) (hf : Continuous f) : IsCompact (range f) := by
  rw [← hp.image_uIcc hc 0]
  exact isCompact_uIcc.image hf

/-- A continuous, periodic function is bounded. -/
/-
**Function.Periodic.isBounded_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Function.
Periodic`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {f : ℝ → α} {c : ℝ},   Functio
n.Periodic f c → c ≠ 0 → Continuous f → Bornology.IsBounded (Set.range f)
参数：Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `Function.Periodic.compact_of_continuous`：∀ {α : Type u} [inst : Topologi
calSpace α] {f : ℝ → α} {c : ℝ},   Function.Periodic f c → c ≠ 0 → Continuous f 
→ IsCompact (Set.range f)

--- 原说明 ---
A continuous, periodic function is bounded.
-/
theorem Periodic.isBounded_of_continuous [PseudoMetricSpace α] {f : ℝ → α} {c : ℝ}
    (hp : Periodic f c) (hc : c ≠ 0) (hf : Continuous f) : IsBounded (range f) :=
  (hp.compact_of_continuous hc hf).isBounded

end Function

end Periodic

section Monotone

variable {ι : Type*} [Preorder ι] [Nonempty ι]

/-- A monotone, bounded above sequence `f : ℕ → ℝ` on `Ici k` has the finite
limit `sSup (f '' Ici k)`. -/
/-
**Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici {f : Nat -> Real} 
{k : Nat} (h_mon : MonotoneOn f (Ici k)) (h_bdd : BddAbove (f '' Ici k)) : Tends
to f atTop (𝓝 (sSup (f '' Ici k)))
参数：h_mon : MonotoneOn f (Ici k)；h_bdd : BddAbove (f '' Ici k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `Set.range_add_eq_image_Ici`：range_add_eq_image_Ici : range (fun x => f (
x + k)) = f '' Ici k
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用定理 `tendsto_atTop_ciSup`：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : B
ddAbove <| range f) : Tendsto f atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `monotone_add_nat_iff_monotoneOn_nat_Ici`：monotone_add_nat_iff_monotoneOn
_nat_Ici {f : Nat -> α} {k : Nat} : Monotone (fun n => f (n + k)) ↔ MonotoneOn f
 { x | k <= x }
· 使用定理 `Set.Ici.eq_1`：∀ {α : Type u_1} [inst : Preorder α] (b : α), Set.Ici b = 
{x | b ≤ x}

--- 原说明 ---
A monotone, bounded above sequence `f : ℕ → ℝ` on `Ici k` has the finite
limit `sSup (f '' Ici k)`.
-/
theorem Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici {f : ℕ → ℝ} {k : ℕ}
    (h_mon : MonotoneOn f (Ici k)) (h_bdd : BddAbove (f '' Ici k)) :
    Tendsto f atTop (𝓝 (sSup (f '' Ici k))) := by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [Ici, ← monotone_add_nat_iff_monotoneOn_nat_Ici] at h_mon
  rw [← tendsto_add_atTop_iff_nat k, ← range_add_eq_image_Ici, sSup_range]
  exact tendsto_atTop_ciSup h_mon h_bdd

/-- An antitone, bounded below sequence `f : ℕ → ℝ` on `Ici k` has the finite
limit `sInf (f '' Ici k)`. -/
/-
**Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici {f : Nat -> Real} 
{k : Nat} (h_ant : AntitoneOn f (Ici k)) (h_bdd : BddBelow (f '' Ici k)) : Tends
to f atTop (𝓝 (sInf (f '' Ici k)))
参数：h_ant : AntitoneOn f (Ici k)；h_bdd : BddBelow (f '' Ici k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `Set.range_add_eq_image_Ici`：range_add_eq_image_Ici : range (fun x => f (
x + k)) = f '' Ici k
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `tendsto_atTop_ciInf`：tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : B
ddBelow <| range f) : Tendsto f atTop (𝓝 (⨅ i, f i))
· 使用定理 `LinearOrder.infConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], InfConvergenceClass α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `antitone_add_nat_iff_antitoneOn_nat_Ici`：antitone_add_nat_iff_antitoneOn
_nat_Ici {f : Nat -> α} {k : Nat} : Antitone (fun n => f (n + k)) ↔ AntitoneOn f
 { x | k <= x }
· 使用定理 `Set.Ici.eq_1`：∀ {α : Type u_1} [inst : Preorder α] (b : α), Set.Ici b = 
{x | b ≤ x}

--- 原说明 ---
An antitone, bounded below sequence `f : ℕ → ℝ` on `Ici k` has the finite
limit `sInf (f '' Ici k)`.
-/
theorem Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici {f : ℕ → ℝ} {k : ℕ}
    (h_ant : AntitoneOn f (Ici k)) (h_bdd : BddBelow (f '' Ici k)) :
    Tendsto f atTop (𝓝 (sInf (f '' Ici k))) := by
  rw [← range_add_eq_image_Ici] at h_bdd
  rw [Ici, ← antitone_add_nat_iff_antitoneOn_nat_Ici] at h_ant
  rw [← tendsto_add_atTop_iff_nat k, ← range_add_eq_image_Ici, sInf_range]
  exact tendsto_atTop_ciInf h_ant h_bdd

variable [IsDirected ι (· ≤ ·)]

/-- The limit of a monotone, bounded above function `f : ι → ℝ` is a least upper bound
of the function. -/
/-
**Real.isLUB_of_tendsto_monotone_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.isLUB_of_tendsto_monotone_bddAbove {f : ι -> Real} {x : Real} (h_tto 
: Tendsto f atTop (𝓝 x)) (h_mon : Monotone f) (h_bdd : BddAbove (range f)) : IsL
UB (range f) x
参数：h_tto : Tendsto f atTop (𝓝 x)；h_mon : Monotone f；h_bdd : BddAbove (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `tendsto_atTop_ciSup`：tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : B
ddAbove <| range f) : Tendsto f atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `isLUB_ciSup`：isLUB_ciSup [Nonempty ι] {f : ι -> α} (H : BddAbove (range 
f)) : IsLUB (range f) (⨆ i, f i)

--- 原说明 ---
The limit of a monotone, bounded above function `f : ι → ℝ` is a least upper bou
nd
of the function.
-/
theorem Real.isLUB_of_tendsto_monotone_bddAbove {f : ι → ℝ}
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x))
    (h_mon : Monotone f) (h_bdd : BddAbove (range f)) : IsLUB (range f) x := by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciSup h_mon h_bdd)]
  exact isLUB_ciSup h_bdd

/-- The limit of an antitone, bounded below function `f : ι → ℝ` is a greatest lower bound
of the function. -/
/-
**Real.isGLB_of_tendsto_antitone_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.isGLB_of_tendsto_antitone_bddBelow {f : ι -> Real} {x : Real} (h_tto 
: Tendsto f atTop (𝓝 x)) (h_ant : Antitone f) (h_bdd : BddBelow (range f)) : IsG
LB (range f) x
参数：h_tto : Tendsto f atTop (𝓝 x)；h_ant : Antitone f；h_bdd : BddBelow (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `tendsto_atTop_ciInf`：tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : B
ddBelow <| range f) : Tendsto f atTop (𝓝 (⨅ i, f i))
· 使用定理 `LinearOrder.infConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], InfConvergenceClass α
· 使用定理 `isGLB_ciInf`：isGLB_ciInf [Nonempty ι] {f : ι -> α} (H : BddBelow (range 
f)) : IsGLB (range f) (⨅ i, f i)

--- 原说明 ---
The limit of an antitone, bounded below function `f : ι → ℝ` is a greatest lower
 bound
of the function.
-/
theorem Real.isGLB_of_tendsto_antitone_bddBelow {f : ι → ℝ}
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x))
    (h_ant : Antitone f) (h_bdd : BddBelow (range f)) : IsGLB (range f) x := by
  rw [tendsto_nhds_unique h_tto (tendsto_atTop_ciInf h_ant h_bdd)]
  exact isGLB_ciInf h_bdd

/-- The limit of an antitone, bounded below sequence `f : ℕ → ℝ` on `Ici k` is a least
upper bound of the sequence. -/
/-
**Real.isLUB_of_tendsto_monotoneOn_bddAbove_nat_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Real.isLUB_of_tendsto_monotoneOn_bddAbove_nat_Ici {f : Nat -> Real} {k : N
at} {x : Real} (h_tto : Tendsto f atTop (𝓝 x)) (h_mon : MonotoneOn f (Ici k)) (h
_bdd : BddAbove (f '' Ici k)) : IsLUB (f '' Ici k) x
参数：h_tto : Tendsto f atTop (𝓝 x)；h_mon : MonotoneOn f (Ici k)；h_bdd : BddAbove (
f '' Ici k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici`：Real.tendsto_at
Top_csSup_of_monotoneOn_bddAbove_nat_Ici {f : Nat -> Real} {k : Nat} (h_mon : Mo
notoneOn f (Ici k)) (h_bdd : BddAbove (f '' I…
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `Set.nonempty_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set.Ici
 a).Nonempty

--- 原说明 ---
The limit of an antitone, bounded below sequence `f : ℕ → ℝ` on `Ici k` is a lea
st
upper bound of the sequence.
-/
theorem Real.isLUB_of_tendsto_monotoneOn_bddAbove_nat_Ici {f : ℕ → ℝ} {k : ℕ}
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x))
    (h_mon : MonotoneOn f (Ici k)) (h_bdd : BddAbove (f '' Ici k)) : IsLUB (f '' Ici k) x := by
  rw [tendsto_nhds_unique h_tto
    (Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici h_mon h_bdd)]
  exact isLUB_csSup (image_nonempty.mpr nonempty_Ici) h_bdd

/-- The limit of an antitone, bounded below sequence `f : ℕ → ℝ` on `Ici k` is a greatest
lower bound of the sequence. -/
/-
**Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici {f : Nat -> Real} {k : N
at} {x : Real} (h_tto : Tendsto f atTop (𝓝 x)) (h_ant : AntitoneOn f (Ici k)) (h
_bdd : BddBelow (f '' Ici k)) : IsGLB (f '' Ici k) x
参数：h_tto : Tendsto f atTop (𝓝 x)；h_ant : AntitoneOn f (Ici k)；h_bdd : BddBelow (
f '' Ici k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici`：Real.tendsto_at
Top_csInf_of_antitoneOn_bddBelow_nat_Ici {f : Nat -> Real} {k : Nat} (h_ant : An
titoneOn f (Ici k)) (h_bdd : BddBelow (f '' I…
· 使用定理 `isGLB_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s
 : Set α},   s.Nonempty → autoParam (BddBelow s) isGLB_csInf._auto_1 → IsGLB s (
s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `Set.nonempty_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set.Ici
 a).Nonempty

--- 原说明 ---
The limit of an antitone, bounded below sequence `f : ℕ → ℝ` on `Ici k` is a gre
atest
lower bound of the sequence.
-/
theorem Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici {f : ℕ → ℝ} {k : ℕ}
    {x : ℝ} (h_tto : Tendsto f atTop (𝓝 x))
    (h_ant : AntitoneOn f (Ici k)) (h_bdd : BddBelow (f '' Ici k)) : IsGLB (f '' Ici k) x := by
  rw [tendsto_nhds_unique h_tto
    (Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici h_ant h_bdd)]
  exact isGLB_csInf (image_nonempty.mpr nonempty_Ici) h_bdd

end Monotone

