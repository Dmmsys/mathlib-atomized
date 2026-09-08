/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Darboux's theorem

In this file we prove that the derivative of a differentiable function on an interval takes all
intermediate values. The proof is based on the
[Wikipedia](https://en.wikipedia.org/wiki/Darboux%27s_theorem_(analysis)) page about this theorem.
-/

public section

open Filter Set

open scoped Topology

variable {a b : ℝ} {f f' : ℝ → ℝ}

/-- **Darboux's theorem**: if `a ≤ b` and `f' a < m < f' b`, then `f' c = m` for some
`c ∈ (a, b)`. -/
/-
**exists_hasDerivWithinAt_eq_of_gt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_hasDerivWithinAt_eq_of_gt_of_lt (hab : a <= b) (hf : forall x in Ic
c a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : Real} (hma : f' a < m) (hmb :
 m < f' b) : m in f' '' Ioo a b
参数：hab : a <= b；hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x；
hma : f' a < m；hmb : m < f' b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `lt_asymm`：lt_asymm (h : a < b) : ¬b < a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivWithinAt.sub`：HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s
 x) (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (f - g) (f' - g') s x
· 使用定理 `HasDerivWithinAt.const_mul`：HasDerivWithinAt.const_mul (c : 𝔸) (hd : Has
DerivWithinAt d d' s x) : HasDerivWithinAt (fun y => c * d y) (c * d') s x
· 使用定理 `hasDerivWithinAt_id`：hasDerivWithinAt_id : HasDerivWithinAt id 1 s x
· 使用定理 `IsCompact.exists_isMinOn`：IsCompact.exists_isMinOn [ClosedIicTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `HasDerivWithinAt.continuousWithinAt`：HasDerivWithinAt.continuousWithinAt
 (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `nonneg_of_mul_nonneg_right`：nonneg_of_mul_nonneg_right [PosMulStrictMono
 R] (h : 0 <= a * b) (ha : 0 < a) : 0 <= b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `sub_mem_posTangentConeAt_of_segment_subset`：sub_mem_posTangentConeAt_of_
segment_subset (h : segment Real x y subseteq s) : y - x in posTangentConeAt s x
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
**Darboux's theorem**: if `a ≤ b` and `f' a < m < f' b`, then `f' c = m` for som
e
`c ∈ (a, b)`.
-/
theorem exists_hasDerivWithinAt_eq_of_gt_of_lt (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ} (hma : f' a < m)
    (hmb : m < f' b) : m ∈ f' '' Ioo a b := by
  rcases hab.eq_or_lt with (rfl | hab')
  · exact (lt_asymm hma hmb).elim
  set g : ℝ → ℝ := fun x => f x - m * x
  have hg : ∀ x ∈ Icc a b, HasDerivWithinAt g (f' x - m) (Icc a b) x := by
    intro x hx
    simpa using! (hf x hx).sub ((hasDerivWithinAt_id x _).const_mul m)
  obtain ⟨c, cmem, hc⟩ : ∃ c ∈ Icc a b, IsMinOn g (Icc a b) c :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 <| hab) fun x hx => (hg x hx).continuousWithinAt
  have cmem' : c ∈ Ioo a b := by
    rcases cmem.1.eq_or_lt with (rfl | hac)
    -- Show that `c` can't be equal to `a`
    · refine absurd (sub_nonneg.1 <| nonneg_of_mul_nonneg_right ?_ (sub_pos.2 hab'))
        (not_le_of_gt hma)
      have : b - a ∈ posTangentConeAt (Icc a b) a :=
        sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc hab ▸ Subset.rfl)
      simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
        using! hc.localize.hasFDerivWithinAt_nonneg (hg a (left_mem_Icc.2 hab)) this
    rcases cmem.2.eq_or_lt' with (rfl | hcb)
    -- Show that `c` can't be equal to `b`
    · refine absurd (sub_nonpos.1 <| nonpos_of_mul_nonneg_right ?_ (sub_lt_zero.2 hab'))
        (not_le_of_gt hmb)
      have : a - b ∈ posTangentConeAt (Icc a b) b :=
        sub_mem_posTangentConeAt_of_segment_subset (by rw [segment_symm, segment_eq_Icc hab])
      simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
        using! hc.localize.hasFDerivWithinAt_nonneg (hg b (right_mem_Icc.2 hab)) this
    exact ⟨hac, hcb⟩
  use c, cmem'
  rw [← sub_eq_zero]
  have : Icc a b ∈ 𝓝 c := by rwa [← mem_interior_iff_mem_nhds, interior_Icc]
  exact (hc.isLocalMin this).hasDerivAt_eq_zero ((hg c cmem).hasDerivAt this)

/-- **Darboux's theorem**: if `a ≤ b` and `f' b < m < f' a`, then `f' c = m` for some `c ∈ (a, b)`.
-/
/-
**exists_hasDerivWithinAt_eq_of_lt_of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_hasDerivWithinAt_eq_of_lt_of_gt (hab : a <= b) (hf : forall x in Ic
c a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : Real} (hma : m < f' a) (hmb :
 f' b < m) : m in f' '' Ioo a b
参数：hab : a <= b；hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x；
hma : m < f' a；hmb : f' b < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `exists_hasDerivWithinAt_eq_of_gt_of_lt`：exists_hasDerivWithinAt_eq_of_gt
_of_lt (hab : a <= b) (hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc 
a b) x) {m : Real} (hma : f'…
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg

--- 原说明 ---
**Darboux's theorem**: if `a ≤ b` and `f' b < m < f' a`, then `f' c = m` for som
e `c ∈ (a, b)`.
-/
theorem exists_hasDerivWithinAt_eq_of_lt_of_gt (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ} (hma : m < f' a)
    (hmb : f' b < m) : m ∈ f' '' Ioo a b :=
  let ⟨c, cmem, hc⟩ :=
    exists_hasDerivWithinAt_eq_of_gt_of_lt hab (fun x hx => (hf x hx).neg) (neg_lt_neg hma)
      (neg_lt_neg hmb)
  ⟨c, cmem, neg_injective hc⟩

/-- **Darboux's theorem**: the image of a `Set.OrdConnected` set under `f'` is a `Set.OrdConnected`
set, `HasDerivWithinAt` version. -/
/-
**Set.OrdConnected.image_hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.image_hasDerivWithinAt {s : Set Real} (hs : OrdConnected 
s) (hf : forall x in s, HasDerivWithinAt f (f' x) s x) : OrdConnected (f' '' s)
参数：hs : OrdConnected s；hf : forall x in s, HasDerivWithinAt f (f' x) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Set.ordConnected_of_Ioo`：ordConnected_of_Ioo {α : Type*} [PartialOrder α
] {s : Set α} (hs : forall x in s, forall y in s, x < y -> Ioo x y subseteq s) :
 OrdConnected…
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `exists_hasDerivWithinAt_eq_of_gt_of_lt`：exists_hasDerivWithinAt_eq_of_gt
_of_lt (hab : a <= b) (hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc 
a b) x) {m : Real} (hma : f'…
· 使用定理 `HasDerivWithinAt.mono`：HasDerivWithinAt.mono (h : HasDerivWithinAt f f' 
t x) (hst : s subseteq t) : HasDerivWithinAt f f' s x
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `exists_hasDerivWithinAt_eq_of_lt_of_gt`：exists_hasDerivWithinAt_eq_of_lt
_of_gt (hab : a <= b) (hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc 
a b) x) {m : Real} (hma : m …

--- 原说明 ---
**Darboux's theorem**: the image of a `Set.OrdConnected` set under `f'` is a `Se
t.OrdConnected`
set, `HasDerivWithinAt` version.
-/
theorem Set.OrdConnected.image_hasDerivWithinAt {s : Set ℝ} (hs : OrdConnected s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) : OrdConnected (f' '' s) := by
  apply ordConnected_of_Ioo
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ - m ⟨hma, hmb⟩
  rcases le_total a b with hab | hab
  · have : Icc a b ⊆ s := hs.out ha hb
    rcases exists_hasDerivWithinAt_eq_of_gt_of_lt hab (fun x hx => (hf x <| this hx).mono this) hma
        hmb with
      ⟨c, cmem, hc⟩
    exact ⟨c, this <| Ioo_subset_Icc_self cmem, hc⟩
  · have : Icc b a ⊆ s := hs.out hb ha
    rcases exists_hasDerivWithinAt_eq_of_lt_of_gt hab (fun x hx => (hf x <| this hx).mono this) hmb
        hma with
      ⟨c, cmem, hc⟩
    exact ⟨c, this <| Ioo_subset_Icc_self cmem, hc⟩

/-- **Darboux's theorem**: the image of a `Set.OrdConnected` set under `f'` is a `Set.OrdConnected`
set, `derivWithin` version. -/
/-
**Set.OrdConnected.image_derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.image_derivWithin {s : Set Real} (hs : OrdConnected s) (h
f : DifferentiableOn Real f s) : OrdConnected (derivWithin f s '' s)
参数：hs : OrdConnected s；hf : DifferentiableOn Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.image_hasDerivWithinAt`：Set.OrdConnected.image_hasDeriv
WithinAt {s : Set Real} (hs : OrdConnected s) (hf : forall x in s, HasDerivWithi
nAt f (f' x) s x) : OrdConnec…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x

--- 原说明 ---
**Darboux's theorem**: the image of a `Set.OrdConnected` set under `f'` is a `Se
t.OrdConnected`
set, `derivWithin` version.
-/
theorem Set.OrdConnected.image_derivWithin {s : Set ℝ} (hs : OrdConnected s)
    (hf : DifferentiableOn ℝ f s) : OrdConnected (derivWithin f s '' s) :=
  hs.image_hasDerivWithinAt fun x hx => (hf x hx).hasDerivWithinAt

/-- **Darboux's theorem**: the image of a `Set.OrdConnected` set under `f'` is a `Set.OrdConnected`
set, `deriv` version. -/
/-
**Set.OrdConnected.image_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.image_deriv {s : Set Real} (hs : OrdConnected s) (hf : fo
rall x in s, DifferentiableAt Real f x) : OrdConnected (deriv f '' s)
参数：hs : OrdConnected s；hf : forall x in s, DifferentiableAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.image_hasDerivWithinAt`：Set.OrdConnected.image_hasDeriv
WithinAt {s : Set Real} (hs : OrdConnected s) (hf : forall x in s, HasDerivWithi
nAt f (f' x) s x) : OrdConnec…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x

--- 原说明 ---
**Darboux's theorem**: the image of a `Set.OrdConnected` set under `f'` is a `Se
t.OrdConnected`
set, `deriv` version.
-/
theorem Set.OrdConnected.image_deriv {s : Set ℝ} (hs : OrdConnected s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) : OrdConnected (deriv f '' s) :=
  hs.image_hasDerivWithinAt fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt

/-- **Darboux's theorem**: the image of a convex set under `f'` is a convex set,
`HasDerivWithinAt` version. -/
/-
**Convex.image_hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.image_hasDerivWithinAt {s : Set Real} (hs : Convex Real s) (hf : fo
rall x in s, HasDerivWithinAt f (f' x) s x) : Convex Real (f' '' s)
参数：hs : Convex Real s；hf : forall x in s, HasDerivWithinAt f (f' x) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Set.OrdConnected.convex`：Set.OrdConnected.convex [Semiring 𝕜] [PartialOr
der 𝕜] [AddCommMonoid E] [LinearOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [Po
sSMulMono 𝕜 E…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Set.OrdConnected.image_hasDerivWithinAt`：Set.OrdConnected.image_hasDeriv
WithinAt {s : Set Real} (hs : OrdConnected s) (hf : forall x in s, HasDerivWithi
nAt f (f' x) s x) : OrdConnec…
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected

--- 原说明 ---
**Darboux's theorem**: the image of a convex set under `f'` is a convex set,
`HasDerivWithinAt` version.
-/
theorem Convex.image_hasDerivWithinAt {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) : Convex ℝ (f' '' s) :=
  (hs.ordConnected.image_hasDerivWithinAt hf).convex

/-- **Darboux's theorem**: the image of a convex set under `f'` is a convex set,
`derivWithin` version. -/
/-
**Convex.image_derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.image_derivWithin {s : Set Real} (hs : Convex Real s) (hf : Differe
ntiableOn Real f s) : Convex Real (derivWithin f s '' s)
参数：hs : Convex Real s；hf : DifferentiableOn Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.convex`：Set.OrdConnected.convex [Semiring 𝕜] [PartialOr
der 𝕜] [AddCommMonoid E] [LinearOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [Po
sSMulMono 𝕜 E…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Set.OrdConnected.image_derivWithin`：Set.OrdConnected.image_derivWithin {
s : Set Real} (hs : OrdConnected s) (hf : DifferentiableOn Real f s) : OrdConnec
ted (derivWithin f s '' …
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected

--- 原说明 ---
**Darboux's theorem**: the image of a convex set under `f'` is a convex set,
`derivWithin` version.
-/
theorem Convex.image_derivWithin {s : Set ℝ} (hs : Convex ℝ s) (hf : DifferentiableOn ℝ f s) :
    Convex ℝ (derivWithin f s '' s) :=
  (hs.ordConnected.image_derivWithin hf).convex

/-- **Darboux's theorem**: the image of a convex set under `f'` is a convex set,
`deriv` version. -/
/-
**Convex.image_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.image_deriv {s : Set Real} (hs : Convex Real s) (hf : forall x in s
, DifferentiableAt Real f x) : Convex Real (deriv f '' s)
参数：hs : Convex Real s；hf : forall x in s, DifferentiableAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.convex`：Set.OrdConnected.convex [Semiring 𝕜] [PartialOr
der 𝕜] [AddCommMonoid E] [LinearOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [Po
sSMulMono 𝕜 E…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Set.OrdConnected.image_deriv`：Set.OrdConnected.image_deriv {s : Set Real
} (hs : OrdConnected s) (hf : forall x in s, DifferentiableAt Real f x) : OrdCon
nected (deriv f ''…
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected

--- 原说明 ---
**Darboux's theorem**: the image of a convex set under `f'` is a convex set,
`deriv` version.
-/
theorem Convex.image_deriv {s : Set ℝ} (hs : Convex ℝ s) (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    Convex ℝ (deriv f '' s) :=
  (hs.ordConnected.image_deriv hf).convex

/-- **Darboux's theorem**: if `a ≤ b` and `f' a ≤ m ≤ f' b`, then `f' c = m` for some
`c ∈ [a, b]`. -/
/-
**exists_hasDerivWithinAt_eq_of_ge_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_hasDerivWithinAt_eq_of_ge_of_le (hab : a <= b) (hf : forall x in Ic
c a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : Real} (hma : f' a <= m) (hmb 
: m <= f' b) : m in f' '' Icc a b
参数：hab : a <= b；hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x；
hma : f' a <= m；hmb : m <= f' b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Set.OrdConnected.image_hasDerivWithinAt`：Set.OrdConnected.image_hasDeriv
WithinAt {s : Set Real} (hs : OrdConnected s) (hf : forall x in s, HasDerivWithi
nAt f (f' x) s x) : OrdConnec…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a

--- 原说明 ---
**Darboux's theorem**: if `a ≤ b` and `f' a ≤ m ≤ f' b`, then `f' c = m` for som
e
`c ∈ [a, b]`.
-/
theorem exists_hasDerivWithinAt_eq_of_ge_of_le (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ} (hma : f' a ≤ m)
    (hmb : m ≤ f' b) : m ∈ f' '' Icc a b :=
  (ordConnected_Icc.image_hasDerivWithinAt hf).out (mem_image_of_mem _ (left_mem_Icc.2 hab))
    (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩

/-- **Darboux's theorem**: if `a ≤ b` and `f' b ≤ m ≤ f' a`, then `f' c = m` for some
`c ∈ [a, b]`. -/
/-
**exists_hasDerivWithinAt_eq_of_le_of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_hasDerivWithinAt_eq_of_le_of_ge (hab : a <= b) (hf : forall x in Ic
c a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : Real} (hma : f' a <= m) (hmb 
: m <= f' b) : m in f' '' Icc a b
参数：hab : a <= b；hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x；
hma : f' a <= m；hmb : m <= f' b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Set.OrdConnected.image_hasDerivWithinAt`：Set.OrdConnected.image_hasDeriv
WithinAt {s : Set Real} (hs : OrdConnected s) (hf : forall x in s, HasDerivWithi
nAt f (f' x) s x) : OrdConnec…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a

--- 原说明 ---
**Darboux's theorem**: if `a ≤ b` and `f' b ≤ m ≤ f' a`, then `f' c = m` for som
e
`c ∈ [a, b]`.
-/
theorem exists_hasDerivWithinAt_eq_of_le_of_ge (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ} (hma : f' a ≤ m)
    (hmb : m ≤ f' b) : m ∈ f' '' Icc a b :=
  (ordConnected_Icc.image_hasDerivWithinAt hf).out (mem_image_of_mem _ (left_mem_Icc.2 hab))
    (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩

/-- If the derivative of a function is never equal to `m`, then either
it is always greater than `m`, or it is always less than `m`. -/
/-
**hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne {s : Set Real} (hs : 
Convex Real s) (hf : forall x in s, HasDerivWithinAt f (f' x) s x) {m : Real} (h
f' : forall x in s, f' x != m) : (forall x in s, f' x < m) ∨ forall x in s, m < 
f' x
参数：hs : Convex Real s；hf : forall x in s, HasDerivWithinAt f (f' x) s x；hf' : fo
rall x in s, f' x != m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Set.OrdConnected.image_hasDerivWithinAt`：Set.OrdConnected.image_hasDeriv
WithinAt {s : Set Real} (hs : OrdConnected s) (hf : forall x in s, HasDerivWithi
nAt f (f' x) s x) : OrdConnec…
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
If the derivative of a function is never equal to `m`, then either
it is always greater than `m`, or it is always less than `m`.
-/
theorem hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) {m : ℝ} (hf' : ∀ x ∈ s, f' x ≠ m) :
    (∀ x ∈ s, f' x < m) ∨ ∀ x ∈ s, m < f' x := by
  contrapose! hf'
  rcases hf' with ⟨⟨b, hb, hmb⟩, ⟨a, ha, hma⟩⟩
  exact (hs.ordConnected.image_hasDerivWithinAt hf).out (mem_image_of_mem f' ha)
    (mem_image_of_mem f' hb) ⟨hma, hmb⟩
