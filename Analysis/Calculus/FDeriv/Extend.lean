/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Extending differentiability to the boundary

We investigate how differentiable functions inside a set extend to differentiable functions
on the boundary. For this, it suffices that the function and its derivative admit limits there.
A general version of this statement is given in `hasFDerivWithinAt_closure_of_tendsto_fderiv`.

One-dimensional versions, in which one wants to obtain differentiability at the left endpoint or
the right endpoint of an interval, are given in `hasDerivWithinAt_Ici_of_tendsto_deriv` and
`hasDerivWithinAt_Iic_of_tendsto_deriv`.  These versions are formulated in terms of the
one-dimensional derivative `deriv ℝ f`.
-/

public section


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

open Filter Set Metric ContinuousLinearMap

open scoped Topology

/-- If a function `f` is differentiable in a convex open set and continuous on its closure, and its
derivative converges to a limit `f'` at a point on the boundary, then `f` is differentiable there
with derivative `f'`. -/
/-
**hasFDerivWithinAt_closure_of_tendsto_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_closure_of_tendsto_fderiv {f : E -> F} {s : Set E} {x : 
E} {f' : E ->L[Real] F} (f_diff : DifferentiableOn Real f s) (s_conv : Convex Re
al s) (s_open : IsOpen s) (f_cont : forall y in closure s, ContinuousWithinAt f 
s y) (h : Tendsto (fun y => fderiv Real f y) (𝓝[s] x) (𝓝 f')) : HasFDerivWithinA
t f f' (closure s) x
参数：f_diff : DifferentiableOn Real f s；s_conv : Convex Real s；s_open : IsOpen s；f
_cont : forall y in closure s, ContinuousWithinAt f s y；h : Tendsto (fun y => fd
eriv Real f y) (𝓝[s] x) (𝓝 f')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.of_notMem_closure`：HasFDerivWithinAt.of_notMem_closure
 (h : x ∉ closure s) : HasFDerivWithinAt f f' s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_closure`：closure_closure : closure (closure s) = closure s
· 使用定理 `hasFDerivWithinAt_iff_isLittleO`：hasFDerivWithinAt_iff_isLittleO : HasFD
erivWithinAt f f' s x ↔ (fun x' => f x' - f x - f' (x' - x)) =o[𝓝[s] x] (fun x' 
=> x' - x)
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.tendsto_nhdsWithin_nhds`：tendsto_nhdsWithin_nhds [PseudoMetricSpa
ce β] {f : α -> β} {a b} : Tendsto f (𝓝[s] a) (𝓝 b) ↔ forall ε > 0, exists δ > 0
, forall ⦃x : α⦄, x …
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `DifferentiableAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.uniqueDiffOn`：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 
𝕜 s
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
If a function `f` is differentiable in a convex open set and continuous on its c
losure, and its
derivative converges to a limit `f'` at a point on the boundary, then `f` is dif
ferentiable there
with derivative `f'`.
-/
theorem hasFDerivWithinAt_closure_of_tendsto_fderiv {f : E → F} {s : Set E} {x : E} {f' : E →L[ℝ] F}
    (f_diff : DifferentiableOn ℝ f s) (s_conv : Convex ℝ s) (s_open : IsOpen s)
    (f_cont : ∀ y ∈ closure s, ContinuousWithinAt f s y)
    (h : Tendsto (fun y => fderiv ℝ f y) (𝓝[s] x) (𝓝 f')) :
    HasFDerivWithinAt f f' (closure s) x := by
  -- one can assume without loss of generality that `x` belongs to the closure of `s`, as the
  -- statement is empty otherwise
  by_cases! hx : x ∉ closure s
  · rw [← closure_closure] at hx; exact HasFDerivWithinAt.of_notMem_closure hx
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  /- One needs to show that `‖f y - f x - f' (y - x)‖ ≤ ε ‖y - x‖` for `y` close to `x` in
    `closure s`, where `ε` is an arbitrary positive constant. By continuity of the functions, it
    suffices to prove this for nearby points inside `s`. In a neighborhood of `x`, the derivative
    of `f` is arbitrarily close to `f'` by assumption. The mean value inequality completes the
    proof. -/
  intro ε ε_pos
  obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ y ∈ s, dist y x < δ → ‖fderiv ℝ f y - f'‖ < ε := by
    simpa [dist_eq_norm] using tendsto_nhdsWithin_nhds.1 h ε ε_pos
  set B := ball x δ
  suffices ∀ y ∈ B ∩ closure s, ‖f y - f x - (f' y - f' x)‖ ≤ ε * ‖y - x‖ from
    mem_nhdsWithin_iff.2 ⟨δ, δ_pos, fun y hy => by simpa using this y hy⟩
  suffices
    ∀ p : E × E,
      p ∈ closure ((B ∩ s) ×ˢ (B ∩ s)) → ‖f p.2 - f p.1 - (f' p.2 - f' p.1)‖ ≤ ε * ‖p.2 - p.1‖ by
    rw [closure_prod_eq] at this
    intro y y_in
    apply this ⟨x, y⟩
    have : B ∩ closure s ⊆ closure (B ∩ s) := isOpen_ball.inter_closure
    exact ⟨this ⟨mem_ball_self δ_pos, hx⟩, this y_in⟩
  have key : ∀ p : E × E, p ∈ (B ∩ s) ×ˢ (B ∩ s) →
        ‖f p.2 - f p.1 - (f' p.2 - f' p.1)‖ ≤ ε * ‖p.2 - p.1‖ := by
    rintro ⟨u, v⟩ ⟨u_in, v_in⟩
    have conv : Convex ℝ (B ∩ s) := (convex_ball _ _).inter s_conv
    have diff : DifferentiableOn ℝ f (B ∩ s) := f_diff.mono inter_subset_right
    have bound : ∀ z ∈ B ∩ s, ‖fderivWithin ℝ f (B ∩ s) z - f'‖ ≤ ε := by
      intro z z_in
      have h := hδ z
      have : fderivWithin ℝ f (B ∩ s) z = fderiv ℝ f z := by
        have op : IsOpen (B ∩ s) := isOpen_ball.inter s_open
        rw [DifferentiableAt.fderivWithin _ (op.uniqueDiffOn z z_in)]
        exact (diff z z_in).differentiableAt (IsOpen.mem_nhds op z_in)
      rw [← this] at h
      exact le_of_lt (h z_in.2 z_in.1)
    simpa using conv.norm_image_sub_le_of_norm_fderivWithin_le' diff bound u_in v_in
  rintro ⟨u, v⟩ uv_in
  have f_cont' : ∀ y ∈ closure s, ContinuousWithinAt (f - ⇑f') s y := by
    intro y y_in
    exact Tendsto.sub (f_cont y y_in) f'.cont.continuousWithinAt
  refine ContinuousWithinAt.closure_le uv_in ?_ ?_ key
  all_goals
    -- common start for both continuity proofs
    have : (B ∩ s) ×ˢ (B ∩ s) ⊆ s ×ˢ s := by grw [inter_subset_right]
    obtain ⟨u_in, v_in⟩ : u ∈ closure s ∧ v ∈ closure s := by
      simpa [closure_prod_eq] using closure_mono this uv_in
    apply ContinuousWithinAt.mono _ this
    simp only [ContinuousWithinAt]
  · rw [nhdsWithin_prod_eq]
    have : ∀ u v, f v - f u - (f' v - f' u) = f v - f' v - (f u - f' u) := by intros; abel
    simp only [this]
    exact
      Tendsto.comp continuous_norm.continuousAt
        ((Tendsto.comp (f_cont' v v_in) tendsto_snd).sub <|
          Tendsto.comp (f_cont' u u_in) tendsto_fst)
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    rw [nhds_prod_eq]
    exact
      tendsto_const_nhds.mul
        (Tendsto.comp continuous_norm.continuousAt <| tendsto_snd.sub tendsto_fst)

/-- If a function is differentiable on the right of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the right at `a`. -/
/-
**hasDerivWithinAt_Ici_of_tendsto_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_Ici_of_tendsto_deriv {s : Set Real} {e : E} {a : Real} {f
 : Real -> E} (f_diff : DifferentiableOn Real f s) (f_lim : ContinuousWithinAt f
 s a) (hs : s in 𝓝[>] a) (f_lim' : Tendsto (fun x => deriv f x) (𝓝[>] a) (𝓝 e)) 
: HasDerivWithinAt f e (Ici a) a
参数：f_diff : DifferentiableOn Real f s；f_lim : ContinuousWithinAt f s a；hs : s in
 𝓝[>] a；f_lim' : Tendsto (fun x => deriv f x) (𝓝[>] a) (𝓝 e)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsGT_iff_exists_Ioc_subset`：mem_nhdsGT_iff_exists_Ioc_subset [NoMa
xOrder α] [DenselyOrdered α] {a : α} {s : Set α} : s in 𝓝[>] a ↔ exists u in Ioi
 a, Ioc a u subseteq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
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
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `convex_Ioo`：convex_Ioo (r s : β) : Convex 𝕜 (Ioo r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
If a function is differentiable on the right of a point `a : ℝ`, continuous at `
a`, and
its derivative also converges at `a`, then `f` is differentiable on the right at
 `a`.
-/
theorem hasDerivWithinAt_Ici_of_tendsto_deriv {s : Set ℝ} {e : E} {a : ℝ} {f : ℝ → E}
    (f_diff : DifferentiableOn ℝ f s) (f_lim : ContinuousWithinAt f s a) (hs : s ∈ 𝓝[>] a)
    (f_lim' : Tendsto (fun x => deriv f x) (𝓝[>] a) (𝓝 e)) : HasDerivWithinAt f e (Ici a) a := by
  /- This is a specialization of `hasFDerivWithinAt_closure_of_tendsto_fderiv`. To be in the
    setting of this theorem, we need to work on an open interval with closure contained in
    `s ∪ {a}`, that we call `t = (a, b)`. Then, we check all the assumptions of this theorem and
    we apply it. -/
  obtain ⟨b, ab : a < b, sab : Ioc a b ⊆ s⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hs
  let t := Ioo a b
  have ts : t ⊆ s := Subset.trans Ioo_subset_Ioc_self sab
  have t_diff : DifferentiableOn ℝ f t := f_diff.mono ts
  have t_conv : Convex ℝ t := convex_Ioo a b
  have t_open : IsOpen t := isOpen_Ioo
  have t_closure : closure t = Icc a b := closure_Ioo ab.ne
  have t_cont : ∀ y ∈ closure t, ContinuousWithinAt f t y := by
    rw [t_closure]
    intro y hy
    by_cases h : y = a
    · rw [h]; exact f_lim.mono ts
    · have : y ∈ s := sab ⟨lt_of_le_of_ne hy.1 (Ne.symm h), hy.2⟩
      exact (f_diff.continuousOn y this).mono ts
  have t_diff' : Tendsto (fun x => fderiv ℝ f x) (𝓝[t] a) (𝓝 (smulRight (1 : ℝ →L[ℝ] ℝ) e)) := by
    simp only [toSpanSingleton_deriv.symm]
    exact Tendsto.comp
      (isBoundedBilinearMap_smulRight : IsBoundedBilinearMap ℝ _).continuous_right.continuousAt
      (tendsto_nhdsWithin_mono_left Ioo_subset_Ioi_self f_lim')
  -- now we can apply `hasFDerivWithinAt_closure_of_tendsto_fderiv`
  have : HasDerivWithinAt f e (Icc a b) a := by
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← t_closure]
    exact hasFDerivWithinAt_closure_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff'
  exact this.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE ab)

/-- If a function is differentiable on the left of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the left at `a`. -/
/-
**hasDerivWithinAt_Iic_of_tendsto_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_Iic_of_tendsto_deriv {s : Set Real} {e : E} {a : Real} {f
 : Real -> E} (f_diff : DifferentiableOn Real f s) (f_lim : ContinuousWithinAt f
 s a) (hs : s in 𝓝[<] a) (f_lim' : Tendsto (fun x => deriv f x) (𝓝[<] a) (𝓝 e)) 
: HasDerivWithinAt f e (Iic a) a
参数：f_diff : DifferentiableOn Real f s；f_lim : ContinuousWithinAt f s a；hs : s in
 𝓝[<] a；f_lim' : Tendsto (fun x => deriv f x) (𝓝[<] a) (𝓝 e)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsLT_iff_exists_Ico_subset`：mem_nhdsLT_iff_exists_Ico_subset [NoMi
nOrder α] [DenselyOrdered α] {a : α} {s : Set α} : s in 𝓝[<] a ↔ exists l in Iio
 a, Ico l a subseteq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
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
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `convex_Ioo`：convex_Ioo (r s : β) : Convex 𝕜 (Ioo r s)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `closure_Ioo`：closure_Ioo {a b : α} (hab : a != b) : closure (Ioo a b) = 
Icc a b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
If a function is differentiable on the left of a point `a : ℝ`, continuous at `a
`, and
its derivative also converges at `a`, then `f` is differentiable on the left at 
`a`.
-/
theorem hasDerivWithinAt_Iic_of_tendsto_deriv {s : Set ℝ} {e : E} {a : ℝ}
    {f : ℝ → E} (f_diff : DifferentiableOn ℝ f s) (f_lim : ContinuousWithinAt f s a)
    (hs : s ∈ 𝓝[<] a) (f_lim' : Tendsto (fun x => deriv f x) (𝓝[<] a) (𝓝 e)) :
    HasDerivWithinAt f e (Iic a) a := by
  /- This is a specialization of `hasFDerivWithinAt_closure_of_tendsto_fderiv`. To be in the
    setting of this theorem, we need to work on an open interval with closure contained in
    `s ∪ {a}`, that we call `t = (b, a)`. Then, we check all the assumptions of this theorem and we
    apply it. -/
  obtain ⟨b, ba, sab⟩ : ∃ b ∈ Iio a, Ico b a ⊆ s := mem_nhdsLT_iff_exists_Ico_subset.1 hs
  let t := Ioo b a
  have ts : t ⊆ s := Subset.trans Ioo_subset_Ico_self sab
  have t_diff : DifferentiableOn ℝ f t := f_diff.mono ts
  have t_conv : Convex ℝ t := convex_Ioo b a
  have t_open : IsOpen t := isOpen_Ioo
  have t_closure : closure t = Icc b a := closure_Ioo (ne_of_lt ba)
  have t_cont : ∀ y ∈ closure t, ContinuousWithinAt f t y := by
    rw [t_closure]
    intro y hy
    by_cases h : y = a
    · rw [h]; exact f_lim.mono ts
    · have : y ∈ s := sab ⟨hy.1, lt_of_le_of_ne hy.2 h⟩
      exact (f_diff.continuousOn y this).mono ts
  have t_diff' : Tendsto (fun x => fderiv ℝ f x) (𝓝[t] a) (𝓝 (smulRight (1 : ℝ →L[ℝ] ℝ) e)) := by
    simp only [toSpanSingleton_deriv.symm]
    exact Tendsto.comp
      (isBoundedBilinearMap_smulRight : IsBoundedBilinearMap ℝ _).continuous_right.continuousAt
      (tendsto_nhdsWithin_mono_left Ioo_subset_Iio_self f_lim')
  -- now we can apply `hasFDerivWithinAt_closure_of_tendsto_fderiv`
  have : HasDerivWithinAt f e (Icc b a) a := by
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← t_closure]
    exact hasFDerivWithinAt_closure_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff'
  exact this.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE ba)

/-- If a real function `f` has a derivative `g` everywhere but at a point, and `f` and `g` are
continuous at this point, then `g` is also the derivative of `f` at this point. -/
/-
**hasDerivAt_of_hasDerivAt_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_of_hasDerivAt_of_ne {f g : Real -> E} {x : Real} (f_diff : fora
ll y != x, HasDerivAt f (g y) y) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
 : HasDerivAt f (g x) x
参数：f_diff : forall y != x, HasDerivAt f (g y) y；hf : ContinuousAt f x；hg : Conti
nuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `hasDerivWithinAt_Ici_of_tendsto_deriv`：hasDerivWithinAt_Ici_of_tendsto_d
eriv {s : Set Real} {e : E} {a : Real} {f : Real -> E} (f_diff : DifferentiableO
n Real f s) (f_lim : Contin…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.tendsto_inf_left`：tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α
} {y : Filter β} (h : Tendsto f x₁ y) : Tendsto f (x₁ ⊓ x₂) y
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `hasDerivWithinAt_Iic_of_tendsto_deriv`：hasDerivWithinAt_Iic_of_tendsto_d
eriv {s : Set Real} {e : E} {a : Real} {f : Real -> E} (f_diff : DifferentiableO
n Real f s) (f_lim : Contin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Set.Iic_union_Ici`：Iic_union_Ici : Iic a union Ici a = univ
· 使用定理 `HasDerivWithinAt.union`：HasDerivWithinAt.union (hs : HasDerivWithinAt f 
f' s x) (ht : HasDerivWithinAt f f' t x) : HasDerivWithinAt f f' (s union t) x

--- 原说明 ---
If a real function `f` has a derivative `g` everywhere but at a point, and `f` a
nd `g` are
continuous at this point, then `g` is also the derivative of `f` at this point.
-/
theorem hasDerivAt_of_hasDerivAt_of_ne {f g : ℝ → E} {x : ℝ}
    (f_diff : ∀ y ≠ x, HasDerivAt f (g y) y) (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : HasDerivAt f (g x) x := by
  have A : HasDerivWithinAt f (g x) (Ici x) x := by
    have diff : DifferentiableOn ℝ f (Ioi x) := fun y hy =>
      (f_diff y (ne_of_gt hy)).differentiableAt.differentiableWithinAt
    -- next line is the nontrivial bit of this proof, appealing to differentiability
    -- extension results.
    apply
      hasDerivWithinAt_Ici_of_tendsto_deriv diff hf.continuousWithinAt
        self_mem_nhdsWithin
    have : Tendsto g (𝓝[>] x) (𝓝 (g x)) := tendsto_inf_left hg
    apply this.congr' _
    apply mem_of_superset self_mem_nhdsWithin fun y hy => _
    intro y hy
    exact (f_diff y (ne_of_gt hy)).deriv.symm
  have B : HasDerivWithinAt f (g x) (Iic x) x := by
    have diff : DifferentiableOn ℝ f (Iio x) := fun y hy =>
      (f_diff y (ne_of_lt hy)).differentiableAt.differentiableWithinAt
    -- next line is the nontrivial bit of this proof, appealing to differentiability
    -- extension results.
    apply
      hasDerivWithinAt_Iic_of_tendsto_deriv diff hf.continuousWithinAt
        self_mem_nhdsWithin
    have : Tendsto g (𝓝[<] x) (𝓝 (g x)) := tendsto_inf_left hg
    apply this.congr' _
    apply mem_of_superset self_mem_nhdsWithin fun y hy => _
    intro y hy
    exact (f_diff y (ne_of_lt hy)).deriv.symm
  simpa using B.union A

/-- If a real function `f` has a derivative `g` everywhere but at a point, and `f` and `g` are
continuous at this point, then `g` is the derivative of `f` everywhere. -/
/-
**hasDerivAt_of_hasDerivAt_of_ne'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_of_hasDerivAt_of_ne' {f g : Real -> E} {x : Real} (f_diff : for
all y != x, HasDerivAt f (g y) y) (hf : ContinuousAt f x) (hg : ContinuousAt g x
) (y : Real) : HasDerivAt f (g y) y
参数：f_diff : forall y != x, HasDerivAt f (g y) y；hf : ContinuousAt f x；hg : Conti
nuousAt g x；y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `hasDerivAt_of_hasDerivAt_of_ne`：hasDerivAt_of_hasDerivAt_of_ne {f g : Re
al -> E} {x : Real} (f_diff : forall y != x, HasDerivAt f (g y) y) (hf : Continu
ousAt f x) (hg : Con…

--- 原说明 ---
If a real function `f` has a derivative `g` everywhere but at a point, and `f` a
nd `g` are
continuous at this point, then `g` is the derivative of `f` everywhere.
-/
theorem hasDerivAt_of_hasDerivAt_of_ne' {f g : ℝ → E} {x : ℝ}
    (f_diff : ∀ y ≠ x, HasDerivAt f (g y) y) (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) (y : ℝ) : HasDerivAt f (g y) y := by
  rcases eq_or_ne y x with (rfl | hne)
  · exact hasDerivAt_of_hasDerivAt_of_ne f_diff hf hg
  · exact f_diff y hne
