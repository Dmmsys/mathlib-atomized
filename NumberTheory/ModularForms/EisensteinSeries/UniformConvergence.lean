/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# Uniform convergence of Eisenstein series

We show that the sum of `eisSummand` converges locally uniformly on `ℍ` to the Eisenstein series
of weight `k` and level `Γ(N)` with congruence condition `a : Fin 2 → ZMod N`.

## Outline of argument

The key lemma `r_mul_max_le` shows that, for `z ∈ ℍ` and `c, d ∈ ℤ` (not both zero),
`|c z + d|` is bounded below by `r z * max (|c|, |d|)`, where `r z` is an explicit function of `z`
(independent of `c, d`) satisfying `0 < r z < 1` for all `z`.

We then show in `summable_one_div_rpow_max` that the sum of `max (|c|, |d|) ^ (-k)` over
`(c, d) ∈ ℤ × ℤ` is convergent for `2 < k`. This is proved by decomposing `ℤ × ℤ` using the
`Finset.box` lemmas.
-/

public section

noncomputable section

open Complex UpperHalfPlane Set Finset CongruenceSubgroup Topology

open scoped UpperHalfPlane

variable (z : ℍ)

namespace EisensteinSeries

/-- The sum defining the Eisenstein series (of weight `k` and level `Γ(N)` with congruence
condition `a : Fin 2 → ZMod N`) converges locally uniformly on `ℍ`. -/
/-
**EisensteinSeries.eisensteinSeries_tendstoLocallyUniformly** 是 Mathlib 中的一个定理，位
于命名空间 `EisensteinSeries`。
形式化陈述：eisensteinSeries_tendstoLocallyUniformly {k : Int} (hk : 3 <= k) {N : Nat}
 (a : Fin 2 -> ZMod N) : TendstoLocallyUniformly (fun (s : Finset (gammaSet N 1 
a)) => (∑ x in s, eisSummand k x ·)) (eisensteinSeries a k ·) Filter.atTop
参数：hk : 3 <= k；a : Fin 2 -> ZMod N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Summable.subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α
] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace α
], Sum…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用引理 `EisensteinSeries.summable_one_div_norm_rpow`：summable_one_div_norm_rpow 
{k : Real} (hk : 2 < k) : Summable fun (x : Fin 2 -> Int) => ‖x‖ ^ (-k)
· 使用定理 `UpperHalfPlane.instLocallyCompactSpace`：LocallyCompactSpace UpperHalfPla
ne
· 使用引理 `UpperHalfPlane.subset_verticalStrip_of_isCompact`：subset_verticalStrip_o
f_isCompact {K : Set ℍ} (hK : IsCompact K) : exists A B : Real, 0 < B ∧ K subset
eq verticalStrip A B
· 使用定理 `TendstoUniformlyOn.mono`：TendstoUniformlyOn.mono (h : TendstoUniformlyOn
 F f p s) (h' : s' subseteq s) : TendstoUniformlyOn F f p s'
· 使用定理 `tendstoUniformlyOn_tsum`：tendstoUniformlyOn_tsum {f : α -> β -> F} (hu :
 Summable u) {s : Set β} (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : TendstoU
niformlyOn (f…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用引理 `EisensteinSeries.summand_bound_of_mem_verticalStrip`：summand_bound_of_me
m_verticalStrip {k : Real} (hk : 0 <= k) (x : Fin 2 -> Int) {A B : Real} (hB : 0
 < B) (hz : z in verticalStrip A B) : ‖x …
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The sum defining the Eisenstein series (of weight `k` and level `Γ(N)` with cong
ruence
condition `a : Fin 2 → ZMod N`) converges locally uniformly on `ℍ`.
-/
theorem eisensteinSeries_tendstoLocallyUniformly {k : ℤ} (hk : 3 ≤ k) {N : ℕ} (a : Fin 2 → ZMod N) :
    TendstoLocallyUniformly (fun (s : Finset (gammaSet N 1 a)) ↦ (∑ x ∈ s, eisSummand k x ·))
      (eisensteinSeries a k ·) Filter.atTop := by
  have hk' : (2 : ℝ) < k := by norm_cast
  have p_sum : Summable fun x : gammaSet N 1 a ↦ ‖x.val‖ ^ (-k) :=
    mod_cast (summable_one_div_norm_rpow hk').subtype (· ∈ gammaSet N 1 a)
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, eisensteinSeries]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  refine (tendstoUniformlyOn_tsum (hu := p_sum.mul_left <| r ⟨⟨A, B⟩, hB⟩ ^ (-k : ℝ))
    (fun p z hz ↦ ?_)).mono HABK
  simpa only [eisSummand, one_div, ← zpow_neg, norm_zpow, ← Real.rpow_intCast,
    Int.cast_neg] using summand_bound_of_mem_verticalStrip (by positivity) p hB hz

/-- Variant of `eisensteinSeries_tendstoLocallyUniformly` formulated with maps `ℂ → ℂ`, which is
nice to have for holomorphicity later. -/
/-
**EisensteinSeries.eisensteinSeries_tendstoLocallyUniformlyOn** 是 Mathlib 中的一个引理
，位于命名空间 `EisensteinSeries`。
形式化陈述：eisensteinSeries_tendstoLocallyUniformlyOn {k : Int} {N : Nat} (hk : 3 <= 
k) (a : Fin 2 -> ZMod N) : TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet 
N 1 a)) => ↑ₕ(fun (z : ℍ) => ∑ x in s, eisSummand k x z)) (↑ₕ(eisensteinSeriesSI
F a k)) Filter.atTop {z : Complex | 0 < z.im}
参数：hk : 3 <= k；a : Fin 2 -> ZMod N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UpperHalfPlane.upperHalfPlaneSet.eq_1`：UpperHalfPlane.upperHalfPlaneSet 
= {z | 0 < z.im}
· 使用定理 `UpperHalfPlane.range_coe`：range_coe : Set.range UpperHalfPlane.coe = ℍₒ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `TendstoLocallyUniformlyOn.comp`：TendstoLocallyUniformlyOn.comp [Topologi
calSpace γ] {t : Set γ} (h : TendstoLocallyUniformlyOn F f p s) (g : γ -> α) (hg
 : MapsTo g t s) (cg…
· 使用定理 `UpperHalfPlane.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbeddin
g ((↑) : ℍ -> Complex)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `EisensteinSeries.eisensteinSeries_tendstoLocallyUniformly`：eisensteinSer
ies_tendstoLocallyUniformly {k : Int} (hk : 3 <= k) {N : Nat} (a : Fin 2 -> ZMod
 N) : TendstoLocallyUniformly (fun (s : Finset …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target`：∀ {X : Type u_1
} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : 
X → Y)   (h : Topology.IsOpenEmbedding f) [in…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `OpenPartialHomeomorph.continuousOn_symm`：continuousOn_symm : ContinuousO
n e.symm e.target

--- 原说明 ---
Variant of `eisensteinSeries_tendstoLocallyUniformly` formulated with maps `ℂ → 
ℂ`, which is
nice to have for holomorphicity later.
-/
lemma eisensteinSeries_tendstoLocallyUniformlyOn {k : ℤ} {N : ℕ} (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) : TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet N 1 a)) ↦
      ↑ₕ(fun (z : ℍ) ↦ ∑ x ∈ s, eisSummand k x z)) (↑ₕ(eisensteinSeriesSIF a k))
          Filter.atTop {z : ℂ | 0 < z.im} := by
  rw [← upperHalfPlaneSet, ← range_coe, ← image_univ]
  apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (OpenPartialHomeomorph.continuousOn_symm _)
  · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
    apply eisensteinSeries_tendstoLocallyUniformly hk
  · simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.top_eq_univ, mapsTo_range_iff,
    Set.mem_univ, forall_const]

end EisensteinSeries

