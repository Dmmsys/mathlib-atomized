/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.AsymptoticCone

/-!
# Asymptotic cones in normed spaces

In this file, we prove that the asymptotic cone of a set is non-trivial if and only if the set is
unbounded.
-/

public section

open AffineSpace Bornology Filter Topology

variable
  {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-
**AffineSpace.asymptoticNhds_le_cobounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineSpace.asymptoticNhds_le_cobounded {v : V} (hv : v != 0) : asymptotic
Nhds Real P v <= cobounded P
参数：hv : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_id'`：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <=
 y
· 使用定理 `Metric.tendsto_dist_right_atTop_iff`：tendsto_dist_right_atTop_iff (c : α
) {f : β -> α} {l : Filter β} : Tendsto (fun x => dist (f x) c) l atTop ↔ Tendst
o f l (cobounded α)
· 使用定理 `AffineSpace.asymptoticNhds_eq_smul_vadd`：asymptoticNhds_eq_smul_vadd (v 
: V) (p : P) : asymptoticNhds k P v = atTop (α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.vadd_pure`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {f :
 Filter α} {b : β}, f +ᵥ pure b = Filter.map (fun x => x +ᵥ b) f
· 使用定理 `Filter.map₂_smul`：map₂_smul : map₂ (· • ·) f g = f • g
· 使用定理 `Filter.map_prod_eq_map₂`：map_prod_eq_map₂ (m : α -> β -> γ) (f : Filter 
α) (g : Filter β) : Filter.map (fun p : α × β => m p.1 p.2) (f ×ˢ g) = map₂ m f 
g
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_vadd_left`：dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Filter.Tendsto.atTop_mul_pos`：Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC :
 0 < C) (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f 
x * g x) l atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `tendsto_norm_atTop_atTop`：tendsto_norm_atTop_atTop : Tendsto (norm : Rea
l -> Real) atTop atTop
· 使用定理 `Filter.Tendsto.fst`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : 
Filter α} {g : Filter β} {h : Filter γ} {m : α → β × γ},   Filter.Tendsto m f (g
 ×ˢ h) →…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
-/
theorem AffineSpace.asymptoticNhds_le_cobounded {v : V} (hv : v ≠ 0) :
    asymptoticNhds ℝ P v ≤ cobounded P := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [← tendsto_id', ← Metric.tendsto_dist_right_atTop_iff p,
    asymptoticNhds_eq_smul_vadd v p, vadd_pure, ← map₂_smul, ← map_prod_eq_map₂, map_map,
    tendsto_map'_iff]
  change Tendsto (fun x : ℝ × V => dist (x.1 • x.2 +ᵥ p) p) (atTop ×ˢ 𝓝 v) atTop
  simp_rw [dist_vadd_left, norm_smul]
  exact Tendsto.atTop_mul_pos (norm_pos_iff.mpr hv)
    (tendsto_norm_atTop_atTop.comp tendsto_id.fst)
    tendsto_snd.norm
/-
**asymptoticCone_subset_singleton_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_subset_singleton_of_bounded {s : Set P} (hs : IsBounded s) 
: asymptoticCone Real s subseteq {0}
参数：hs : IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `AffineSpace.asymptoticNhds_le_cobounded`：AffineSpace.asymptoticNhds_le_c
obounded {v : V} (hv : v != 0) : asymptoticNhds Real P v <= cobounded P
-/
theorem asymptoticCone_subset_singleton_of_bounded {s : Set P} (hs : IsBounded s) :
    asymptoticCone ℝ s ⊆ {0} := by
  intro v h
  by_contra! hv
  exact h (asymptoticNhds_le_cobounded hv hs)

variable [FiniteDimensional ℝ V]
/-
**AffineSpace.cobounded_eq_iSup_sphere_asymptoticNhds** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：AffineSpace.cobounded_eq_iSup_sphere_asymptoticNhds : cobounded P = ⨆ v in
 Metric.sphere 0 1, asymptoticNhds Real P v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `isCompact_sphere`：isCompact_sphere {α : Type*} [PseudoMetricSpace α] [Pr
operSpace α] (x : α) (r : Real) : IsCompact (sphere x r)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.comap_dist_left_atTop`：comap_dist_left_atTop (c : α) : comap (dis
t c) atTop = cobounded α
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.iInter_mem_sets`：∀ {α : Type u} {f : Filter α} {β : Type v} {s : 
β → Set α} (is : Finset β), ⋂ i ∈ is, s i ∈ f ↔ ∀ i ∈ is, s i ∈ f
· 使用定理 `mem_sphere_zero_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E]
 {a : E} {r : ℝ}, a ∈ Metric.sphere 0 r ↔ ‖a‖ = r
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.smul_mem_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
: Set α} {t : Set β} {a : α} {b : β}, a ∈ s → b ∈ t → a • b ∈ s • t
（共 48 条，此处仅展示前 30 条）
-/
theorem AffineSpace.cobounded_eq_iSup_sphere_asymptoticNhds :
    cobounded P = ⨆ v ∈ Metric.sphere 0 1, asymptoticNhds ℝ P v := by
  refine le_antisymm ?_ <| iSup₂_le fun _ h => asymptoticNhds_le_cobounded <|
    Metric.ne_of_mem_sphere h one_ne_zero
  intro s hs
  have ⟨p⟩ : Nonempty P := inferInstance
  simp_rw [mem_iSup, asymptoticNhds_eq_smul_vadd _ p, vadd_pure] at hs
  choose! t ht u hu smul_subset_s using hs
  have ⟨cover, h₁, h₂⟩ := (isCompact_sphere 0 1).elim_nhds_subcover u hu
  rw [← Metric.comap_dist_left_atTop p]
  refine ⟨Set.Ioi 0 ∩ ⋂ x ∈ cover, t x, inter_mem (Ioi_mem_atTop 0)
    (cover.iInter_mem_sets.mpr fun x hx => ht x (h₁ x hx)), fun x hx => ?_⟩
  rw [Set.mem_preimage, dist_eq_norm_vsub'] at hx
  let x' := ‖x -ᵥ p‖⁻¹ • (x -ᵥ p)
  have x'_mem : x' ∈ Metric.sphere 0 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx.1.ne']
  have ⟨y, y_mem, hy⟩ := Set.mem_iUnion₂.mp (h₂ x'_mem)
  rw [← vsub_vadd x p, ← show ‖x -ᵥ p‖ • x' = x -ᵥ p from smul_inv_smul₀ hx.1.ne' (x -ᵥ p)]
  exact smul_subset_s y (h₁ y y_mem) <| Set.smul_mem_smul (Set.biInter_subset_of_mem y_mem hx.2) hy

/-- In a finite dimensional normed affine space over `ℝ`, a set is bounded if and only if its
asymptotic cone is trivial. -/
/-
**isBounded_iff_asymptoticCone_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBounded_iff_asymptoticCone_subset_singleton {s : Set P} : IsBounded s ↔ 
asymptoticCone Real s subseteq {0}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `asymptoticCone_subset_singleton_of_bounded`：asymptoticCone_subset_single
ton_of_bounded {s : Set P} (hs : IsBounded s) : asymptoticCone Real s subseteq {
0}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSpace.cobounded_eq_iSup_sphere_asymptoticNhds`：AffineSpace.cobound
ed_eq_iSup_sphere_asymptoticNhds : cobounded P = ⨆ v in Metric.sphere 0 1, asymp
toticNhds Real P v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Metric.ne_of_mem_sphere`：ne_of_mem_sphere (h : y in sphere x ε) (hε : ε 
!= 0) : y != x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
In a finite dimensional normed affine space over `ℝ`, a set is bounded if and on
ly if its
asymptotic cone is trivial.
-/
theorem isBounded_iff_asymptoticCone_subset_singleton {s : Set P} :
    IsBounded s ↔ asymptoticCone ℝ s ⊆ {0} := by
  refine ⟨asymptoticCone_subset_singleton_of_bounded, fun h => ?_⟩
  simp_rw [isBounded_def, cobounded_eq_iSup_sphere_asymptoticNhds, mem_iSup]
  intro v hv
  by_contra h'
  exact Metric.ne_of_mem_sphere hv one_ne_zero (h h')

/-- In a finite dimensional normed affine space over `ℝ`, a set is unbounded if and only if its
asymptotic cone contains a nonzero vector. -/
/-
**not_bounded_iff_exists_ne_zero_mem_asymptoticCone** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：not_bounded_iff_exists_ne_zero_mem_asymptoticCone {s : Set P} : ¬ IsBounde
d s ↔ exists v != 0, v in asymptoticCone Real s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isBounded_iff_asymptoticCone_subset_singleton`：isBounded_iff_asymptoticC
one_subset_singleton {s : Set P} : IsBounded s ↔ asymptoticCone Real s subseteq 
{0}
· 使用定理 `Set.subset_singleton_iff`：subset_singleton_iff {α : Type*} {s : Set α} {
x : α} : s subseteq {x} ↔ forall y in s, y = x
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_imp_iff_and_not`：∀ {a b : Prop} [Decidable a], ¬(a → b) ↔ 
a ∧ ¬b

--- 原说明 ---
In a finite dimensional normed affine space over `ℝ`, a set is unbounded if and 
only if its
asymptotic cone contains a nonzero vector.
-/
theorem not_bounded_iff_exists_ne_zero_mem_asymptoticCone {s : Set P} :
    ¬ IsBounded s ↔ ∃ v ≠ 0, v ∈ asymptoticCone ℝ s := by
  rw [isBounded_iff_asymptoticCone_subset_singleton, Set.subset_singleton_iff, not_forall]
  tauto
