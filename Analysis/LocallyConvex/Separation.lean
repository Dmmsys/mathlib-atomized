/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.RCLike.Extend
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Separation Hahn-Banach theorem

In this file we prove the geometric Hahn-Banach theorem. For any two disjoint convex sets, there
exists a continuous linear functional separating them, geometrically meaning that we can intercalate
a plane between them.

We provide many variations to stricten the result under more assumptions on the convex sets:
* `geometric_hahn_banach_open`: One set is open. Weak separation.
* `geometric_hahn_banach_open_point`, `geometric_hahn_banach_point_open`: One set is open, the
  other is a singleton. Weak separation.
* `geometric_hahn_banach_open_open`: Both sets are open. Semistrict separation.
* `geometric_hahn_banach_of_nonempty_interior'`: One set has nonempty interior. Nonstrict
  separation.
* `geometric_hahn_banach_of_nonempty_interior`: One set has nonempty interior, the other one is
  nonempty. Nonstrict separation by a nonzero functional.
* `geometric_hahn_banach_of_nonempty_interior_point`: One set has nonempty interior, the other one
  is a singleton outside this interior. Nonstrict separation, with the maximum attained at the
  singleton.
* `geometric_hahn_banach_compact_closed`, `geometric_hahn_banach_closed_compact`: One set is closed,
  the other one is compact. Strict separation.
* `geometric_hahn_banach_point_closed`, `geometric_hahn_banach_closed_point`: One set is closed, the
  other one is a singleton. Strict separation.
* `geometric_hahn_banach_point_point`: Both sets are singletons. Strict separation.
-/

public section

assert_not_exists ContinuousLinearMap.hasOpNorm

open Set

open scoped Pointwise

variable {𝕜 E : Type*}

set_option backward.isDefEq.respectTransparency false in
/-- Given a set `s` which is a convex neighbourhood of `0` and a point `x₀` outside of it, there is
a continuous linear functional `f` separating `x₀` and `s`, in the sense that it sends `x₀` to 1 and
all of `s` to values strictly below `1`. -/
/-
**separate_convex_open_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separate_convex_open_set [TopologicalSpace E] [AddCommGroup E] [IsTopologi
calAddGroup E] [Module Real E] [ContinuousSMul Real E] {s : Set E} (hs₀ : (0 : E
) in s) (hs₁ : Convex Real s) (hs₂ : IsOpen s) {x₀ : E} (hx₀ : x₀ ∉ s) : exists 
f : StrongDual Real E, f x₀ = 1 ∧ forall x in s, f x < 1
参数：hs₀ : (0 : E) in s；hs₁ : Convex Real s；hs₂ : IsOpen s；hx₀ : x₀ ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `exists_extension_of_le_sublinear`：exists_extension_of_le_sublinear (f : 
E ->ₗ.[Real] Real) (N : E -> Real) (N_hom : forall c : Real, 0 < c -> forall x, 
N (c • x) = c * N x) (…
· 使用定理 `gauge_smul_of_nonneg`：gauge_smul_of_nonneg [MulActionWithZero α E] [IsSc
alarTower α Real (Set E)] {s : Set E} {a : α} (ha : 0 <= a) (x : E) : gauge s (a
 • x) = a …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `gauge_add_le`：gauge_add_le (hs : Convex Real s) (absorbs : Absorbent Rea
l s) (x y : E) : gauge s (x + y) <= gauge s x + gauge s y
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.mkSpanSingleton'_apply`：∀ {R : Type u_1} {S : Type u_2} [inst
 : Ring R] [inst_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup
 E]   [inst_3 : _root_.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `gauge_nonneg`：gauge_nonneg (x : E) : 0 <= gauge s x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用引理 `le_mul_iff_one_le_right`：le_mul_iff_one_le_right [PosMulMono α] [PosMulR
eflectLE α] (a0 : 0 < a) : a <= a * b ↔ 1 <= b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `one_le_gauge_of_notMem`：one_le_gauge_of_notMem (hs₁ : StarConvex Real 0 
s) (hs₂ : Absorbs Real s {x}) (hx : x ∉ s) : 1 <= gauge s x
· 使用定理 `Convex.starConvex`：Convex.starConvex (hs : Convex 𝕜 s) (hx : x in s) : S
tarConvex 𝕜 x s
· 使用定理 `Absorbent.absorbs`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] 
[inst_1 : SMul M α] {s : Set α},   Absorbent M s → ∀ {x : α}, Absorbs M s {x}
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.coe_mk`：coe_mk (x : M) (hx : x in p) : ((⟨x, hx⟩ : p) : M) = x
（共 81 条，此处仅展示前 30 条）

--- 原说明 ---
Given a set `s` which is a convex neighbourhood of `0` and a point `x₀` outside 
of it, there is
a continuous linear functional `f` separating `x₀` and `s`, in the sense that it
 sends `x₀` to 1 and
all of `s` to values strictly below `1`.
-/
theorem separate_convex_open_set [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E] {s : Set E} (hs₀ : (0 : E) ∈ s) (hs₁ : Convex ℝ s)
    (hs₂ : IsOpen s) {x₀ : E} (hx₀ : x₀ ∉ s) :
    ∃ f : StrongDual ℝ E, f x₀ = 1 ∧ ∀ x ∈ s, f x < 1 := by
  let f : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton x₀ 1 (ne_of_mem_of_not_mem hs₀ hx₀).symm
  have := exists_extension_of_le_sublinear f (gauge s) (fun c hc => gauge_smul_of_nonneg hc.le)
    (gauge_add_le hs₁ <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀) ?_
  · obtain ⟨φ, hφ₁, hφ₂⟩ := this
    have hφ₃ : φ x₀ = 1 := by
      rw [← f.domain.coe_mk x₀ (Submodule.mem_span_singleton_self _), hφ₁,
        LinearPMap.mkSpanSingleton'_apply_self]
    have hφ₄ : ∀ x ∈ s, φ x < 1 := fun x hx =>
      (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_isOpen hs₂ hx)
    refine ⟨⟨φ, ?_⟩, hφ₃, hφ₄⟩
    refine
      φ.continuous_of_nonzero_on_open _ (hs₂.vadd (-x₀)) (Nonempty.vadd_set ⟨0, hs₀⟩)
        (vadd_set_subset_iff.mpr fun x hx => ?_)
    change φ (-x₀ + x) ≠ 0
    rw [map_add, map_neg]
    specialize hφ₄ x hx
    linarith
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [LinearPMap.mkSpanSingleton'_apply]
  simp only [mul_one, smul_eq_mul]
  obtain h | h := le_or_gt y 0
  · exact h.trans (gauge_nonneg _)
  · rw [gauge_smul_of_nonneg h.le, smul_eq_mul, RingHom.id_apply, le_mul_iff_one_le_right h]
    exact
      one_le_gauge_of_notMem (hs₁.starConvex hs₀)
        (absorbent_nhds_zero <| hs₂.mem_nhds hs₀).absorbs hx₀

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {s t : Set E} {x y : E}
section

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is open,
there is a continuous linear functional which separates them. -/
/-
**geometric_hahn_banach_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_open (hs₁ : Convex Real s) (hs₂ : IsOpen s) (ht : Co
nvex Real t) (disj : Disjoint s t) : exists (f : StrongDual Real E) (u : Real), 
(forall a in s, f a < u) ∧ forall b in t, u <= f b
参数：hs₁ : Convex Real s；hs₂ : IsOpen s；ht : Convex Real t；disj : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.sub_mem_sub`：∀ {α : Type u_2} [inst : Sub α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a - b ∈ s - t
· 使用定理 `sub_add_sub_cancel'`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G
), a - b + (c - a) = c - b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Convex.vadd`：Convex.vadd (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 (z +ᵥ s)
· 使用定理 `Convex.sub`：Convex.sub (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s
 - t)
· 使用定理 `Disjoint.zero_notMem_sub_set`：∀ {α : Type u_2} [inst : AddGroup α] {s t 
: Set α}, Disjoint s t → 0 ∉ s - t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.vadd_mem_vadd_set_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGr
oup α] [inst_1 : AddAction α β] {s : Set β} {a : α} {x : β},   a +ᵥ x ∈ a +ᵥ s ↔
 x ∈ s
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `separate_convex_open_set`：separate_convex_open_set [TopologicalSpace E] 
[AddCommGroup E] [IsTopologicalAddGroup E] [Module Real E] [ContinuousSMul Real 
E] {s : Set E}…
· 使用定理 `IsOpen.vadd`：∀ {α : Type u_2} {G : Type u_4} [inst : TopologicalSpace α]
 [inst_1 : AddGroup G] [inst_2 : AddAction G α]   [ContinuousConstVAdd G α] {s :
 …
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` wh
ere `s` is open,
there is a continuous linear functional which separates them.
-/
theorem geometric_hahn_banach_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht : Convex ℝ t)
    (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u ≤ f b := by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, 0, by simp, fun b _hb => le_rfl⟩
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact ⟨0, 1, fun a _ha => zero_lt_one, by simp⟩
  let x₀ := b₀ - a₀
  let C := x₀ +ᵥ (s - t)
  have : (0 : E) ∈ C :=
    ⟨a₀ - b₀, sub_mem_sub ha₀ hb₀, by simp_rw [x₀, vadd_eq_add, sub_add_sub_cancel', sub_self]⟩
  have : Convex ℝ C := (hs₁.sub ht).vadd _
  have : x₀ ∉ C := by
    intro hx₀
    rw [← add_zero x₀] at hx₀
    exact disj.zero_notMem_sub_set (vadd_mem_vadd_set_iff.1 hx₀)
  obtain ⟨f, hf₁, hf₂⟩ := separate_convex_open_set ‹0 ∈ C› ‹_› (hs₂.sub_right.vadd _) ‹x₀ ∉ C›
  have forall_le : ∀ a ∈ s, ∀ b ∈ t, f a ≤ f b := by
    intro a ha b hb
    have := hf₂ (x₀ + (a - b)) (vadd_mem_vadd_set <| sub_mem_sub ha hb)
    simp only [f.map_add, f.map_sub, hf₁] at this
    linarith
  refine ⟨f, sInf (f '' t), image_subset_iff.1 (?_ : f '' s ⊆ Iio (sInf (f '' t))), fun b hb => ?_⟩
  · rw [← interior_Iic]
    refine interior_maximal (image_subset_iff.2 fun a ha => ?_) (f.isOpenMap_of_ne_zero ?_ _ hs₂)
    · exact le_csInf (Nonempty.image _ ⟨_, hb₀⟩) (forall_mem_image.2 <| forall_le _ ha)
    · rintro rfl
      simp at hf₁
  · exact csInf_le ⟨f a₀, forall_mem_image.2 <| forall_le _ ha₀⟩ (mem_image_of_mem _ hb)
/-
**geometric_hahn_banach_open_point** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_open_point (hs₁ : Convex Real s) (hs₂ : IsOpen s) (d
isj : x ∉ s) : exists f : StrongDual Real E, forall a in s, f a < f x
参数：hs₁ : Convex Real s；hs₂ : IsOpen s；disj : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `geometric_hahn_banach_open`：geometric_hahn_banach_open (hs₁ : Convex Rea
l s) (hs₂ : IsOpen s) (ht : Convex Real t) (disj : Disjoint s t) : exists (f : S
trongDual Real E…
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem geometric_hahn_banach_open_point (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (disj : x ∉ s) :
    ∃ f : StrongDual ℝ E, ∀ a ∈ s, f a < f x :=
  let ⟨f, _s, hs, hx⟩ :=
    geometric_hahn_banach_open hs₁ hs₂ (convex_singleton x) (disjoint_singleton_right.2 disj)
  ⟨f, fun a ha => lt_of_lt_of_le (hs a ha) (hx x (mem_singleton _))⟩
/-
**geometric_hahn_banach_point_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_point_open (ht₁ : Convex Real t) (ht₂ : IsOpen t) (d
isj : x ∉ t) : exists f : StrongDual Real E, forall b in t, f x < f b
参数：ht₁ : Convex Real t；ht₂ : IsOpen t；disj : x ∉ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `geometric_hahn_banach_open_point`：geometric_hahn_banach_open_point (hs₁ 
: Convex Real s) (hs₂ : IsOpen s) (disj : x ∉ s) : exists f : StrongDual Real E,
 forall a in s, f a < …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem geometric_hahn_banach_point_open (ht₁ : Convex ℝ t) (ht₂ : IsOpen t) (disj : x ∉ t) :
    ∃ f : StrongDual ℝ E, ∀ b ∈ t, f x < f b :=
  let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by simpa⟩
/-
**geometric_hahn_banach_open_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_open_open (hs₁ : Convex Real s) (hs₂ : IsOpen s) (ht
₁ : Convex Real t) (ht₃ : IsOpen t) (disj : Disjoint s t) : exists (f : StrongDu
al Real E) (u : Real), (forall a in s, f a < u) ∧ forall b in t, u < f b
参数：hs₁ : Convex Real s；hs₂ : IsOpen s；ht₁ : Convex Real t；ht₃ : IsOpen t；disj : 
Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `geometric_hahn_banach_open`：geometric_hahn_banach_open (hs₁ : Convex Rea
l s) (hs₂ : IsOpen s) (ht : Convex Real t) (disj : Disjoint s t) : exists (f : S
trongDual Real E…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `interior_Ici`：interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = I
oi a
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
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearMap.isOpenMap_of_ne_zero`：∀ {R : Type u_1} {M : Type u_2
} [inst : TopologicalSpace R] [inst_1 : DivisionRing R] [ContinuousSub R]   [ins
t_3 : AddCommGroup M] [inst_4 …
（共 34 条，此处仅展示前 30 条）
-/
theorem geometric_hahn_banach_open_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht₁ : Convex ℝ t)
    (ht₃ : IsOpen t) (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ ∀ b ∈ t, u < f b := by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact ⟨0, -1, by simp, fun b _hb => by simp⟩
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact ⟨0, 1, fun a _ha => by simp, by simp⟩
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open hs₁ hs₂ ht₁ disj
  refine ⟨f, s, hf₁, image_subset_iff.1 (?_ : f '' t ⊆ Ioi s)⟩
  rw [← interior_Ici]
  refine interior_maximal (image_subset_iff.2 hf₂) (f.isOpenMap_of_ne_zero ?_ _ ht₃)
  rintro rfl
  simp_rw [zero_apply] at hf₁ hf₂
  exact (hf₁ _ ha₀).not_ge (hf₂ _ hb₀)

/-- If `s` and `t` are convex, `interior s` is nonempty and disjoint from `t`, then a nonzero
continuous linear functional weakly separates `s` and `t`. The proof first separates `interior s`
from `t`, then extends the inequality from `interior s` to all of `s` using
`closure (interior s) = closure s`. -/
/-
**geometric_hahn_banach_of_nonempty_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_of_nonempty_interior (hs : Convex Real s) (ht : Conv
ex Real t) (hst : Disjoint (interior s) t) (hsint : (interior s).Nonempty) (htne
 : t.Nonempty) : exists (f : StrongDual Real E) (u : Real), f != 0 ∧ (forall a i
n s, f a <= u) ∧ forall b in t, u <= f b
参数：hs : Convex Real s；ht : Convex Real t；hst : Disjoint (interior s) t；hsint : (
interior s).Nonempty；htne : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `geometric_hahn_banach_open`：geometric_hahn_banach_open (hs₁ : Convex Rea
l s) (hs₂ : IsOpen s) (ht : Convex Real t) (disj : Disjoint s t) : exists (f : S
trongDual Real E…
· 使用定理 `Convex.interior`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_
1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [in
st_4 …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` and `t` are convex, `interior s` is nonempty and disjoint from `t`, then 
a nonzero
continuous linear functional weakly separates `s` and `t`. The proof first separ
ates `interior s`
from `t`, then extends the inequality from `interior s` to all of `s` using
`closure (interior s) = closure s`.
-/
theorem geometric_hahn_banach_of_nonempty_interior
  (hs : Convex ℝ s) (ht : Convex ℝ t) (hst : Disjoint (interior s) t)
    (hsint : (interior s).Nonempty) (htne : t.Nonempty) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), f ≠ 0 ∧ (∀ a ∈ s, f a ≤ u) ∧ ∀ b ∈ t, u ≤ f b := by
  obtain ⟨f, u, hfA, hfB⟩ :=
    geometric_hahn_banach_open hs.interior isOpen_interior ht hst
  refine ⟨f, u, ?_, fun a ha ↦ ?_, hfB⟩
  · obtain ⟨a, ha⟩ := hsint
    obtain ⟨b, hb⟩ := htne
    intro hzero
    have ha' : (0 : ℝ) < u := by simpa [hzero] using hfA a ha
    have hb' : u ≤ (0 : ℝ) := by simpa [hzero] using hfB b hb
    linarith
  · apply closure_minimal (fun x hx => le_of_lt (hfA x hx)) <| isClosed_Iic.preimage f.continuous
    simpa [hs.closure_interior_eq_closure_of_nonempty_interior hsint] using subset_closure ha

/-- If `s` and `t` are convex, `interior s` is nonempty and disjoint from `t`, then a continuous
linear functional weakly separates `s` and `t`. If `t` is nonempty, this follows from
`geometric_hahn_banach_of_nonempty_interior`; if `t = ∅`, the zero functional works. -/
/-
**geometric_hahn_banach_of_nonempty_interior'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_of_nonempty_interior' (hs : Convex Real s) (ht : Con
vex Real t) (hst : Disjoint (interior s) t) (hsint : (interior s).Nonempty) : ex
ists (f : StrongDual Real E) (u : Real), (forall a in s, f a <= u) ∧ forall b in
 t, u <= f b
参数：hs : Convex Real s；ht : Convex Real t；hst : Disjoint (interior s) t；hsint : (
interior s).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `geometric_hahn_banach_of_nonempty_interior`：geometric_hahn_banach_of_non
empty_interior (hs : Convex Real s) (ht : Convex Real t) (hst : Disjoint (interi
or s) t) (hsint : (interior s).N…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
If `s` and `t` are convex, `interior s` is nonempty and disjoint from `t`, then 
a continuous
linear functional weakly separates `s` and `t`. If `t` is nonempty, this follows
 from
`geometric_hahn_banach_of_nonempty_interior`; if `t = ∅`, the zero functional wo
rks.
-/
theorem geometric_hahn_banach_of_nonempty_interior'
  (hs : Convex ℝ s) (ht : Convex ℝ t) (hst : Disjoint (interior s) t)
    (hsint : (interior s).Nonempty) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a ≤ u) ∧ ∀ b ∈ t, u ≤ f b := by
  by_cases htne : t.Nonempty
  · obtain ⟨f, u, -, hs', ht'⟩ :=
      geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
    exact ⟨f, u, hs', ht'⟩
  · exact ⟨0, 0, by simp⟩

/-- If `A` is convex with nonempty interior and `x ∉ interior A`, then there is a nonzero
continuous linear functional whose maximum on `A` is attained at `x`. -/
/-
**geometric_hahn_banach_of_nonempty_interior_point** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_of_nonempty_interior_point {A : Set E} (hA : Convex 
Real A) (hxA : x ∉ interior A) (hAint : (interior A).Nonempty) : exists f : Stro
ngDual Real E, f != 0 ∧ forall a in A, f a <= f x
参数：hA : Convex Real A；hxA : x ∉ interior A；hAint : (interior A).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `geometric_hahn_banach_of_nonempty_interior`：geometric_hahn_banach_of_non
empty_interior (hs : Convex Real s) (ht : Convex Real t) (hst : Disjoint (interi
or s) t) (hsint : (interior s).N…
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
If `A` is convex with nonempty interior and `x ∉ interior A`, then there is a no
nzero
continuous linear functional whose maximum on `A` is attained at `x`.
-/
theorem geometric_hahn_banach_of_nonempty_interior_point
    {A : Set E} (hA : Convex ℝ A) (hxA : x ∉ interior A) (hAint : (interior A).Nonempty) :
    ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∀ a ∈ A, f a ≤ f x := by
  obtain ⟨f, u, hfne, hA', hx'⟩ :=
    geometric_hahn_banach_of_nonempty_interior hA (convex_singleton x)
      (disjoint_singleton_right.2 hxA) hAint (singleton_nonempty x)
  exact ⟨f, hfne, fun a ha => (hA' a ha).trans (hx' x (mem_singleton _))⟩

variable [LocallyConvexSpace ℝ E]

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
compact and `t` is closed, there is a continuous linear functional which strongly separates them. -/
/-
**geometric_hahn_banach_compact_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_compact_closed (hs₁ : Convex Real s) (hs₂ : IsCompac
t s) (ht₁ : Convex Real t) (ht₂ : IsClosed t) (disj : Disjoint s t) : exists (f 
: StrongDual Real E) (u v : Real), (forall a in s, f a < u) ∧ u < v ∧ forall b i
n t, v < f b
参数：hs₁ : Convex Real s；hs₂ : IsCompact s；ht₁ : Convex Real t；ht₂ : IsClosed t；di
sj : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.exists_open_convexes`：Disjoint.exists_open_convexes (disj : Dis
joint s t) (hs₁ : Convex 𝕜 s) (hs₂ : IsCompact s) (ht₁ : Convex 𝕜 t) (ht₂ : IsCl
osed t) : exists u …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `geometric_hahn_banach_open_open`：geometric_hahn_banach_open_open (hs₁ : 
Convex Real s) (hs₂ : IsOpen s) (ht₁ : Convex Real t) (ht₃ : IsOpen t) (disj : D
isjoint s t) : exists…
（共 91 条，此处仅展示前 30 条）

--- 原说明 ---
A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` wh
ere `s` is
compact and `t` is closed, there is a continuous linear functional which strongl
y separates them.
-/
theorem geometric_hahn_banach_compact_closed (hs₁ : Convex ℝ s) (hs₂ : IsCompact s)
    (ht₁ : Convex ℝ t) (ht₂ : IsClosed t) (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact ⟨0, -2, -1, by simp⟩
  obtain rfl | _ht := t.eq_empty_or_nonempty
  · exact ⟨0, 1, 2, by simp⟩
  obtain ⟨U, V, hU, hV, hU₁, hV₁, sU, tV, disj'⟩ := disj.exists_open_convexes hs₁ hs₂ ht₁ ht₂
  obtain ⟨f, u, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj'
  obtain ⟨x, hx₁, hx₂⟩ := hs₂.exists_isMaxOn hs f.continuous.continuousOn
  have : f x < u := hf₁ x (sU hx₁)
  exact
    ⟨f, (f x + u) / 2, u,
      fun a ha => by have := hx₂ ha; dsimp at this; linarith,
      by linarith,
      fun b hb => hf₂ b (tV hb)⟩

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
closed, and `t` is compact, there is a continuous linear functional which strongly separates them.
-/
/-
**geometric_hahn_banach_closed_compact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_closed_compact (hs₁ : Convex Real s) (hs₂ : IsClosed
 s) (ht₁ : Convex Real t) (ht₂ : IsCompact t) (disj : Disjoint s t) : exists (f 
: StrongDual Real E) (u v : Real), (forall a in s, f a < u) ∧ u < v ∧ forall b i
n t, v < f b
参数：hs₁ : Convex Real s；hs₂ : IsClosed s；ht₁ : Convex Real t；ht₂ : IsCompact t；di
sj : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `geometric_hahn_banach_compact_closed`：geometric_hahn_banach_compact_clos
ed (hs₁ : Convex Real s) (hs₂ : IsCompact s) (ht₁ : Convex Real t) (ht₂ : IsClos
ed t) (disj : Disjoint s t…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` wh
ere `s` is
closed, and `t` is compact, there is a continuous linear functional which strong
ly separates them.
-/
theorem geometric_hahn_banach_closed_compact (hs₁ : Convex ℝ s) (hs₂ : IsClosed s)
    (ht₁ : Convex ℝ t) (ht₂ : IsCompact t) (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b :=
  let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩
/-
**geometric_hahn_banach_point_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_point_closed (ht₁ : Convex Real t) (ht₂ : IsClosed t
) (disj : x ∉ t) : exists (f : StrongDual Real E) (u : Real), f x < u ∧ forall b
 in t, u < f b
参数：ht₁ : Convex Real t；ht₂ : IsClosed t；disj : x ∉ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `geometric_hahn_banach_compact_closed`：geometric_hahn_banach_compact_clos
ed (hs₁ : Convex Real s) (hs₂ : IsCompact s) (ht₁ : Convex Real t) (ht₂ : IsClos
ed t) (disj : Disjoint s t…
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_left`：disjoint_singleton_left : Disjoint {a} s ↔ 
a ∉ s
· 使用定理 `LT.lt.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a → 
c < b → c < a
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem geometric_hahn_banach_point_closed (ht₁ : Convex ℝ t) (ht₂ : IsClosed t) (disj : x ∉ t) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), f x < u ∧ ∀ b ∈ t, u < f b :=
  let ⟨f, _u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
  ⟨f, v, hst.trans' <| ha x <| mem_singleton _, hb⟩
/-
**geometric_hahn_banach_closed_point** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_closed_point (hs₁ : Convex Real s) (hs₂ : IsClosed s
) (disj : x ∉ s) : exists (f : StrongDual Real E) (u : Real), (forall a in s, f 
a < u) ∧ u < f x
参数：hs₁ : Convex Real s；hs₂ : IsClosed s；disj : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `geometric_hahn_banach_closed_compact`：geometric_hahn_banach_closed_compa
ct (hs₁ : Convex Real s) (hs₂ : IsClosed s) (ht₁ : Convex Real t) (ht₂ : IsCompa
ct t) (disj : Disjoint s t…
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem geometric_hahn_banach_closed_point (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (disj : x ∉ s) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ u < f x :=
  let ⟨f, s, _t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) isCompact_singleton
      (disjoint_singleton_right.2 disj)
  ⟨f, s, ha, hst.trans <| hb x <| mem_singleton _⟩

/-- See also `SeparatingDual.eq_iff_forall_dual_eq`. -/
/-
**geometric_hahn_banach_point_point** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geometric_hahn_banach_point_point [T1Space E] (hxy : x != y) : exists f : 
StrongDual Real E, f x < f y
参数：hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `geometric_hahn_banach_compact_closed`：geometric_hahn_banach_compact_clos
ed (hs₁ : Convex Real s) (hs₂ : IsCompact s) (ht₁ : Convex Real t) (ht₂ : IsClos
ed t) (disj : Disjoint s t…
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton`：disjoint_singleton : Disjoint ({a} : Set α) {b} 
↔ a != b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
See also `SeparatingDual.eq_iff_forall_dual_eq`.
-/
theorem geometric_hahn_banach_point_point [T1Space E] (hxy : x ≠ y) :
    ∃ f : StrongDual ℝ E, f x < f y := by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton
      (convex_singleton y) isClosed_singleton (disjoint_singleton.2 hxy)
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩

/-- A closed convex set is the intersection of the half-spaces containing it. -/
/-
**iInter_halfSpaces_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInter_halfSpaces_eq (hs₁ : Convex Real s) (hs₂ : IsClosed s) : ⋂ l : Stro
ngDual Real E, { x | exists y in s, l x <= l y } = s
参数：hs₁ : Convex Real s；hs₂ : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_ofPred`：iInter_ofPred (P : ι -> α -> Prop) : ⋂ i, { x : α | P
 i x } = { x : α | forall i, P i x }
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `geometric_hahn_banach_closed_point`：geometric_hahn_banach_closed_point (
hs₁ : Convex Real s) (hs₂ : IsClosed s) (disj : x ∉ s) : exists (f : StrongDual 
Real E) (u : Real), (for…
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
A closed convex set is the intersection of the half-spaces containing it.
-/
theorem iInter_halfSpaces_eq (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    ⋂ l : StrongDual ℝ E, { x | ∃ y ∈ s, l x ≤ l y } = s := by
  rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l => ⟨x, hx, le_rfl⟩
  by_contra h
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point hs₁ hs₂ h
  obtain ⟨y, hy, hxy⟩ := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).not_ge le_rfl
end

namespace RCLike

variable [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-
**RCLike.separate_convex_open_set** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：separate_convex_open_set {s : Set E} (hs₀ : (0 : E) in s) (hs₁ : Convex Re
al s) (hs₂ : IsOpen s) {x₀ : E} (hx₀ : x₀ ∉ s) : exists f : StrongDual 𝕜 E, re (
f x₀) = 1 ∧ forall x in s, re (f x) < 1
参数：hs₀ : (0 : E) in s；hs₁ : Convex Real s；hs₂ : IsOpen s；hx₀ : x₀ ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsScalarTower.continuousSMul`：IsScalarTower.continuousSMul {M : Type*} (
N : Type*) {α : Type*} [Monoid N] [SMul M N] [MulAction N α] [SMul M α] [IsScala
rTower M N α] [Top…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `separate_convex_open_set`：separate_convex_open_set [TopologicalSpace E] 
[AddCommGroup E] [IsTopologicalAddGroup E] [Module Real E] [ContinuousSMul Real 
E] {s : Set E}…
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StrongDual.extendRCLikeₗ_apply`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {F : 
Type u_2} [inst_1 : TopologicalSpace F] [inst_2 : AddCommGroup F]   [inst_3 : _r
oot_.Module 𝕜 F] [in…
· 使用引理 `StrongDual.re_extendRCLike_apply`：re_extendRCLike_apply (g : StrongDual 
Real F) (x : F) : re ((extendRCLike g) x : 𝕜) = g x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem separate_convex_open_set {s : Set E}
    (hs₀ : (0 : E) ∈ s) (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) {x₀ : E} (hx₀ : x₀ ∉ s) :
    ∃ f : StrongDual 𝕜 E, re (f x₀) = 1 ∧ ∀ x ∈ s, re (f x) < 1 := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨g, hg⟩ := _root_.separate_convex_open_set hs₀ hs₁ hs₂ hx₀
  use g.extendRCLikeₗ
  simpa [g.extendRCLikeₗ_apply]
/-
**RCLike.geometric_hahn_banach_open** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：geometric_hahn_banach_open (hs₁ : Convex Real s) (hs₂ : IsOpen s) (ht : Co
nvex Real t) (disj : Disjoint s t) : exists (f : StrongDual 𝕜 E) (u : Real), (fo
rall a in s, re (f a) < u) ∧ forall b in t, u <= re (f b)
参数：hs₁ : Convex Real s；hs₂ : IsOpen s；ht : Convex Real t；disj : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsScalarTower.continuousSMul`：IsScalarTower.continuousSMul {M : Type*} (
N : Type*) {α : Type*} [Monoid N] [SMul M N] [MulAction N α] [SMul M α] [IsScala
rTower M N α] [Top…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `geometric_hahn_banach_open`：geometric_hahn_banach_open (hs₁ : Convex Rea
l s) (hs₂ : IsOpen s) (ht : Convex Real t) (disj : Disjoint s t) : exists (f : S
trongDual Real E…
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StrongDual.extendRCLikeₗ_apply`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {F : 
Type u_2} [inst_1 : TopologicalSpace F] [inst_2 : AddCommGroup F]   [inst_3 : _r
oot_.Module 𝕜 F] [in…
· 使用引理 `StrongDual.re_extendRCLike_apply`：re_extendRCLike_apply (g : StrongDual 
Real F) (x : F) : re ((extendRCLike g) x : 𝕜) = g x
-/
theorem geometric_hahn_banach_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht : Convex ℝ t)
    (disj : Disjoint s t) : ∃ (f : StrongDual 𝕜 E) (u : ℝ), (∀ a ∈ s, re (f a) < u) ∧
    ∀ b ∈ t, u ≤ re (f b) := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨f, u, h⟩ := _root_.geometric_hahn_banach_open hs₁ hs₂ ht disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply] using Exists.intro u h
/-
**RCLike.geometric_hahn_banach_open_point** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：geometric_hahn_banach_open_point (hs₁ : Convex Real s) (hs₂ : IsOpen s) (d
isj : x ∉ s) : exists f : StrongDual 𝕜 E, forall a in s, re (f a) < re (f x)
参数：hs₁ : Convex Real s；hs₂ : IsOpen s；disj : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsScalarTower.continuousSMul`：IsScalarTower.continuousSMul {M : Type*} (
N : Type*) {α : Type*} [Monoid N] [SMul M N] [MulAction N α] [SMul M α] [IsScala
rTower M N α] [Top…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `geometric_hahn_banach_open_point`：geometric_hahn_banach_open_point (hs₁ 
: Convex Real s) (hs₂ : IsOpen s) (disj : x ∉ s) : exists f : StrongDual Real E,
 forall a in s, f a < …
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StrongDual.extendRCLikeₗ_apply`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {F : 
Type u_2} [inst_1 : TopologicalSpace F] [inst_2 : AddCommGroup F]   [inst_3 : _r
oot_.Module 𝕜 F] [in…
· 使用引理 `StrongDual.re_extendRCLike_apply`：re_extendRCLike_apply (g : StrongDual 
Real F) (x : F) : re ((extendRCLike g) x : 𝕜) = g x
-/
theorem geometric_hahn_banach_open_point (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (disj : x ∉ s) :
    ∃ f : StrongDual 𝕜 E, ∀ a ∈ s, re (f a) < re (f x) := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨f, h⟩ := _root_.geometric_hahn_banach_open_point hs₁ hs₂ disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply]
/-
**RCLike.geometric_hahn_banach_point_open** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：geometric_hahn_banach_point_open (ht₁ : Convex Real t) (ht₂ : IsOpen t) (d
isj : x ∉ t) : exists f : StrongDual 𝕜 E, forall b in t, re (f x) < re (f b)
参数：ht₁ : Convex Real t；ht₂ : IsOpen t；disj : x ∉ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.geometric_hahn_banach_open_point`：geometric_hahn_banach_open_poin
t (hs₁ : Convex Real s) (hs₂ : IsOpen s) (disj : x ∉ s) : exists f : StrongDual 
𝕜 E, forall a in s, re (f a) …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem geometric_hahn_banach_point_open (ht₁ : Convex ℝ t) (ht₂ : IsOpen t) (disj : x ∉ t) :
    ∃ f : StrongDual 𝕜 E, ∀ b ∈ t, re (f x) < re (f b) :=
  let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by simpa⟩
/-
**RCLike.geometric_hahn_banach_open_open** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：geometric_hahn_banach_open_open (hs₁ : Convex Real s) (hs₂ : IsOpen s) (ht
₁ : Convex Real t) (ht₃ : IsOpen t) (disj : Disjoint s t) : exists (f : StrongDu
al 𝕜 E) (u : Real), (forall a in s, re (f a) < u) ∧ forall b in t, u < re (f b)
参数：hs₁ : Convex Real s；hs₂ : IsOpen s；ht₁ : Convex Real t；ht₃ : IsOpen t；disj : 
Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsScalarTower.continuousSMul`：IsScalarTower.continuousSMul {M : Type*} (
N : Type*) {α : Type*} [Monoid N] [SMul M N] [MulAction N α] [SMul M α] [IsScala
rTower M N α] [Top…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `geometric_hahn_banach_open_open`：geometric_hahn_banach_open_open (hs₁ : 
Convex Real s) (hs₂ : IsOpen s) (ht₁ : Convex Real t) (ht₃ : IsOpen t) (disj : D
isjoint s t) : exists…
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StrongDual.extendRCLikeₗ_apply`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {F : 
Type u_2} [inst_1 : TopologicalSpace F] [inst_2 : AddCommGroup F]   [inst_3 : _r
oot_.Module 𝕜 F] [in…
· 使用引理 `StrongDual.re_extendRCLike_apply`：re_extendRCLike_apply (g : StrongDual 
Real F) (x : F) : re ((extendRCLike g) x : 𝕜) = g x
-/
theorem geometric_hahn_banach_open_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s)
    (ht₁ : Convex ℝ t) (ht₃ : IsOpen t) (disj : Disjoint s t) :
    ∃ (f : StrongDual 𝕜 E) (u : ℝ), (∀ a ∈ s, re (f a) < u) ∧ ∀ b ∈ t, u < re (f b) := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨f, u, h⟩ := _root_.geometric_hahn_banach_open_open hs₁ hs₂ ht₁ ht₃ disj
  use f.extendRCLikeₗ
  simpa [f.extendRCLikeₗ_apply] using Exists.intro u h
/-
**RCLike.geometric_hahn_banach_of_nonempty_interior** 是 Mathlib 中的一个定理，位于命名空间 `R
CLike`。
形式化陈述：geometric_hahn_banach_of_nonempty_interior (hs : Convex Real s) (ht : Conv
ex Real t) (hst : Disjoint (interior s) t) (hsint : (interior s).Nonempty) (htne
 : t.Nonempty) : exists (f : StrongDual 𝕜 E) (u : Real), f != 0 ∧ (forall a in s
, re (f a) <= u) ∧ forall b in t, u <= re (f b)
参数：hs : Convex Real s；ht : Convex Real t；hst : Disjoint (interior s) t；hsint : (
interior s).Nonempty；htne : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsScalarTower.continuousSMul`：IsScalarTower.continuousSMul {M : Type*} (
N : Type*) {α : Type*} [Monoid N] [SMul M N] [MulAction N α] [SMul M α] [IsScala
rTower M N α] [Top…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `geometric_hahn_banach_of_nonempty_interior`：geometric_hahn_banach_of_non
empty_interior (hs : Convex Real s) (ht : Convex Real t) (hst : Disjoint (interi
or s) t) (hsint : (interior s).N…
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StrongDual.extendRCLikeₗ_apply`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {F : 
Type u_2} [inst_1 : TopologicalSpace F] [inst_2 : AddCommGroup F]   [inst_3 : _r
oot_.Module 𝕜 F] [in…
（共 31 条，此处仅展示前 30 条）
-/
theorem geometric_hahn_banach_of_nonempty_interior
  (hs : Convex ℝ s) (ht : Convex ℝ t) (hst : Disjoint (interior s) t)
    (hsint : (interior s).Nonempty) (htne : t.Nonempty) :
    ∃ (f : StrongDual 𝕜 E) (u : ℝ), f ≠ 0 ∧ (∀ a ∈ s, re (f a) ≤ u) ∧ ∀ b ∈ t, u ≤ re (f b) := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨f, u, hfne, hA', hB'⟩ :=
    _root_.geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
  refine ⟨f.extendRCLikeₗ, u, fun hzero ↦ ?_, ?_, ?_⟩
  · exact hfne <| (StrongDual.extendRCLikeₗ (𝕜 := 𝕜)).injective (by simpa using hzero)
  · simpa [f.extendRCLikeₗ_apply] using hA'
  · simpa [f.extendRCLikeₗ_apply] using hB'

/-- If `s` and `t` are convex, `interior s` is nonempty and disjoint from `t`, then a continuous
`𝕜`-linear functional weakly separates `s` and `t`. If `t` is nonempty, this follows from
`geometric_hahn_banach_of_nonempty_interior`; if `t = ∅`, the zero functional works. -/
/-
**RCLike.geometric_hahn_banach_of_nonempty_interior'** 是 Mathlib 中的一个定理，位于命名空间 `
RCLike`。
形式化陈述：geometric_hahn_banach_of_nonempty_interior' (hs : Convex Real s) (ht : Con
vex Real t) (hst : Disjoint (interior s) t) (hsint : (interior s).Nonempty) : ex
ists (f : StrongDual 𝕜 E) (u : Real), (forall a in s, re (f a) <= u) ∧ forall b 
in t, u <= re (f b)
参数：hs : Convex Real s；ht : Convex Real t；hst : Disjoint (interior s) t；hsint : (
interior s).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.geometric_hahn_banach_of_nonempty_interior`：geometric_hahn_banach
_of_nonempty_interior (hs : Convex Real s) (ht : Convex Real t) (hst : Disjoint 
(interior s) t) (hsint : (interior s).N…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
If `s` and `t` are convex, `interior s` is nonempty and disjoint from `t`, then 
a continuous
`𝕜`-linear functional weakly separates `s` and `t`. If `t` is nonempty, this fol
lows from
`geometric_hahn_banach_of_nonempty_interior`; if `t = ∅`, the zero functional wo
rks.
-/
theorem geometric_hahn_banach_of_nonempty_interior'
  (hs : Convex ℝ s) (ht : Convex ℝ t) (hst : Disjoint (interior s) t)
    (hsint : (interior s).Nonempty) :
    ∃ (f : StrongDual 𝕜 E) (u : ℝ), (∀ a ∈ s, re (f a) ≤ u) ∧ ∀ b ∈ t, u ≤ re (f b) := by
  by_cases htne : t.Nonempty
  · have hsep :
        ∃ (f : StrongDual 𝕜 E) (u : ℝ),
          f ≠ 0 ∧ (∀ a ∈ s, re (f a) ≤ u) ∧ ∀ b ∈ t, u ≤ re (f b) :=
        geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne
    obtain ⟨f, u, -, hs', ht'⟩ := hsep
    exact ⟨f, u, hs', ht'⟩
  · exact ⟨0, 0, by simp⟩

/-- If `A` is convex with nonempty interior and `x ∉ interior A`, then there is a nonzero
continuous `𝕜`-linear functional whose real part attains its maximum on `A` at `x`. -/
/-
**RCLike.geometric_hahn_banach_of_nonempty_interior_point** 是 Mathlib 中的一个定理，位于命
名空间 `RCLike`。
形式化陈述：geometric_hahn_banach_of_nonempty_interior_point {A : Set E} (hA : Convex 
Real A) (hxA : x ∉ interior A) (hAint : (interior A).Nonempty) : exists f : Stro
ngDual 𝕜 E, f != 0 ∧ forall a in A, re (f a) <= re (f x)
参数：hA : Convex Real A；hxA : x ∉ interior A；hAint : (interior A).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsScalarTower.continuousSMul`：IsScalarTower.continuousSMul {M : Type*} (
N : Type*) {α : Type*} [Monoid N] [SMul M N] [MulAction N α] [SMul M α] [IsScala
rTower M N α] [Top…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `geometric_hahn_banach_of_nonempty_interior_point`：geometric_hahn_banach_
of_nonempty_interior_point {A : Set E} (hA : Convex Real A) (hxA : x ∉ interior 
A) (hAint : (interior A).Nonempty) : e…
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `A` is convex with nonempty interior and `x ∉ interior A`, then there is a no
nzero
continuous `𝕜`-linear functional whose real part attains its maximum on `A` at `
x`.
-/
theorem geometric_hahn_banach_of_nonempty_interior_point
    {A : Set E} (hA : Convex ℝ A) (hxA : x ∉ interior A) (hAint : (interior A).Nonempty) :
    ∃ f : StrongDual 𝕜 E, f ≠ 0 ∧ ∀ a ∈ A, re (f a) ≤ re (f x) := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨f, hfne, hA'⟩ := _root_.geometric_hahn_banach_of_nonempty_interior_point hA hxA hAint
  refine ⟨f.extendRCLikeₗ, fun hzero ↦ ?_, ?_⟩
  · exact hfne <| (StrongDual.extendRCLikeₗ (𝕜 := 𝕜)).injective (by simpa using hzero)
  · simpa [f.extendRCLikeₗ_apply] using hA'

variable [LocallyConvexSpace ℝ E]
/-
**RCLike.geometric_hahn_banach_compact_closed** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`
。
形式化陈述：geometric_hahn_banach_compact_closed (hs₁ : Convex Real s) (hs₂ : IsCompac
t s) (ht₁ : Convex Real t) (ht₂ : IsClosed t) (disj : Disjoint s t) : exists (f 
: StrongDual 𝕜 E) (u v : Real), (forall a in s, re (f a) < u) ∧ u < v ∧ forall b
 in t, v < re (f b)
参数：hs₁ : Convex Real s；hs₂ : IsCompact s；ht₁ : Convex Real t；ht₂ : IsClosed t；di
sj : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsScalarTower.continuousSMul`：IsScalarTower.continuousSMul {M : Type*} (
N : Type*) {α : Type*} [Monoid N] [SMul M N] [MulAction N α] [SMul M α] [IsScala
rTower M N α] [Top…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `geometric_hahn_banach_compact_closed`：geometric_hahn_banach_compact_clos
ed (hs₁ : Convex Real s) (hs₂ : IsCompact s) (ht₁ : Convex Real t) (ht₂ : IsClos
ed t) (disj : Disjoint s t…
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StrongDual.extendRCLikeₗ_apply`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {F : 
Type u_2} [inst_1 : TopologicalSpace F] [inst_2 : AddCommGroup F]   [inst_3 : _r
oot_.Module 𝕜 F] [in…
· 使用引理 `StrongDual.re_extendRCLike_apply`：re_extendRCLike_apply (g : StrongDual 
Real F) (x : F) : re ((extendRCLike g) x : 𝕜) = g x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem geometric_hahn_banach_compact_closed (hs₁ : Convex ℝ s) (hs₂ : IsCompact s)
    (ht₁ : Convex ℝ t) (ht₂ : IsClosed t) (disj : Disjoint s t) :
    ∃ (f : StrongDual 𝕜 E) (u v : ℝ), (∀ a ∈ s, re (f a) < u) ∧ u < v ∧ ∀ b ∈ t, v < re (f b) := by
  have := IsScalarTower.continuousSMul (M := ℝ) (α := E) 𝕜
  obtain ⟨g, u, v, h1⟩ := _root_.geometric_hahn_banach_compact_closed hs₁ hs₂ ht₁ ht₂ disj
  use g.extendRCLikeₗ
  simpa [g.extendRCLikeₗ_apply, exists_and_left] using ⟨u, h1.1, v, h1.2⟩
/-
**RCLike.geometric_hahn_banach_closed_compact** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`
。
形式化陈述：geometric_hahn_banach_closed_compact (hs₁ : Convex Real s) (hs₂ : IsClosed
 s) (ht₁ : Convex Real t) (ht₂ : IsCompact t) (disj : Disjoint s t) : exists (f 
: StrongDual 𝕜 E) (u v : Real), (forall a in s, re (f a) < u) ∧ u < v ∧ forall b
 in t, v < re (f b)
参数：hs₁ : Convex Real s；hs₂ : IsClosed s；ht₁ : Convex Real t；ht₂ : IsCompact t；di
sj : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.geometric_hahn_banach_compact_closed`：geometric_hahn_banach_compa
ct_closed (hs₁ : Convex Real s) (hs₂ : IsCompact s) (ht₁ : Convex Real t) (ht₂ :
 IsClosed t) (disj : Disjoint s t…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem geometric_hahn_banach_closed_compact (hs₁ : Convex ℝ s) (hs₂ : IsClosed s)
    (ht₁ : Convex ℝ t) (ht₂ : IsCompact t) (disj : Disjoint s t) :
    ∃ (f : StrongDual 𝕜 E) (u v : ℝ), (∀ a ∈ s, re (f a) < u) ∧ u < v ∧ ∀ b ∈ t, v < re (f b) :=
  let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by simpa using ht, by simpa using st, by simpa using hs⟩
/-
**RCLike.geometric_hahn_banach_point_closed** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：geometric_hahn_banach_point_closed (ht₁ : Convex Real t) (ht₂ : IsClosed t
) (disj : x ∉ t) : exists (f : StrongDual 𝕜 E) (u : Real), re (f x) < u ∧ forall
 b in t, u < re (f b)
参数：ht₁ : Convex Real t；ht₂ : IsClosed t；disj : x ∉ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.geometric_hahn_banach_compact_closed`：geometric_hahn_banach_compa
ct_closed (hs₁ : Convex Real s) (hs₂ : IsCompact s) (ht₁ : Convex Real t) (ht₂ :
 IsClosed t) (disj : Disjoint s t…
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_left`：disjoint_singleton_left : Disjoint {a} s ↔ 
a ∉ s
· 使用定理 `LT.lt.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a → 
c < b → c < a
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem geometric_hahn_banach_point_closed (ht₁ : Convex ℝ t) (ht₂ : IsClosed t)
    (disj : x ∉ t) : ∃ (f : StrongDual 𝕜 E) (u : ℝ), re (f x) < u ∧ ∀ b ∈ t, u < re (f b) :=
  let ⟨f, _u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) isCompact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
  ⟨f, v, hst.trans' <| ha x <| mem_singleton _, hb⟩
/-
**RCLike.geometric_hahn_banach_closed_point** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：geometric_hahn_banach_closed_point (hs₁ : Convex Real s) (hs₂ : IsClosed s
) (disj : x ∉ s) : exists (f : StrongDual 𝕜 E) (u : Real), (forall a in s, re (f
 a) < u) ∧ u < re (f x)
参数：hs₁ : Convex Real s；hs₂ : IsClosed s；disj : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.geometric_hahn_banach_closed_compact`：geometric_hahn_banach_close
d_compact (hs₁ : Convex Real s) (hs₂ : IsClosed s) (ht₁ : Convex Real t) (ht₂ : 
IsCompact t) (disj : Disjoint s t…
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem geometric_hahn_banach_closed_point (hs₁ : Convex ℝ s) (hs₂ : IsClosed s)
    (disj : x ∉ s) : ∃ (f : StrongDual 𝕜 E) (u : ℝ), (∀ a ∈ s, re (f a) < u) ∧ u < re (f x) :=
  let ⟨f, s, _t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) isCompact_singleton
      (disjoint_singleton_right.2 disj)
  ⟨f, s, ha, hst.trans <| hb x <| mem_singleton _⟩
/-
**RCLike.geometric_hahn_banach_point_point** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：geometric_hahn_banach_point_point [T1Space E] (hxy : x != y) : exists f : 
StrongDual 𝕜 E, re (f x) < re (f y)
参数：hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.geometric_hahn_banach_compact_closed`：geometric_hahn_banach_compa
ct_closed (hs₁ : Convex Real s) (hs₂ : IsCompact s) (ht₁ : Convex Real t) (ht₂ :
 IsClosed t) (disj : Disjoint s t…
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton`：disjoint_singleton : Disjoint ({a} : Set α) {b} 
↔ a != b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 38 条，此处仅展示前 30 条）
-/
theorem geometric_hahn_banach_point_point [T1Space E] (hxy : x ≠ y) :
    ∃ f : StrongDual 𝕜 E, re (f x) < re (f y) := by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (𝕜 := 𝕜) (convex_singleton x) isCompact_singleton
      (convex_singleton y) isClosed_singleton (disjoint_singleton.2 hxy)
  exact ⟨f, by linarith [hs x rfl, ht y rfl]⟩
/-
**RCLike.iInter_halfSpaces_eq** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：iInter_halfSpaces_eq (hs₁ : Convex Real s) (hs₂ : IsClosed s) : ⋂ l : Stro
ngDual 𝕜 E, { x | exists y in s, re (l x) <= re (l y) } = s
参数：hs₁ : Convex Real s；hs₂ : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_ofPred`：iInter_ofPred (P : ι -> α -> Prop) : ⋂ i, { x : α | P
 i x } = { x : α | forall i, P i x }
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `RCLike.geometric_hahn_banach_closed_point`：geometric_hahn_banach_closed_
point (hs₁ : Convex Real s) (hs₂ : IsClosed s) (disj : x ∉ s) : exists (f : Stro
ngDual 𝕜 E) (u : Real), (forall…
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iInter_halfSpaces_eq (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    ⋂ l : StrongDual 𝕜 E, { x | ∃ y ∈ s, re (l x) ≤ re (l y) } = s := by
  rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l => ⟨x, hx, le_rfl⟩
  by_contra h
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point (𝕜 := 𝕜) hs₁ hs₂ h
  obtain ⟨y, hy, hxy⟩ := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).false
/-
**RCLike.iInter_halfSpaces_eq'** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：iInter_halfSpaces_eq' (hs₁ : Convex Real s) (hs₂ : IsClosed s) : ⋂ (l : St
rongDual 𝕜 E) (c : Real) (_ : forall y in s, re (l y) <= c), { x | re (l x) <= c
 } = s
参数：hs₁ : Convex Real s；hs₂ : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_ofPred`：iInter_ofPred (P : ι -> α -> Prop) : ⋂ i, { x : α | P
 i x } = { x : α | forall i, P i x }
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `RCLike.geometric_hahn_banach_closed_point`：geometric_hahn_banach_closed_
point (hs₁ : Convex Real s) (hs₂ : IsClosed s) (disj : x ∉ s) : exists (f : Stro
ngDual 𝕜 E) (u : Real), (forall…
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem iInter_halfSpaces_eq' (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    ⋂ (l : StrongDual 𝕜 E) (c : ℝ) (_ : ∀ y ∈ s, re (l y) ≤ c), { x | re (l x) ≤ c } = s := by
  simp_rw [Set.iInter_ofPred]
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx l c hc => hc x hx
  by_contra h
  obtain ⟨l, c, hls, hl⟩ := geometric_hahn_banach_closed_point (𝕜 := 𝕜) hs₁ hs₂ h
  exact (hl.trans_le (hx l c (fun y hy ↦ (hls y hy).le))).false
/-
**RCLike.iInter_countable_halfSpaces_eq** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：iInter_countable_halfSpaces_eq [HereditarilyLindelofSpace E] (hs₁ : Convex
 Real s) (hs₂ : IsClosed s) : exists l : Nat -> StrongDual 𝕜 E, exists c : Nat -
> Real, ⋂ n, { x | re (l n x) <= c n } = s
参数：hs₁ : Convex Real s；hs₂ : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Set.iInter_sigma`：iInter_sigma {γ : α -> Type*} (s : Sigma γ -> Set β) :
 ⋂ ia, s ia = ⋂ i, ⋂ a, s ⟨i, a⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_subtype`：iInter_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `RCLike.iInter_halfSpaces_eq'`：iInter_halfSpaces_eq' (hs₁ : Convex Real s
) (hs₂ : IsClosed s) : ⋂ (l : StrongDual 𝕜 E) (c : Real) (_ : forall y in s, re 
(l y) <= c), { x |…
· 使用引理 `eq_closed_inter_nat`：eq_closed_inter_nat [HereditarilyLindelofSpace X] {
ι : Type*} [Nonempty ι] (C : ι -> Set X) (h : forall i, IsClosed (C i)) : exists
 k : Nat …
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `RCLike.continuous_re`：continuous_re : Continuous (re : K -> Real)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem iInter_countable_halfSpaces_eq [HereditarilyLindelofSpace E]
    (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    ∃ l : ℕ → StrongDual 𝕜 E, ∃ c : ℕ → ℝ, ⋂ n, { x | re (l n x) ≤ c n } = s := by
  set ι := Σ (l : StrongDual 𝕜 E), { c : ℝ // ∀ y ∈ s, re (l y) ≤ c }
  set l : ι → StrongDual 𝕜 E := fun lc ↦ lc.1
  set c : ι → ℝ := fun lc ↦ lc.2.val
  set hc : ∀ i, ∀ y ∈ s, re (l i y) ≤ c i := fun lc ↦ lc.2.prop
  have : Nonempty ι := ⟨0, 0, fun _ _ ↦ by simp⟩
  have : ⋂ i : ι, { x | re (l i x) ≤ c i } = s := by
    simpa only [ι, iInter_sigma, iInter_subtype, l, c] using iInter_halfSpaces_eq' hs₁ hs₂
  obtain ⟨k, hk⟩ := eq_closed_inter_nat (fun i : ι ↦ { x | re (l i x) ≤ c i })
    (fun i ↦ isClosed_le (continuous_re.comp (l i).continuous) continuous_const)
  exact ⟨l ∘ k, c ∘ k, hk.trans this⟩

end RCLike

