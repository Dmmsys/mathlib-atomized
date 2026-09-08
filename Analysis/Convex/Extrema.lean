/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Minima and maxima of convex functions

We show that if a function `f : E → β` is convex, then a local minimum is also
a global minimum, and likewise for concave functions.
-/

public section


variable {E β : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module ℝ β] [IsOrderedModule ℝ β] [PosSMulReflectLE ℝ β] {s : Set E}

open Set Filter Function Topology

/-- Helper lemma for the more general case: `IsMinOn.of_isLocalMinOn_of_convexOn`.
-/
/-
**IsMinOn.of_isLocalMinOn_of_convexOn_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.of_isLocalMinOn_of_convexOn_Icc {f : Real -> β} {a b : Real} (a_lt
_b : a < b) (h_local_min : IsLocalMinOn f (Icc a b) a) (h_conv : ConvexOn Real (
Icc a b) f) : IsMinOn f (Icc a b) a
参数：a_lt_b : a < b；h_local_min : IsLocalMinOn f (Icc a b) a；h_conv : ConvexOn Rea
l (Icc a b) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `IsMinFilter.filter_mono`：IsMinFilter.filter_mono (h : IsMinFilter f l a)
 (hl : l' <= l) : IsMinFilter f l' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_Icc_eq_nhdsGE`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] {a b : α},   b < a → nhdsWithin b (S
et.Icc b a) = …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsLocalMinOn.eq_1`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : Preorder β] (f : α → β) (s : Set α) (a : α),   IsLocalMinOn f s a =
 IsMinF…
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `Ioc_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioc b a ∈ nhdsWithin 
b (S…
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
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
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Convex.mem_Ioc`：Convex.mem_Ioc (h : x < y) : z in Ioc x y ↔ exists a b, 
0 <= a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `smul_le_smul_iff_of_pos_left`：smul_le_smul_iff_of_pos_left [PosSMulMono 
α β] [PosSMulReflectLE α β] (ha : 0 < a) : a • b₁ <= a • b₂ ↔ b₁ <= b₂
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Helper lemma for the more general case: `IsMinOn.of_isLocalMinOn_of_convexOn`.
-/
theorem IsMinOn.of_isLocalMinOn_of_convexOn_Icc {f : ℝ → β} {a b : ℝ} (a_lt_b : a < b)
    (h_local_min : IsLocalMinOn f (Icc a b) a) (h_conv : ConvexOn ℝ (Icc a b) f) :
    IsMinOn f (Icc a b) a := by
  rintro c hc
  dsimp only [mem_ofPred_eq]
  rw [IsLocalMinOn, nhdsWithin_Icc_eq_nhdsGE a_lt_b] at h_local_min
  rcases hc.1.eq_or_lt with (rfl | a_lt_c)
  · exact le_rfl
  have H₁ : ∀ᶠ y in 𝓝[>] a, f a ≤ f y :=
    h_local_min.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have H₂ : ∀ᶠ y in 𝓝[>] a, y ∈ Ioc a c := Ioc_mem_nhdsGT a_lt_c
  rcases (H₁.and H₂).exists with ⟨y, hfy, hy_ac⟩
  rcases (Convex.mem_Ioc a_lt_c).mp hy_ac with ⟨ya, yc, ya₀, yc₀, yac, rfl⟩
  suffices ya • f a + yc • f a ≤ ya • f a + yc • f c from
    (smul_le_smul_iff_of_pos_left yc₀).1 (le_of_add_le_add_left this)
  calc
    ya • f a + yc • f a = f a := by rw [← add_smul, yac, one_smul]
    _ ≤ f (ya * a + yc * c) := hfy
    _ ≤ ya • f a + yc • f c := h_conv.2 (left_mem_Icc.2 a_lt_b.le) hc ya₀ yc₀.le yac

/-- A local minimum of a convex function is a global minimum, restricted to a set `s`.
-/
/-
**IsMinOn.of_isLocalMinOn_of_convexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.of_isLocalMinOn_of_convexOn {f : E -> β} {a : E} (a_in_s : a in s)
 (h_localmin : IsLocalMinOn f s a) (h_conv : ConvexOn Real s f) : IsMinOn f s a
参数：a_in_s : a in s；h_localmin : IsLocalMinOn f s a；h_conv : ConvexOn Real s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `AffineMap.lineMap_continuous`：lineMap_continuous {p q : P} : Continuous 
(lineMap p q : R ->ᵃ[R] P)
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsLocalMinOn.comp_continuousOn`：IsLocalMinOn.comp_continuousOn [Topologi
calSpace δ] {t : Set α} {s : Set δ} {g : δ -> α} {b : δ} (hf : IsLocalMinOn f t 
(g b)) (hst : s subs…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsMinOn.of_isLocalMinOn_of_convexOn_Icc`：IsMinOn.of_isLocalMinOn_of_conv
exOn_Icc {f : Real -> β} {a b : Real} (a_lt_b : a < b) (h_local_min : IsLocalMin
On f (Icc a b) a) (h_conv : C…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ConvexOn.subset`：ConvexOn.subset {t : Set E} (hf : ConvexOn 𝕜 t f) (hst 
: s subseteq t) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f
· 使用定理 `ConvexOn.comp_affineMap`：ConvexOn.comp_affineMap {f : F -> β} (g : E ->ᵃ
[𝕜] F) {s : Set F} (hf : ConvexOn 𝕜 s f) : ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g)
· 使用定理 `convex_Icc`：convex_Icc (r s : β) : Convex 𝕜 (Icc r s)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a

--- 原说明 ---
A local minimum of a convex function is a global minimum, restricted to a set `s
`.
-/
theorem IsMinOn.of_isLocalMinOn_of_convexOn {f : E → β} {a : E} (a_in_s : a ∈ s)
    (h_localmin : IsLocalMinOn f s a) (h_conv : ConvexOn ℝ s f) : IsMinOn f s a := by
  intro x x_in_s
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a x
  have hg0 : g 0 = a := AffineMap.lineMap_apply_zero a x
  have hg1 : g 1 = x := AffineMap.lineMap_apply_one a x
  have hgc : Continuous g := AffineMap.lineMap_continuous
  have h_maps : MapsTo g (Icc 0 1) s := by
    simpa only [g, mapsTo_iff_image_subset, ← segment_eq_image_lineMap]
      using h_conv.1.segment_subset a_in_s x_in_s
  have fg_local_min_on : IsLocalMinOn (f ∘ g) (Icc 0 1) 0 := by
    rw [← hg0] at h_localmin
    exact h_localmin.comp_continuousOn h_maps hgc.continuousOn (left_mem_Icc.2 zero_le_one)
  have fg_min_on : IsMinOn (f ∘ g) (Icc 0 1 : Set ℝ) 0 := by
    refine IsMinOn.of_isLocalMinOn_of_convexOn_Icc one_pos fg_local_min_on ?_
    exact (h_conv.comp_affineMap g).subset h_maps (convex_Icc 0 1)
  simpa only [hg0, hg1, comp_apply, mem_ofPred_eq] using fg_min_on (right_mem_Icc.2 zero_le_one)

/-- A local maximum of a concave function is a global maximum, restricted to a set `s`. -/
/-
**IsMaxOn.of_isLocalMaxOn_of_concaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.of_isLocalMaxOn_of_concaveOn {f : E -> β} {a : E} (a_in_s : a in s
) (h_localmax : IsLocalMaxOn f s a) (h_conc : ConcaveOn Real s f) : IsMaxOn f s 
a
参数：a_in_s : a in s；h_localmax : IsLocalMaxOn f s a；h_conc : ConcaveOn Real s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinOn.of_isLocalMinOn_of_convexOn`：IsMinOn.of_isLocalMinOn_of_convexOn
 {f : E -> β} {a : E} (a_in_s : a in s) (h_localmin : IsLocalMinOn f s a) (h_con
v : ConvexOn Real s f) : …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [inst : P
reorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3 : Par
tialOrder β] [IsOrd…

--- 原说明 ---
A local maximum of a concave function is a global maximum, restricted to a set `
s`.
-/
theorem IsMaxOn.of_isLocalMaxOn_of_concaveOn {f : E → β} {a : E} (a_in_s : a ∈ s)
    (h_localmax : IsLocalMaxOn f s a) (h_conc : ConcaveOn ℝ s f) : IsMaxOn f s a :=
  IsMinOn.of_isLocalMinOn_of_convexOn (β := βᵒᵈ) a_in_s h_localmax h_conc

/-- A local minimum of a convex function is a global minimum. -/
/-
**IsMinOn.of_isLocalMin_of_convex_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.of_isLocalMin_of_convex_univ {f : E -> β} {a : E} (h_local_min : I
sLocalMin f a) (h_conv : ConvexOn Real univ f) : forall x, f a <= f x
参数：h_local_min : IsLocalMin f a；h_conv : ConvexOn Real univ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinOn.of_isLocalMinOn_of_convexOn`：IsMinOn.of_isLocalMinOn_of_convexOn
 {f : E -> β} {a : E} (a_in_s : a in s) (h_localmin : IsLocalMinOn f s a) (h_con
v : ConvexOn Real s f) : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `IsLocalMin.on`：IsLocalMin.on (h : IsLocalMin f a) (s) : IsLocalMinOn f s
 a

--- 原说明 ---
A local minimum of a convex function is a global minimum.
-/
theorem IsMinOn.of_isLocalMin_of_convex_univ {f : E → β} {a : E} (h_local_min : IsLocalMin f a)
    (h_conv : ConvexOn ℝ univ f) : ∀ x, f a ≤ f x := fun x =>
  (IsMinOn.of_isLocalMinOn_of_convexOn (mem_univ a) (h_local_min.on univ) h_conv) (mem_univ x)

/-- A local maximum of a concave function is a global maximum. -/
/-
**IsMaxOn.of_isLocalMax_of_convex_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.of_isLocalMax_of_convex_univ {f : E -> β} {a : E} (h_local_max : I
sLocalMax f a) (h_conc : ConcaveOn Real univ f) : forall x, f x <= f a
参数：h_local_max : IsLocalMax f a；h_conc : ConcaveOn Real univ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinOn.of_isLocalMin_of_convex_univ`：IsMinOn.of_isLocalMin_of_convex_un
iv {f : E -> β} {a : E} (h_local_min : IsLocalMin f a) (h_conv : ConvexOn Real u
niv f) : forall x, f a <= …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [inst : P
reorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3 : Par
tialOrder β] [IsOrd…

--- 原说明 ---
A local maximum of a concave function is a global maximum.
-/
theorem IsMaxOn.of_isLocalMax_of_convex_univ {f : E → β} {a : E} (h_local_max : IsLocalMax f a)
    (h_conc : ConcaveOn ℝ univ f) : ∀ x, f x ≤ f a :=
  IsMinOn.of_isLocalMin_of_convex_univ (β := βᵒᵈ) h_local_max h_conc
