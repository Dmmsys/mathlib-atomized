/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.Separation.Connected

/-!
# Cardinality of connected components under open and closed maps

Let `f : X → Y` be an open and closed map.

## Main results

- `IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`: If `Y` is connected,
  the number of connected components of `X` is bounded by the cardinality of the fiber
  of `f` at `y`.
- `IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton`: If `f` is also continuous
  with finite fibers and `Y` has finitely many connected components, so does `X`.
-/

public section

open scoped Function

open ConnectedComponents

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf₁ : IsOpenMap f)
  (hf₂ : IsClosedMap f)

include hf₁ hf₂

/-- If `f : X → Y` is an open and closed map and `Y` is connected, the number of connected
components of `X` is bounded by the cardinality of the fiber of any point. -/
@[stacks 07VB]
/-
**IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton** 是 Mathli
b 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton [Conne
ctedSpace Y] (y : Y) : ENat.card (ConnectedComponents X) <= (f ⁻¹' {y}).encard
参数：y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用引理 `Set.encard_iUnion_of_finite`：encard_iUnion_of_finite [Finite ι] {s : ι -
> Set α} (hs : Pairwise (Disjoint on s)) : (⋃ i, s i).encard = ∑ᶠ i, (s i).encar
d
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Disjoint.inter_left`：inter_left (u : Set α) (h : Disjoint s t) : Disjoin
t (s inter u) t
· 使用定理 `Disjoint.inter_right`：inter_right (u : Set α) (h : Disjoint s t) : Disjo
int s (t inter u)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `finsum_eq_sum_of_fintype`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCom
mMonoid M] [inst_1 : Fintype α] (f : α → M), ∑ᶠ (i : α), f i = ∑ i, f i
· 使用定理 `Fintype.sum_mono`：∀ {ι : Type u_1} {M : Type u_4} [inst : Fintype ι] [in
st_1 : AddCommMonoid M] [inst_2 : Preorder M] [AddLeftMono M],   Monotone fun f 
=> ∑ i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.one_le_encard_iff_nonempty`：∀ {α : Type u_1} {s : Set α}, 1 ≤ s.enca
rd ↔ s.Nonempty
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsClopen.eq_univ`：IsClopen.eq_univ [PreconnectedSpace α] {s : Set α} (h'
 : IsClopen s) (h : s.Nonempty) : s = univ
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : X → Y` is an open and closed map and `Y` is connected, the number of con
nected
components of `X` is bounded by the cardinality of the fiber of any point.
-/
lemma IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton [ConnectedSpace Y]
    (y : Y) : ENat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).encard := by
  suffices h : ∀ {n : ℕ} (U : Fin n → Set X) (hU₁ : ∀ i, IsClopen (U i)) (hU₂ : ∀ i, (U i).Nonempty)
      (hU₃ : Pairwise (Disjoint on U)) (hU₄ : ⋃ i, U i = Set.univ),
      n ≤ (f ⁻¹' {y}).encard by
    obtain (hy | hy) := finite_or_infinite (ConnectedComponents X)
    · cases nonempty_fintype (ConnectedComponents X)
      simp only [ENat.card_eq_coe_fintype_card]
      refine h (fun i ↦ ConnectedComponents.mk ⁻¹' {(Fintype.equivFin _).symm i}) (fun i ↦ ?_)
          (fun i ↦ ?_) (fun i j hij ↦ Disjoint.preimage _ (by simp [hij])) ?_
      · exact (isClopen_discrete _).preimage continuous_coe
      · exact (Set.singleton_nonempty _).preimage surjective_coe
      · simp [← Set.preimage_iUnion]
    · simp only [ENat.card_eq_top_of_infinite, top_le_iff, ENat.eq_top_iff_forall_ge]
      intro m
      obtain ⟨U, hU1, hU2, hU3, hU4⟩ := exists_fun_isClopen_of_infinite X (m + 1) (by simp)
      exact le_trans (by simp) (h U hU1 hU2 hU3 hU4)
  intro n U hU1 hU2 hU3 hU4
  have heq : f ⁻¹' {y} = ⋃ i, (U i ∩ f ⁻¹' {y}) := by
    conv_lhs => rw [← Set.univ_inter (f ⁻¹' {y}), ← hU4, Set.iUnion_inter]
  rw [heq, Set.encard_iUnion_of_finite fun i j hij ↦ .inter_left _ (.inter_right _ <| hU3 hij)]
  trans ∑ i : Fin n, 1
  · simp
  · rw [finsum_eq_sum_of_fintype]
    refine Fintype.sum_mono fun i ↦ Set.one_le_encard_iff_nonempty.mpr (show y ∈ f '' (U i) from ?_)
    convert! Set.mem_univ y
    exact IsClopen.eq_univ ⟨hf₂ _ (hU1 i).1, hf₁ _ (hU1 i).2⟩ ((hU2 i).image f)
/-
**IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connected
Space** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_conne
ctedSpace [ConnectedSpace Y] {y : Y} (hy : (f ⁻¹' {y}).Finite) : Finite (Connect
edComponents X)
参数：hy : (f ⁻¹' {y}).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.card_lt_top`：∀ {α : Type u_1}, ENat.card α < ⊤ ↔ Finite α
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`：IsO
penMap.enatCard_connectedComponents_le_encard_preimage_singleton [ConnectedSpace
 Y] (y : Y) : ENat.card (ConnectedComponents X) <= (f ⁻¹'…
· 使用定理 `Set.Finite.encard_lt_top`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.enc
ard < ⊤
-/
lemma IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace
    [ConnectedSpace Y] {y : Y} (hy : (f ⁻¹' {y}).Finite) :
    Finite (ConnectedComponents X) := by
  rw [← ENat.card_lt_top]
  exact lt_of_le_of_lt (hf₁.enatCard_connectedComponents_le_encard_preimage_singleton hf₂ y)
    hy.encard_lt_top

/-- If `f : X → Y` is continuous, open and closed with finite fibers and `Y` has finitely many
connected components, so does `X`. -/
/-
**IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton** 是 Mathlib 
中的一个引理，位于命名空间 ``。
形式化陈述：IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton [Finite 
(ConnectedComponents Y)] (hfc : Continuous f) (h : forall y, (f ⁻¹' {y}).Finite)
 : Finite (ConnectedComponents X)
参数：ConnectedComponents Y；hfc : Continuous f；h : forall y, (f ⁻¹' {y}).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConnectedComponents.surjective_coe`：surjective_coe : Surjective (mk : α 
-> ConnectedComponents α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isConnected_iff_connectedSpace`：isConnected_iff_connectedSpace {s : Set 
α} : IsConnected s ↔ ConnectedSpace s
· 使用定理 `isConnected_connectedComponent`：isConnected_connectedComponent {x : α} :
 IsConnected (connectedComponent x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `connectedComponents_preimage_singleton`：connectedComponents_preimage_sin
gleton {x : α} : (↑) ⁻¹' ({↑x} : Set (ConnectedComponents α)) = connectedCompone
nt x
· 使用引理 `IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_con
nectedSpace`：IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_o
f_connectedSpace [ConnectedSpace Y] {y : Y} (hy : (f ⁻¹' {y}).Finite) : F…
· 使用定理 `IsOpenMap.restrictPreimage`：IsOpenMap.restrictPreimage (H : IsOpenMap f)
 (s : Set β) : IsOpenMap (s.restrictPreimage f)
· 使用定理 `IsClosedMap.restrictPreimage`：IsClosedMap.restrictPreimage (H : IsClosed
Map f) (s : Set β) : IsClosedMap (s.restrictPreimage f)
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `IsClopen.preimage`：IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X
 -> Y} (hf : Continuous f) : IsClopen (f ⁻¹' s)
· 使用定理 `isClopen_discrete`：isClopen_discrete [DiscreteTopology X] (s : Set X) : 
IsClopen s
· 使用定理 `TotallyDisconnectedSpace.t1Space`：∀ {X : Type u_1} [inst : TopologicalSp
ace X] [h : TotallyDisconnectedSpace X], T1Space X
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : X → Y` is continuous, open and closed with finite fibers and `Y` has fin
itely many
connected components, so does `X`.
-/
lemma IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton
    [Finite (ConnectedComponents Y)] (hfc : Continuous f) (h : ∀ y, (f ⁻¹' {y}).Finite) :
    Finite (ConnectedComponents X) := by
  suffices h : ∀ (y : ConnectedComponents Y), Finite (ConnectedComponents (f ⁻¹' mk ⁻¹' {y})) by
    refine .of_equiv _ (equivOfIsClopen (U := fun y ↦ f ⁻¹' mk ⁻¹' {y}) ?_ ?_ ?_).symm
    · exact fun y ↦ (isClopen_discrete {y}).preimage (continuous_coe.comp hfc)
    · exact fun i j hij ↦ (Disjoint.preimage mk (by simpa)).preimage f
    · rw [Set.iUnion_eq_univ_iff]
      exact fun x ↦ ⟨mk (f x), rfl⟩
  intro y
  obtain ⟨y, rfl⟩ := surjective_coe y
  have := isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := y))
  rw [connectedComponents_preimage_singleton]
  refine IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace
    (hf₁.restrictPreimage (connectedComponent y)) (hf₂.restrictPreimage (connectedComponent y))
    (y := ⟨y, mem_connectedComponent⟩) ?_
  rw [← Set.finite_image_iff Subtype.val_injective.injOn]
  convert! h y
  aesop (add safe mem_connectedComponent)

end

