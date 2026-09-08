/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Data.Rel
public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.ContinuousOn

/-!
# Basic results on uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups.

## Main definitions

In this file we define a complete lattice structure on the type `UniformSpace X`
of uniform structures on `X`, as well as the pullback (`UniformSpace.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notation

Localized in `Uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`,
and `○` for composition of relations, seen as terms with type `Set (X × X)`.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/

@[expose] public section

open Set Filter Topology
open scoped SetRel Uniformity

universe u v ua ub uc ud

/-!
### Relations, seen as `SetRel α α`
-/

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

open scoped SetRel in
/-
**IsOpen.relComp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.relComp [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace
 γ] {s : SetRel α β} {t : SetRel β γ} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (
s ○ t)
参数：hs : IsOpen s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
lemma IsOpen.relComp [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {s : SetRel α β} {t : SetRel β γ} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ○ t) := by
  conv =>
    arg 1; equals ⋃ b, (fun p => (p.1, b)) ⁻¹' s ∩ (fun p => (b, p.2)) ⁻¹' t => ext ⟨_, _⟩; simp
  exact isOpen_iUnion fun a ↦ hs.preimage (by fun_prop) |>.inter <| ht.preimage (by fun_prop)
/-
**IsOpen.relInv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.relInv [TopologicalSpace α] [TopologicalSpace β] {s : SetRel α β} (
hs : IsOpen s) : IsOpen s.inv
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
-/
lemma IsOpen.relInv [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) : IsOpen s.inv :=
  hs.preimage continuous_swap
/-
**IsOpen.relImage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.relImage [TopologicalSpace α] [TopologicalSpace β] {s : SetRel α β}
 (hs : IsOpen s) {t : Set α} : IsOpen (s.image t)
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
-/
lemma IsOpen.relImage [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) {t : Set α} : IsOpen (s.image t) := by
  simp_rw [SetRel.image, ← exists_prop, Set.ofPred_exists]
  exact isOpen_biUnion fun _ _ => hs.preimage <| .prodMk_right _
/-
**IsOpen.relPreimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.relPreimage [TopologicalSpace α] [TopologicalSpace β] {s : SetRel α
 β} (hs : IsOpen s) {t : Set β} : IsOpen (s.preimage t)
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsOpen.relImage`：IsOpen.relImage [TopologicalSpace α] [TopologicalSpace 
β] {s : SetRel α β} (hs : IsOpen s) {t : Set α} : IsOpen (s.image t)
· 使用引理 `IsOpen.relInv`：IsOpen.relInv [TopologicalSpace α] [TopologicalSpace β] {
s : SetRel α β} (hs : IsOpen s) : IsOpen s.inv
-/
lemma IsOpen.relPreimage [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) {t : Set β} : IsOpen (s.preimage t) :=
  hs.relInv.relImage
/-
**IsClosed.relInv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.relInv [TopologicalSpace α] [TopologicalSpace β] {s : SetRel α β}
 (hs : IsClosed s) : IsClosed s.inv
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
-/
lemma IsClosed.relInv [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) : IsClosed s.inv :=
  hs.preimage continuous_swap
/-
**IsClosed.relImage_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.relImage_of_finite [TopologicalSpace α] [TopologicalSpace β] {s :
 SetRel α β} (hs : IsClosed s) {t : Set α} (ht : t.Finite) : IsClosed (s.image t
)
参数：hs : IsClosed s；ht : t.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `Set.Finite.isClosed_biUnion`：Set.Finite.isClosed_biUnion {s : Set α} {f 
: α -> Set X} (hs : s.Finite) (h : forall i in s, IsClosed (f i)) : IsClosed (⋃ 
i in s, f i)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
-/
lemma IsClosed.relImage_of_finite [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set α} (ht : t.Finite) : IsClosed (s.image t) := by
  simp_rw [SetRel.image, ← exists_prop, Set.ofPred_exists]
  exact ht.isClosed_biUnion fun _ _ => hs.preimage <| .prodMk_right _
/-
**IsClosed.relPreimage_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.relPreimage_of_finite [TopologicalSpace α] [TopologicalSpace β] {
s : SetRel α β} (hs : IsClosed s) {t : Set β} (ht : t.Finite) : IsClosed (s.prei
mage t)
参数：hs : IsClosed s；ht : t.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsClosed.relImage_of_finite`：IsClosed.relImage_of_finite [TopologicalSpa
ce α] [TopologicalSpace β] {s : SetRel α β} (hs : IsClosed s) {t : Set α} (ht : 
t.Finite) : IsClo…
· 使用引理 `IsClosed.relInv`：IsClosed.relInv [TopologicalSpace α] [TopologicalSpace 
β] {s : SetRel α β} (hs : IsClosed s) : IsClosed s.inv
-/
lemma IsClosed.relPreimage_of_finite [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set β} (ht : t.Finite) : IsClosed (s.preimage t) :=
  hs.relInv.relImage_of_finite ht

section UniformSpace

variable [UniformSpace α]

/-- If `s ∈ 𝓤 α`, then for any natural `n`, for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ○ ... ○ t ⊆ s` (`n` compositions). -/
/-
**eventually_uniformity_iterate_comp_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_uniformity_iterate_comp_subset {s : SetRel α α} (hs : s in 𝓤 α)
 (n : Nat) : forallᶠ t in (𝓤 α).smallSets, (t ○ ·)^[n] t subseteq s
参数：hs : s in 𝓤 α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `isRefl_of_mem_uniformity`：isRefl_of_mem_uniformity {s : SetRel α α} (h :
 s in 𝓤 α) : s.IsRefl
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `SetRel.left_subset_comp`：left_subset_comp {R : SetRel α β} [S.IsRefl] : 
R subseteq R ○ S
· 使用引理 `SetRel.comp_subset_comp`：comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ 
subseteq R₂) (hS : S₁ subseteq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_and`：eventually_and {p q : α -> Prop} {f : Filter α} :
 (forallᶠ x in f, p x ∧ q x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in f, q x

--- 原说明 ---
If `s ∈ 𝓤 α`, then for any natural `n`, for a subset `t` of a sufficiently small
 set in `𝓤 α`,
we have `t ○ t ○ ... ○ t ⊆ s` (`n` compositions).
-/
theorem eventually_uniformity_iterate_comp_subset {s : SetRel α α} (hs : s ∈ 𝓤 α) (n : ℕ) :
    ∀ᶠ t in (𝓤 α).smallSets, (t ○ ·)^[n] t ⊆ s := by
  suffices ∀ᶠ t in (𝓤 α).smallSets, t ⊆ s ∧ (t ○ ·)^[n] t ⊆ s from (eventually_and.1 this).2
  induction n generalizing s with
  | zero => simpa
  | succ _ ihn =>
    rcases comp_mem_uniformity_sets hs with ⟨t, htU, hts⟩
    refine (ihn htU).mono fun U hU => ?_
    rw [Function.iterate_succ_apply']
    have := isRefl_of_mem_uniformity htU
    exact ⟨hU.1.trans <| SetRel.left_subset_comp.trans hts,
     (SetRel.comp_subset_comp hU.1 hU.2).trans hts⟩

/-- If `s ∈ 𝓤 α`, then for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ⊆ s`. -/
/-
**eventually_uniformity_comp_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_uniformity_comp_subset {s : SetRel α α} (hs : s in 𝓤 α) : foral
lᶠ t in (𝓤 α).smallSets, t ○ t subseteq s
参数：hs : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_uniformity_iterate_comp_subset`：eventually_uniformity_iterate
_comp_subset {s : SetRel α α} (hs : s in 𝓤 α) (n : Nat) : forallᶠ t in (𝓤 α).sma
llSets, (t ○ ·)^[n] t subseteq …

--- 原说明 ---
If `s ∈ 𝓤 α`, then for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ⊆ s`.
-/
theorem eventually_uniformity_comp_subset {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∀ᶠ t in (𝓤 α).smallSets, t ○ t ⊆ s :=
  eventually_uniformity_iterate_comp_subset hs 1

/-!
### Balls in uniform spaces
-/

namespace UniformSpace

open UniformSpace (ball)

/-
**UniformSpace.isOpen_ball** 是 Mathlib 中的一个引理，位于命名空间 `UniformSpace`。
形式化陈述：isOpen_ball (x : α) {V : SetRel α α} (hV : IsOpen V) : IsOpen (ball x V)
参数：x : α；hV : IsOpen V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
-/
lemma isOpen_ball (x : α) {V : SetRel α α} (hV : IsOpen V) : IsOpen (ball x V) :=
  hV.preimage <| .prodMk_right _
/-
**UniformSpace.isClosed_ball** 是 Mathlib 中的一个引理，位于命名空间 `UniformSpace`。
形式化陈述：isClosed_ball (x : α) {V : SetRel α α} (hV : IsClosed V) : IsClosed (ball 
x V)
参数：x : α；hV : IsClosed V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
-/
lemma isClosed_ball (x : α) {V : SetRel α α} (hV : IsClosed V) : IsClosed (ball x V) :=
  hV.preimage <| .prodMk_right _

/-!
### Neighborhoods in uniform spaces
-/

/-
**UniformSpace.hasBasis_nhds_prod** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：hasBasis_nhds_prod (x y : α) : HasBasis (𝓝 (x, y)) (fun s => s in 𝓤 α ∧ Se
tRel.IsSymm s) fun s => ball x s ×ˢ ball y s
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.HasBasis.prod_same_index`：∀ {α : Type u_1} {β : Type u_2} {ι : So
rt u_4} {la : Filter α} {sa : ι → Set α} {lb : Filter β} {p : ι → Prop}   {sb : 
ι → Set β},   la.HasB…
· 使用定理 `UniformSpace.hasBasis_nhds`：UniformSpace.hasBasis_nhds (x : α) : HasBasi
s (𝓝 x) (fun s : SetRel α α => s in 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s
· 使用定理 `Filter.inter_sets`：∀ {α : Type u_1} (self : Filter α) {x y : Set α}, x ∈
 self.sets → y ∈ self.sets → x ∩ y ∈ self.sets
· 使用定理 `UniformSpace.ball_inter_left`：ball_inter_left (x : β) (V W : Set (β × β)
) : ball x (V inter W) subseteq ball x V
· 使用定理 `UniformSpace.ball_inter_right`：ball_inter_right (x : β) (V W : Set (β × 
β)) : ball x (V inter W) subseteq ball x W

--- 原说明 ---
### Neighborhoods in uniform spaces
-/
theorem hasBasis_nhds_prod (x y : α) :
    HasBasis (𝓝 (x, y)) (fun s => s ∈ 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s ×ˢ ball y s := by
  rw [nhds_prod_eq]
  apply (hasBasis_nhds x).prod_same_index (hasBasis_nhds y)
  rintro U V ⟨U_in, U_symm⟩ ⟨V_in, V_symm⟩
  exact ⟨U ∩ V, ⟨(𝓤 α).inter_sets U_in V_in, inferInstance⟩, ball_inter_left x U V,
    ball_inter_right y U V⟩

end UniformSpace

open UniformSpace

/-
**nhds_eq_uniformity_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_eq_uniformity_prod {a b : α} : 𝓝 (a, b) = (𝓤 α).lift' fun s : SetRel 
α α => { y : α | (y, a) in s } ×ˢ { y : α | (b, y) in s }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `nhds_nhds_eq_uniformity_uniformity_prod`：nhds_nhds_eq_uniformity_uniform
ity_prod {a b : α} : 𝓝 a ×ˢ 𝓝 b = (𝓤 α).lift fun s : SetRel α α => (𝓤 α).lift' f
un t => { y : α | (y, a) in s…
· 使用定理 `Filter.lift_lift'_same_eq_lift'`：∀ {α : Type u_1} {β : Type u_2} {f : Fi
lter α} {g : Set α → Set α → Set β},   (∀ (s : Set α), Monotone fun t => g s t) 
→     (∀ (t : Set α),…
· 使用定理 `Monotone.set_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst 
: Preorder α] {f : α → Set β} {g : α → Set γ},   Monotone f → Monotone g → Monot
one fun…
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
· 使用定理 `Set.monotone_preimage`：monotone_preimage {f : α -> β} : Monotone (preima
ge f)
-/
theorem nhds_eq_uniformity_prod {a b : α} :
    𝓝 (a, b) =
      (𝓤 α).lift' fun s : SetRel α α => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ s } := by
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift']
  · exact fun s => monotone_const.set_prod monotone_preimage
  · refine fun t => Monotone.set_prod ?_ monotone_const
    exact monotone_preimage (f := fun y => (y, a))
/-
**nhdset_of_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdset_of_mem_uniformity {d : SetRel α α} (s : SetRel α α) (hd : d in 𝓤 α)
 : exists t : SetRel α α, IsOpen t ∧ s subseteq t ∧ t subseteq { p | exists x y,
 (p.1, x) in d ∧ (x, y) in s ∧ (y, p.2) in d }
参数：s : SetRel α α；hd : d in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_uniformity_prod`：nhds_eq_uniformity_prod {a b : α} : 𝓝 (a, b) = 
(𝓤 α).lift' fun s : SetRel α α => { y : α | (y, a) in s } ×ˢ { y : α | (b, y) in
 s }
· 使用定理 `Filter.mem_lift'_sets`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {h
 : Set α → Set β},   Monotone h → ∀ {s : Set β}, s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ 
s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem nhdset_of_mem_uniformity {d : SetRel α α} (s : SetRel α α) (hd : d ∈ 𝓤 α) :
    ∃ t : SetRel α α, IsOpen t ∧ s ⊆ t ∧
      t ⊆ { p | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d } := by
  let cl_d := { p : α × α | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d }
  have : ∀ p ∈ s, ∃ t, t ⊆ cl_d ∧ IsOpen t ∧ p ∈ t := fun ⟨x, y⟩ hp =>
    mem_nhds_iff.mp <|
      show cl_d ∈ 𝓝 (x, y) by
        rw [nhds_eq_uniformity_prod, mem_lift'_sets]
        · exact ⟨d, hd, fun ⟨a, b⟩ ⟨ha, hb⟩ => ⟨x, y, ha, hp, hb⟩⟩
        · exact fun _ _ h _ h' => ⟨h h'.1, h h'.2⟩
  choose t ht using this
  exact ⟨(⋃ p : α × α, ⋃ h : p ∈ s, t p h : SetRel α α),
    isOpen_iUnion fun p : α × α => isOpen_iUnion fun hp => (ht p hp).right.left,
    fun ⟨a, b⟩ hp => by
      simp only [mem_iUnion, Prod.exists]; exact ⟨a, b, hp, (ht (a, b) hp).right.right⟩,
    iUnion_subset fun p => iUnion_subset fun hp => (ht p hp).left⟩

/-- Entourages are neighborhoods of the diagonal. -/
/-
**nhds_le_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_le_uniformity (x : α) : 𝓝 (x, x) <= 𝓤 α
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `UniformSpace.mem_comp_of_mem_ball`：mem_comp_of_mem_ball {V W : SetRel β 
β} {x y z : β} [V.IsSymm] (hx : x in ball z V) (hy : y in ball z W) : (x, y) in 
V ○ W

--- 原说明 ---
Entourages are neighborhoods of the diagonal.
-/
theorem nhds_le_uniformity (x : α) : 𝓝 (x, x) ≤ 𝓤 α := by
  intro V V_in
  rcases comp_symm_mem_uniformity_sets V_in with ⟨w, w_in, w_symm, w_sub⟩
  have : ball x w ×ˢ ball x w ∈ 𝓝 (x, x) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in)
  apply mem_of_superset this
  rintro ⟨u, v⟩ ⟨u_in, v_in⟩
  exact w_sub (mem_comp_of_mem_ball u_in v_in)

/-- Entourages are neighborhoods of the diagonal. -/
/-
**iSup_nhds_le_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_nhds_le_uniformity : ⨆ x : α, 𝓝 (x, x) <= 𝓤 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `nhds_le_uniformity`：nhds_le_uniformity (x : α) : 𝓝 (x, x) <= 𝓤 α

--- 原说明 ---
Entourages are neighborhoods of the diagonal.
-/
theorem iSup_nhds_le_uniformity : ⨆ x : α, 𝓝 (x, x) ≤ 𝓤 α :=
  iSup_le nhds_le_uniformity

/-- Entourages are neighborhoods of the diagonal. -/
/-
**nhdsSet_diagonal_le_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_diagonal_le_uniformity : 𝓝ˢ (diagonal α) <= 𝓤 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `nhdsSet_diagonal`：nhdsSet_diagonal (X) [TopologicalSpace (X × X)] : 𝓝ˢ (
diagonal X) = ⨆ (x : X), 𝓝 (x, x)
· 使用定理 `iSup_nhds_le_uniformity`：iSup_nhds_le_uniformity : ⨆ x : α, 𝓝 (x, x) <= 
𝓤 α

--- 原说明 ---
Entourages are neighborhoods of the diagonal.
-/
theorem nhdsSet_diagonal_le_uniformity : 𝓝ˢ (diagonal α) ≤ 𝓤 α :=
  (nhdsSet_diagonal α).trans_le iSup_nhds_le_uniformity

section

variable (α)

/-
**UniformSpace.has_seq_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.has_seq_basis [IsCountablyGenerated <| 𝓤 α] : exists V : Nat 
-> SetRel α α, HasAntitoneBasis (𝓤 α) V ∧ forall n, SetRel.IsSymm (V n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.exists_antitone_subbasis`：∀ {α : Type u_1} {ι' : Sort u_
5} {f : Filter α} [h : f.IsCountablyGenerated] {p : ι' → Prop} {s : ι' → Set α},
   f.HasBasis p s → ∃ x, (∀ (i…
· 使用定理 `UniformSpace.hasBasis_symmetric`：UniformSpace.hasBasis_symmetric : (𝓤 α)
.HasBasis (fun s : SetRel α α => s in 𝓤 α ∧ SetRel.IsSymm s) id
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem UniformSpace.has_seq_basis [IsCountablyGenerated <| 𝓤 α] :
    ∃ V : ℕ → SetRel α α, HasAntitoneBasis (𝓤 α) V ∧ ∀ n, SetRel.IsSymm (V n) :=
  let ⟨U, hsym, hbasis⟩ := (@UniformSpace.hasBasis_symmetric α _).exists_antitone_subbasis
  ⟨U, hbasis, fun n => (hsym n).2⟩

end

/-!
### Closure and interior in uniform spaces
-/

/-
**closure_eq_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_eq_uniformity (s : Set <| α × α) : closure s = ⋂ V in {V | V in 𝓤 
α ∧ SetRel.IsSymm V}, V ○ s ○ V
参数：s : Set <| α × α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhds_basis`：mem_closure_iff_nhds_basis {p : ι -> Prop} {
s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> exi
sts y in t, y in…
· 使用定理 `UniformSpace.hasBasis_nhds_prod`：hasBasis_nhds_prod (x y : α) : HasBasis
 (𝓝 (x, y)) (fun s => s in 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s ×ˢ ball y s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Closure and interior in uniform spaces
-/
theorem closure_eq_uniformity (s : Set <| α × α) :
    closure s = ⋂ V ∈ {V | V ∈ 𝓤 α ∧ SetRel.IsSymm V}, V ○ s ○ V := by
  ext ⟨x, y⟩
  simp +contextual only
    [mem_closure_iff_nhds_basis (UniformSpace.hasBasis_nhds_prod x y), mem_iInter, mem_ofPred_eq,
      and_imp, mem_comp_comp, ← mem_inter_iff, inter_comm, Set.Nonempty]
/-
**uniformity_hasBasis_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_hasBasis_closed : HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 
α ∧ IsClosed V) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `comp_comp_symm_mem_uniformity_sets`：comp_comp_symm_mem_uniformity_sets {
s : SetRel α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t ○ t s
ubseteq s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_eq_uniformity`：closure_eq_uniformity (s : Set <| α × α) : closur
e s = ⋂ V in {V | V in 𝓤 α ∧ SetRel.IsSymm V}, V ○ s ○ V
· 使用定理 `Set.iInter_subset_of_subset`：iInter_subset_of_subset {s : ι -> Set α} {t
 : Set α} (i : ι) (h : s i subseteq t) : ⋂ i, s i subseteq t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem uniformity_hasBasis_closed :
    HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α ∧ IsClosed V) id := by
  refine Filter.hasBasis_self.2 fun t h => ?_
  rcases comp_comp_symm_mem_uniformity_sets h with ⟨w, w_in, w_symm, r⟩
  refine ⟨closure w, mem_of_superset w_in subset_closure, isClosed_closure, ?_⟩
  refine Subset.trans ?_ r
  rw [closure_eq_uniformity]
  apply iInter_subset_of_subset
  apply iInter_subset
  exact ⟨w_in, w_symm⟩
/-
**uniformity_eq_uniformity_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_eq_uniformity_closure : 𝓤 α = (𝓤 α).lift' closure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.HasBasis.lift'_closure_eq_self`：∀ {X : Type u} [inst : Topologica
lSpace X] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBas
is p s → (∀ (i : ι), p i → …
· 使用定理 `uniformity_hasBasis_closed`：uniformity_hasBasis_closed : HasBasis (𝓤 α) 
(fun V : SetRel α α => V in 𝓤 α ∧ IsClosed V) id
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem uniformity_eq_uniformity_closure : 𝓤 α = (𝓤 α).lift' closure :=
  Eq.symm <| uniformity_hasBasis_closed.lift'_closure_eq_self fun _ => And.right
/-
**Filter.HasBasis.uniformity_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformity_closure {p : ι -> Prop} {U : ι -> SetRel α α} (
h : (𝓤 α).HasBasis p U) : (𝓤 α).HasBasis p fun i => closure (U i)
参数：h : (𝓤 α).HasBasis p U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `Filter.HasBasis.lift'_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {ι : Sort v} {l : Filter X} {p : ι → Prop} {s : ι → Set X},   l.HasBasis p s →
 (l.lift' closure).…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `uniformity_eq_uniformity_closure`：uniformity_eq_uniformity_closure : 𝓤 α
 = (𝓤 α).lift' closure
-/
theorem Filter.HasBasis.uniformity_closure {p : ι → Prop} {U : ι → SetRel α α}
    (h : (𝓤 α).HasBasis p U) : (𝓤 α).HasBasis p fun i => closure (U i) :=
  (@uniformity_eq_uniformity_closure α _).symm ▸ h.lift'_closure

/-- Closed entourages form a basis of the uniformity filter. -/
/-
**uniformity_hasBasis_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_hasBasis_closure : HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤
 α) closure
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.uniformity_closure`：Filter.HasBasis.uniformity_closure {
p : ι -> Prop} {U : ι -> SetRel α α} (h : (𝓤 α).HasBasis p U) : (𝓤 α).HasBasis p
 fun i => closure (U i)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id

--- 原说明 ---
Closed entourages form a basis of the uniformity filter.
-/
theorem uniformity_hasBasis_closure : HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α) closure :=
  (𝓤 α).basis_sets.uniformity_closure
/-
**closure_eq_inter_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_eq_inter_uniformity {t : SetRel α α} : closure t = ⋂ d in 𝓤 α, d ○
 (t ○ d)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_eq_uniformity`：closure_eq_uniformity (s : Set <| α × α) : closur
e s = ⋂ V in {V | V in 𝓤 α ∧ SetRel.IsSymm V}, V ○ s ○ V
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.HasBasis.biInter_mem`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {f : Set α → Set β},   l.HasBa
sis p s → Monoton…
· 使用定理 `UniformSpace.hasBasis_symmetric`：UniformSpace.hasBasis_symmetric : (𝓤 α)
.HasBasis (fun s : SetRel α α => s in 𝓤 α ∧ SetRel.IsSymm s) id
· 使用引理 `SetRel.comp_subset_comp`：comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ 
subseteq R₂) (hS : S₁ subseteq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂
· 使用引理 `SetRel.comp_subset_comp_left`：comp_subset_comp_left {S : SetRel β γ} (hR
 : R₁ subseteq R₂) : R₁ ○ S subseteq R₂ ○ S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `SetRel.comp_assoc`：comp_assoc (R : SetRel α β) (S : SetRel β γ) (t : Set
Rel γ δ) : (R ○ S) ○ t = R ○ (S ○ t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_eq_inter_uniformity {t : SetRel α α} : closure t = ⋂ d ∈ 𝓤 α, d ○ (t ○ d) :=
  calc
    closure t = ⋂ (V) (_ : V ∈ 𝓤 α ∧ SetRel.IsSymm V), V ○ t ○ V := closure_eq_uniformity t
    _ = ⋂ V ∈ 𝓤 α, V ○ t ○ V :=
      Eq.symm <| UniformSpace.hasBasis_symmetric.biInter_mem fun _ _ hV => by gcongr
    _ = ⋂ V ∈ 𝓤 α, V ○ (t ○ V) := by simp [SetRel.comp_assoc]
/-
**uniformity_eq_uniformity_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_eq_uniformity_interior : 𝓤 α = (𝓤 α).lift' interior
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `comp3_mem_uniformity`：comp3_mem_uniformity {s : SetRel α α} (hs : s in 𝓤
 α) : exists t in 𝓤 α, t ○ (t ○ t) subseteq s
· 使用定理 `nhdset_of_mem_uniformity`：nhdset_of_mem_uniformity {d : SetRel α α} (s :
 SetRel α α) (hd : d in 𝓤 α) : exists t : SetRel α α, IsOpen t ∧ s subseteq t ∧ 
t subseteq { p…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.subset_interior_iff`：IsOpen.subset_interior_iff (h₁ : IsOpen s) :
 s subseteq interior t ↔ s subseteq t
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.sets_of_superset`：∀ {α : Type u_1} (self : Filter α) {x y : Set α
}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem uniformity_eq_uniformity_interior : 𝓤 α = (𝓤 α).lift' interior :=
  le_antisymm
    (le_iInf₂ fun d hd => by
      let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
      let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs
      have : s ⊆ interior d :=
        calc
          s ⊆ t := hst
          _ ⊆ interior d :=
            ht.subset_interior_iff.mpr fun x (hx : x ∈ t) =>
              let ⟨x, y, h₁, h₂, h₃⟩ := ht_comp hx
              hs_comp ⟨x, h₁, y, h₂, h₃⟩
      have : interior d ∈ 𝓤 α := by filter_upwards [hs] using this
      simp [this])
    fun _ hs => ((𝓤 α).lift' interior).sets_of_superset (mem_lift' hs) interior_subset
/-
**interior_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_mem_uniformity {s : SetRel α α} (hs : s in 𝓤 α) : interior s in 𝓤
 α
参数：hs : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_eq_uniformity_interior`：uniformity_eq_uniformity_interior : 𝓤
 α = (𝓤 α).lift' interior
· 使用定理 `Filter.mem_lift'`：mem_lift' {t : Set α} (ht : t in f) : h t in f.lift' h
-/
theorem interior_mem_uniformity {s : SetRel α α} (hs : s ∈ 𝓤 α) : interior s ∈ 𝓤 α := by
  rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs
/-
**mem_uniformity_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_uniformity_isClosed {s : SetRel α α} (h : s in 𝓤 α) : exists t in 𝓤 α,
 IsClosed t ∧ t subseteq s
参数：h : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `uniformity_hasBasis_closed`：uniformity_hasBasis_closed : HasBasis (𝓤 α) 
(fun V : SetRel α α => V in 𝓤 α ∧ IsClosed V) id
-/
theorem mem_uniformity_isClosed {s : SetRel α α} (h : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, IsClosed t ∧ t ⊆ s :=
  let ⟨t, ⟨ht_mem, htc⟩, hts⟩ := uniformity_hasBasis_closed.mem_iff.1 h
  ⟨t, ht_mem, htc, hts⟩
/-
**isOpen_iff_isOpen_ball_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iff_isOpen_ball_subset {s : Set α} : IsOpen s ↔ forall x in s, exis
ts V in 𝓤 α, IsOpen V ∧ ball x V subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_ball_subset`：isOpen_iff_ball_subset {s : Set α} : IsOpen s ↔ 
forall x in s, exists V in 𝓤 α, ball x V subseteq s
· 使用定理 `interior_mem_uniformity`：interior_mem_uniformity {s : SetRel α α} (hs : 
s in 𝓤 α) : interior s in 𝓤 α
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem isOpen_iff_isOpen_ball_subset {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, IsOpen V ∧ ball x V ⊆ s := by
  rw [isOpen_iff_ball_subset]
  constructor <;> intro h x hx
  · obtain ⟨V, hV, hV'⟩ := h x hx
    exact
      ⟨interior V, interior_mem_uniformity hV, isOpen_interior,
        (ball_mono interior_subset x).trans hV'⟩
  · obtain ⟨V, hV, -, hV'⟩ := h x hx
    exact ⟨V, hV, hV'⟩
/-
**closure_ball_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_ball_subset {x : α} {V : SetRel α α} : closure (ball x V) subseteq
 ball x (closure V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.closure_preimage_subset`：Continuous.closure_preimage_subset (
hf : Continuous f) (t : Set Y) : closure (f ⁻¹' t) subseteq f ⁻¹' closure t
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
-/
theorem closure_ball_subset {x : α} {V : SetRel α α} : closure (ball x V) ⊆ ball x (closure V) :=
  (Continuous.prodMk_right x).closure_preimage_subset V

/-- The uniform neighborhoods of all points of a dense set cover the whole space. -/
/-
**Dense.biUnion_uniformity_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.biUnion_uniformity_ball {s : Set α} {U : SetRel α α} (hs : Dense s) 
(hU : U in 𝓤 α) : ⋃ x in s, ball x U = univ
参数：hs : Dense s；hU : U in 𝓤 α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion₂_eq_univ_iff`：iUnion₂_eq_univ_iff {s : forall i, κ i -> Set α
} : ⋃ (i) (j), s i j = univ ↔ forall a, exists i j, a in s i j
· 使用定理 `Dense.inter_nhds_nonempty`：Dense.inter_nhds_nonempty (hs : Dense s) (ht 
: t in 𝓝 x) : (s inter t).Nonempty
· 使用定理 `mem_nhds_right`：mem_nhds_right (y : α) {s : SetRel α α} (h : s in 𝓤 α) :
 { x : α | (x, y) in s } in 𝓝 y

--- 原说明 ---
The uniform neighborhoods of all points of a dense set cover the whole space.
-/
theorem Dense.biUnion_uniformity_ball {s : Set α} {U : SetRel α α} (hs : Dense s) (hU : U ∈ 𝓤 α) :
    ⋃ x ∈ s, ball x U = univ := by
  refine iUnion₂_eq_univ_iff.2 fun y => ?_
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with ⟨x, hxs, hxy : (x, y) ∈ U⟩
  exact ⟨x, hxs, hxy⟩

/-- The uniform neighborhoods of all points of a dense indexed collection cover the whole space. -/
/-
**DenseRange.iUnion_uniformity_ball** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DenseRange.iUnion_uniformity_ball {ι : Type*} {xs : ι -> α} (xs_dense : De
nseRange xs) {U : SetRel α α} (hU : U in uniformity α) : ⋃ i, UniformSpace.ball 
(xs i) U = univ
参数：xs_dense : DenseRange xs；hU : U in uniformity α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_range`：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in 
range f, g x = ⋃ y, g (f y)
· 使用定理 `Dense.biUnion_uniformity_ball`：Dense.biUnion_uniformity_ball {s : Set α}
 {U : SetRel α α} (hs : Dense s) (hU : U in 𝓤 α) : ⋃ x in s, ball x U = univ

--- 原说明 ---
The uniform neighborhoods of all points of a dense indexed collection cover the 
whole space.
-/
lemma DenseRange.iUnion_uniformity_ball {ι : Type*} {xs : ι → α}
    (xs_dense : DenseRange xs) {U : SetRel α α} (hU : U ∈ uniformity α) :
    ⋃ i, UniformSpace.ball (xs i) U = univ := by
  rw [← biUnion_range (f := xs) (g := fun x ↦ UniformSpace.ball x U)]
  exact Dense.biUnion_uniformity_ball xs_dense hU

/-!
### Uniformity bases
-/

/-- Open elements of `𝓤 α` form a basis of `𝓤 α`. -/
/-
**uniformity_hasBasis_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_hasBasis_open : HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 α 
∧ IsOpen V) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `interior_mem_uniformity`：interior_mem_uniformity {s : SetRel α α} (hs : 
s in 𝓤 α) : interior s in 𝓤 α
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
Open elements of `𝓤 α` form a basis of `𝓤 α`.
-/
theorem uniformity_hasBasis_open : HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α ∧ IsOpen V) id :=
  hasBasis_self.2 fun s hs =>
    ⟨interior s, interior_mem_uniformity hs, isOpen_interior, interior_subset⟩
/-
**Filter.HasBasis.mem_uniformity_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.mem_uniformity_iff {p : β -> Prop} {s : β -> SetRel α α} (
h : (𝓤 α).HasBasis p s) {t : SetRel α α} : t in 𝓤 α ↔ exists i, p i ∧ forall a b
, (a, b) in s i -> (a, b) in t
参数：h : (𝓤 α).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
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
theorem Filter.HasBasis.mem_uniformity_iff {p : β → Prop} {s : β → SetRel α α}
    (h : (𝓤 α).HasBasis p s) {t : SetRel α α} :
    t ∈ 𝓤 α ↔ ∃ i, p i ∧ ∀ a b, (a, b) ∈ s i → (a, b) ∈ t :=
  h.mem_iff.trans <| by simp only [Prod.forall, subset_def]

/-- Open elements `s : SetRel α α` of `𝓤 α` such that `(x, y) ∈ s ↔ (y, x) ∈ s` form a basis
of `𝓤 α`. -/
/-
**uniformity_hasBasis_open_symmetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_hasBasis_open_symmetric : HasBasis (𝓤 α) (fun V : SetRel α α =>
 V in 𝓤 α ∧ IsOpen V ∧ SetRel.IsSymm V) id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.restrict`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : ι → Prop}, (∀ (i : ι)
, p i → ∃ j, p…
· 使用定理 `uniformity_hasBasis_open`：uniformity_hasBasis_open : HasBasis (𝓤 α) (fun
 V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id
· 使用定理 `symmetrize_mem_uniformity`：symmetrize_mem_uniformity {V : SetRel α α} (h
 : V in 𝓤 α) : SetRel.symmetrize V in 𝓤 α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
· 使用引理 `SetRel.symmetrize_subset_self`：symmetrize_subset_self : R.symmetrize sub
seteq R

--- 原说明 ---
Open elements `s : SetRel α α` of `𝓤 α` such that `(x, y) ∈ s ↔ (y, x) ∈ s` form
 a basis
of `𝓤 α`.
-/
theorem uniformity_hasBasis_open_symmetric :
    HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α ∧ IsOpen V ∧ SetRel.IsSymm V) id := by
  simp only [← and_assoc]
  refine uniformity_hasBasis_open.restrict fun s hs => ⟨SetRel.symmetrize s, ?_⟩
  exact
    ⟨⟨symmetrize_mem_uniformity hs.1, IsOpen.inter hs.2 (hs.2.preimage continuous_swap)⟩,
      inferInstance, SetRel.symmetrize_subset_self⟩
/-
**comp_open_symm_mem_uniformity_sets** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_open_symm_mem_uniformity_sets {s : SetRel α α} (hs : s in 𝓤 α) : exis
ts t in 𝓤 α, IsOpen t ∧ SetRel.IsSymm t ∧ t ○ t subseteq s
参数：hs : s in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `uniformity_hasBasis_open_symmetric`：uniformity_hasBasis_open_symmetric :
 HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 α ∧ IsOpen V ∧ SetRel.IsSymm V) id
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SetRel.comp_subset_comp`：comp_subset_comp {S₁ S₂ : SetRel β γ} (hR : R₁ 
subseteq R₂) (hS : S₁ subseteq S₂) : R₁ ○ S₁ subseteq R₂ ○ S₂
-/
theorem comp_open_symm_mem_uniformity_sets {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, IsOpen t ∧ SetRel.IsSymm t ∧ t ○ t ⊆ s := by
  obtain ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hu₄ : u ⊆ t⟩ := uniformity_hasBasis_open_symmetric.mem_iff.mp ht₁
  exact ⟨u, hu₁, hu₂, hu₃, (SetRel.comp_subset_comp hu₄ hu₄).trans ht₂⟩

end UniformSpace

open uniformity

section Constructions

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (UniformSpace α) :=
  PartialOrder.lift (fun u => 𝓤[u]) fun _ _ => UniformSpace.ext
/-
**UniformSpace.le_def** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, u₁ ≤ u₂ ↔ uniformity α ≤ uniform
ity α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem UniformSpace.le_def {u₁ u₂ : UniformSpace α} : u₁ ≤ u₂ ↔ 𝓤[u₁] ≤ 𝓤[u₂] := Iff.rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (UniformSpace α) :=
  ⟨fun s =>
    UniformSpace.ofCore
      { uniformity := ⨅ u ∈ s, 𝓤[u]
        refl := le_iInf fun u => le_iInf fun _ => u.toCore.refl
        symm := le_iInf₂ fun u hu =>
          le_trans (map_mono <| iInf_le_of_le _ <| iInf_le _ hu) u.symm
        comp := le_iInf₂ fun u hu =>
          le_trans (lift'_mono (iInf_le_of_le _ <| iInf_le _ hu) <| le_rfl) u.comp }⟩
/-
**UniformSpace.sInf_le** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：∀ {α : Type ua} {tt : Set (UniformSpace α)} {t : UniformSpace α}, t ∈ tt →
 sInf tt ≤ t
参数：UniformSpace α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
-/
protected theorem UniformSpace.sInf_le {tt : Set (UniformSpace α)} {t : UniformSpace α}
    (h : t ∈ tt) : sInf tt ≤ t :=
  show ⨅ u ∈ tt, 𝓤[u] ≤ 𝓤[t] from iInf₂_le t h
/-
**UniformSpace.le_sInf** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：∀ {α : Type ua} {tt : Set (UniformSpace α)} {t : UniformSpace α}, (∀ t' ∈ 
tt, t ≤ t') → t ≤ sInf tt
参数：UniformSpace α；∀ t' ∈ tt, t ≤ t'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
-/
protected theorem UniformSpace.le_sInf {tt : Set (UniformSpace α)} {t : UniformSpace α}
    (h : ∀ t' ∈ tt, t ≤ t') : t ≤ sInf tt :=
  show 𝓤[t] ≤ ⨅ u ∈ tt, 𝓤[u] from le_iInf₂ h
/-
**UniformSpace.isGLB_sInf** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：∀ {α : Type ua} {tt : Set (UniformSpace α)}, IsGLB tt (sInf tt)
参数：UniformSpace α；sInf tt。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.sInf_le`：∀ {α : Type ua} {tt : Set (UniformSpace α)} {t : U
niformSpace α}, t ∈ tt → sInf tt ≤ t
· 使用定理 `UniformSpace.le_sInf`：∀ {α : Type ua} {tt : Set (UniformSpace α)} {t : U
niformSpace α}, (∀ t' ∈ tt, t ≤ t') → t ≤ sInf tt
-/
protected theorem UniformSpace.isGLB_sInf {tt : Set (UniformSpace α)} : IsGLB tt (sInf tt) :=
  ⟨fun _ ↦ UniformSpace.sInf_le, fun _ ↦ UniformSpace.le_sInf⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (UniformSpace α) :=
  ⟨@UniformSpace.mk α ⊤ ⊤ le_top le_top fun x ↦ by simp only [nhds_top, comap_top]⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (UniformSpace α) :=
  ⟨{  toTopologicalSpace := ⊥
      uniformity := 𝓟 SetRel.id
      symm := by simp [Tendsto, SetRel.id]
      comp := lift'_le (mem_principal_self _) <| principal_mono.2 (SetRel.id_comp _).subset
      nhds_eq_comap_uniformity := fun s => by
        let _ : TopologicalSpace α := ⊥; have := discreteTopology_bot α
        simp [SetRel.id] }⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (UniformSpace α) :=
  ⟨fun u₁ u₂ =>
    { uniformity := 𝓤[u₁] ⊓ 𝓤[u₂]
      symm := u₁.symm.inf u₂.symm
      comp := (lift'_inf_le _ _ _).trans <| inf_le_inf u₁.comp u₂.comp
      toTopologicalSpace := u₁.toTopologicalSpace ⊓ u₂.toTopologicalSpace
      nhds_eq_comap_uniformity := fun _ ↦ by
        rw [@nhds_inf _ u₁.toTopologicalSpace _, @nhds_eq_comap_uniformity _ u₁,
          @nhds_eq_comap_uniformity _ u₂, comap_inf] }⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (UniformSpace α) where
  sup a b := sInf { x | a ≤ x ∧ b ≤ x }
  le_sup_left _ _ := UniformSpace.le_sInf fun _ ⟨h, _⟩ => h
  le_sup_right _ _ := UniformSpace.le_sInf fun _ ⟨_, h⟩ => h
  sup_le _ _ _ h₁ h₂ := UniformSpace.sInf_le ⟨h₁, h₂⟩
  inf := (· ⊓ ·)
  le_inf a _ _ h₁ h₂ := show a.uniformity ≤ _ from le_inf h₁ h₂
  inf_le_left a _ := show _ ≤ a.uniformity from inf_le_left
  inf_le_right _ b := show _ ≤ b.uniformity from inf_le_right
  le_top a := show a.uniformity ≤ ⊤ from le_top
  bot_le u := u.toCore.refl
  sSup tt := sInf { t | ∀ t' ∈ tt, t' ≤ t }
  isLUB_sSup _ := isGLB_upperBounds.mp UniformSpace.isGLB_sInf
  isGLB_sInf _ := UniformSpace.isGLB_sInf
/-
**iInf_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} : 𝓤[iInf u] = ⨅ i, 𝓤
[u i]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
theorem iInf_uniformity {ι : Sort*} {u : ι → UniformSpace α} : 𝓤[iInf u] = ⨅ i, 𝓤[u i] :=
  iInf_range
/-
**inf_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_uniformity {u v : UniformSpace α} : 𝓤[u ⊓ v] = 𝓤[u] ⊓ 𝓤[v]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_uniformity {u v : UniformSpace α} : 𝓤[u ⊓ v] = 𝓤[u] ⊓ 𝓤[v] := rfl
/-
**bot_uniformity** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bot_uniformity : 𝓤[(⊥ : UniformSpace α)] = 𝓟 SetRel.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bot_uniformity : 𝓤[(⊥ : UniformSpace α)] = 𝓟 SetRel.id := rfl
/-
**top_uniformity** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：top_uniformity : 𝓤[(⊤ : UniformSpace α)] = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma top_uniformity : 𝓤[(⊤ : UniformSpace α)] = ⊤ := rfl
/-
**inhabitedUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：inhabitedUniformSpace : Inhabited (UniformSpace α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedUniformSpace : Inhabited (UniformSpace α) :=
  ⟨⊥⟩
/-
**inhabitedUniformSpaceCore** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：inhabitedUniformSpaceCore : Inhabited (UniformSpace.Core α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedUniformSpaceCore : Inhabited (UniformSpace.Core α) :=
  ⟨@UniformSpace.toCore _ default⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Unique (UniformSpace α) where
  uniq u := bot_unique <| le_principal_iff.2 <| by
    rw [SetRel.id, ← diagonal, diagonal_eq_univ]; exact univ_mem

/-- Given `f : α → β` and a uniformity `u` on `β`, the inverse image of `u` under `f`
  is the inverse image in the filter sense of the induced function `α × α → β × β`.
  See note [reducible non-instances]. -/
/-
**UniformSpace.comap** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UniformSpace.comap (f : α -> β) (u : UniformSpace β) : UniformSpace α wher
e uniformity
参数：f : α -> β；u : UniformSpace β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : α → β` and a uniformity `u` on `β`, the inverse image of `u` under `f
`
  is the inverse image in the filter sense of the induced function `α × α → β × 
β`.
  See note [reducible non-instances].
-/
abbrev UniformSpace.comap (f : α → β) (u : UniformSpace β) : UniformSpace α where
  uniformity := 𝓤[u].comap fun p : α × α => (f p.1, f p.2)
  symm := by
    simp only [tendsto_comap_iff]
    exact tendsto_swap_uniformity.comp tendsto_comap
  comp := le_trans
    (by
      rw [comap_lift'_eq, comap_lift'_eq2]
      · exact lift'_mono' fun s _ ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩ => ⟨f x, h₁, h₂⟩
      · exact monotone_id.relComp monotone_id)
    (comap_mono u.comp)
  toTopologicalSpace := u.toTopologicalSpace.induced f
  nhds_eq_comap_uniformity x := by
    simp only [nhds_induced, nhds_eq_comap_uniformity, comap_comap, Function.comp_def]
/-
**uniformity_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_comap {_ : UniformSpace β} (f : α -> β) : 𝓤[UniformSpace.comap 
f ‹_›] = comap (Prod.map f f) (𝓤 β)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_comap {_ : UniformSpace β} (f : α → β) :
    𝓤[UniformSpace.comap f ‹_›] = comap (Prod.map f f) (𝓤 β) :=
  rfl
/-
**ball_preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ball_preimage {f : α -> β} {U : SetRel β β} {x : α} : UniformSpace.ball x 
(Prod.map f f ⁻¹' U) = f ⁻¹' UniformSpace.ball (f x) U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ball_preimage {f : α → β} {U : SetRel β β} {x : α} :
    UniformSpace.ball x (Prod.map f f ⁻¹' U) = f ⁻¹' UniformSpace.ball (f x) U := by
  ext : 1
  simp only [UniformSpace.ball, mem_preimage, Prod.map_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**uniformSpace_comap_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformSpace_comap_id {α : Type*} : UniformSpace.comap (id : α -> α) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_comap`：uniformity_comap {_ : UniformSpace β} (f : α -> β) : 𝓤
[UniformSpace.comap f ‹_›] = comap (Prod.map f f) (𝓤 β)
· 使用定理 `Prod.map_id`：∀ {α : Type u_1} {β : Type u_2}, Prod.map id id = id
· 使用定理 `Filter.comap_id`：comap_id : comap id f = f
-/
theorem uniformSpace_comap_id {α : Type*} : UniformSpace.comap (id : α → α) = id := by
  ext : 2
  rw [uniformity_comap, Prod.map_id, comap_id]
/-
**UniformSpace.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.comap_comap {α β γ} {uγ : UniformSpace γ} {f : α -> β} {g : β
 -> γ} : UniformSpace.comap (g ∘ f) uγ = UniformSpace.comap f (UniformSpace.coma
p g uγ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem UniformSpace.comap_comap {α β γ} {uγ : UniformSpace γ} {f : α → β} {g : β → γ} :
    UniformSpace.comap (g ∘ f) uγ = UniformSpace.comap f (UniformSpace.comap g uγ) := by
  ext1
  simp only [uniformity_comap, Filter.comap_comap, Prod.map_comp_map]
/-
**UniformSpace.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.comap_inf {α γ} {u₁ u₂ : UniformSpace γ} {f : α -> γ} : (u₁ ⊓
 u₂).comap f = u₁.comap f ⊓ u₂.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
-/
theorem UniformSpace.comap_inf {α γ} {u₁ u₂ : UniformSpace γ} {f : α → γ} :
    (u₁ ⊓ u₂).comap f = u₁.comap f ⊓ u₂.comap f :=
  UniformSpace.ext Filter.comap_inf
/-
**UniformSpace.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.comap_iInf {ι α γ} {u : ι -> UniformSpace γ} {f : α -> γ} : (
⨅ i, u i).comap f = ⨅ i, (u i).comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem UniformSpace.comap_iInf {ι α γ} {u : ι → UniformSpace γ} {f : α → γ} :
    (⨅ i, u i).comap f = ⨅ i, (u i).comap f := by
  ext : 1
  simp [uniformity_comap, iInf_uniformity]
/-
**UniformSpace.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.comap_mono {α γ} {f : α -> γ} : Monotone fun u : UniformSpace
 γ => u.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
-/
theorem UniformSpace.comap_mono {α γ} {f : α → γ} :
    Monotone fun u : UniformSpace γ => u.comap f := fun _ _ hu =>
  Filter.comap_mono hu
/-
**uniformContinuous_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_iff_le_comap {α β} {uα : UniformSpace α} {uβ : UniformSp
ace β} {f : α -> β} : UniformContinuous f ↔ uα <= uβ.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
-/
theorem uniformContinuous_iff_le_comap {α β} {uα : UniformSpace α} {uβ : UniformSpace β}
    {f : α → β} : UniformContinuous f ↔ uα ≤ uβ.comap f :=
  Filter.map_le_iff_le_comap

@[deprecated (since := "2026-05-23")]
alias uniformContinuous_iff := uniformContinuous_iff_le_comap
/-
**le_iff_uniformContinuous_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_uniformContinuous_id {u v : UniformSpace α} : u <= v ↔ @UniformCont
inuous _ _ u v id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformContinuous_iff_le_comap`：uniformContinuous_iff_le_comap {α β} {uα
 : UniformSpace α} {uβ : UniformSpace β} {f : α -> β} : UniformContinuous f ↔ uα
 <= uβ.comap f
· 使用定理 `uniformSpace_comap_id`：uniformSpace_comap_id {α : Type*} : UniformSpace.
comap (id : α -> α) = id
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_iff_uniformContinuous_id {u v : UniformSpace α} :
    u ≤ v ↔ @UniformContinuous _ _ u v id := by
  rw [uniformContinuous_iff_le_comap, uniformSpace_comap_id, id]
/-
**uniformContinuous_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_comap {f : α -> β} [u : UniformSpace β] : @UniformContin
uous α β (UniformSpace.comap f u) u f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
-/
theorem uniformContinuous_comap {f : α → β} [u : UniformSpace β] :
    @UniformContinuous α β (UniformSpace.comap f u) u f :=
  tendsto_comap
/-
**uniformContinuous_comap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_comap' {f : γ -> β} {g : α -> γ} [v : UniformSpace β] [u
 : UniformSpace α] (h : UniformContinuous (f ∘ g)) : @UniformContinuous α γ u (U
niformSpace.comap f v) g
参数：h : UniformContinuous (f ∘ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
-/
theorem uniformContinuous_comap' {f : γ → β} {g : α → γ} [v : UniformSpace β] [u : UniformSpace α]
    (h : UniformContinuous (f ∘ g)) : @UniformContinuous α γ u (UniformSpace.comap f v) g :=
  tendsto_comap_iff.2 h

namespace UniformSpace

/-
**UniformSpace.to_nhds_mono** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：to_nhds_mono {u₁ u₂ : UniformSpace α} (h : u₁ <= u₂) (a : α) : @nhds _ (@U
niformSpace.toTopologicalSpace _ u₁) a <= @nhds _ (@UniformSpace.toTopologicalSp
ace _ u₂) a
参数：h : u₁ <= u₂；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_uniformity`：nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball
 x)
· 使用定理 `Filter.lift'_mono`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : Filter α} {h
₁ h₂ : Set α → Set β},   f₁ ≤ f₂ → h₁ ≤ h₂ → f₁.lift' h₁ ≤ f₂.lift' h₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem to_nhds_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) (a : α) :
    @nhds _ (@UniformSpace.toTopologicalSpace _ u₁) a ≤
      @nhds _ (@UniformSpace.toTopologicalSpace _ u₂) a := by
  rw [@nhds_eq_uniformity α u₁ a, @nhds_eq_uniformity α u₂ a]; exact lift'_mono h le_rfl
/-
**UniformSpace.toTopologicalSpace_mono** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：toTopologicalSpace_mono {u₁ u₂ : UniformSpace α} (h : u₁ <= u₂) : @Uniform
Space.toTopologicalSpace _ u₁ <= @UniformSpace.toTopologicalSpace _ u₂
参数：h : u₁ <= u₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_nhds_le_nhds`：le_of_nhds_le_nhds (h : forall x, @nhds α t₁ x <= @n
hds α t₂ x) : t₁ <= t₂
· 使用定理 `UniformSpace.to_nhds_mono`：to_nhds_mono {u₁ u₂ : UniformSpace α} (h : u₁
 <= u₂) (a : α) : @nhds _ (@UniformSpace.toTopologicalSpace _ u₁) a <= @nhds _ (
@UniformSpace.t…
-/
theorem toTopologicalSpace_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) :
    @UniformSpace.toTopologicalSpace _ u₁ ≤ @UniformSpace.toTopologicalSpace _ u₂ :=
  le_of_nhds_le_nhds <| to_nhds_mono h
/-
**UniformSpace.toTopologicalSpace_comap** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`
。
形式化陈述：toTopologicalSpace_comap {f : α -> β} {u : UniformSpace β} : @UniformSpace
.toTopologicalSpace _ (UniformSpace.comap f u) = TopologicalSpace.induced f (@Un
iformSpace.toTopologicalSpace β u)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopologicalSpace_comap {f : α → β} {u : UniformSpace β} :
    @UniformSpace.toTopologicalSpace _ (UniformSpace.comap f u) =
      TopologicalSpace.induced f (@UniformSpace.toTopologicalSpace β u) :=
  rfl
/-
**UniformSpace.uniformSpace_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `UniformSpace`。
形式化陈述：uniformSpace_eq_bot {u : UniformSpace α} : u = ⊥ ↔ SetRel.id in 𝓤[u]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
lemma uniformSpace_eq_bot {u : UniformSpace α} : u = ⊥ ↔ SetRel.id ∈ 𝓤[u] :=
  le_bot_iff.symm.trans le_principal_iff
/-
**UniformSpace._root_.Filter.HasBasis.uniformSpace_eq_bot** 是 Mathlib 中的一个引理，位于命
名空间 `UniformSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.Filter.HasBasis.uniformSpace_eq_bot {ι p} {s : ι → SetRel α α}
    {u : UniformSpace α} (h : 𝓤[u].HasBasis p s) :
    u = ⊥ ↔ ∃ i, p i ∧ Pairwise fun x y : α ↦ (x, y) ∉ s i := by
  simp [uniformSpace_eq_bot, h.mem_iff, subset_def, Pairwise, not_imp_not]
/-
**UniformSpace.toTopologicalSpace_bot** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：toTopologicalSpace_bot : @UniformSpace.toTopologicalSpace α ⊥ = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopologicalSpace_bot : @UniformSpace.toTopologicalSpace α ⊥ = ⊥ := rfl
/-
**UniformSpace.toTopologicalSpace_top** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：toTopologicalSpace_top : @UniformSpace.toTopologicalSpace α ⊤ = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopologicalSpace_top : @UniformSpace.toTopologicalSpace α ⊤ = ⊤ := rfl
/-
**UniformSpace.toTopologicalSpace_iInf** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：toTopologicalSpace_iInf {ι : Sort*} {u : ι -> UniformSpace α} : (iInf u).t
oTopologicalSpace = ⨅ i, (u i).toTopologicalSpace
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext_nhds`：∀ {X : Type u_2} {t t' : TopologicalSpace X},
 (∀ (x : X), nhds x = nhds x) → t = t'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toTopologicalSpace_iInf {ι : Sort*} {u : ι → UniformSpace α} :
    (iInf u).toTopologicalSpace = ⨅ i, (u i).toTopologicalSpace :=
  TopologicalSpace.ext_nhds fun a ↦ by simp only [@nhds_eq_comap_uniformity _ (iInf u), nhds_iInf,
    iInf_uniformity, @nhds_eq_comap_uniformity _ (u _), Filter.comap_iInf]
/-
**UniformSpace.toTopologicalSpace_sInf** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：toTopologicalSpace_sInf {s : Set (UniformSpace α)} : (sInf s).toTopologica
lSpace = ⨅ i in s, @UniformSpace.toTopologicalSpace α i
参数：UniformSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toTopologicalSpace_sInf {s : Set (UniformSpace α)} :
    (sInf s).toTopologicalSpace = ⨅ i ∈ s, @UniformSpace.toTopologicalSpace α i := by
  rw [sInf_eq_iInf]
  simp only [← toTopologicalSpace_iInf]
/-
**UniformSpace.toTopologicalSpace_inf** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：toTopologicalSpace_inf {u v : UniformSpace α} : (u ⊓ v).toTopologicalSpace
 = u.toTopologicalSpace ⊓ v.toTopologicalSpace
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopologicalSpace_inf {u v : UniformSpace α} :
    (u ⊓ v).toTopologicalSpace = u.toTopologicalSpace ⊓ v.toTopologicalSpace :=
  rfl

end UniformSpace

section

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ] {f : α → β} {s t : Set α}

@[fun_prop]
/-
**UniformContinuous.continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.continuous (hf : UniformContinuous f) : Continuous f
参数：hf : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用定理 `UniformSpace.toTopologicalSpace_mono`：toTopologicalSpace_mono {u₁ u₂ : U
niformSpace α} (h : u₁ <= u₂) : @UniformSpace.toTopologicalSpace _ u₁ <= @Unifor
mSpace.toTopologicalSpace …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuous_iff_le_comap`：uniformContinuous_iff_le_comap {α β} {uα
 : UniformSpace α} {uβ : UniformSpace β} {f : α -> β} : UniformContinuous f ↔ uα
 <= uβ.comap f
-/
theorem UniformContinuous.continuous (hf : UniformContinuous f) : Continuous f :=
  continuous_iff_le_induced.mpr <| UniformSpace.toTopologicalSpace_mono <|
    uniformContinuous_iff_le_comap.1 hf

@[fun_prop]
/-
**UniformContinuous.uniformContinuousOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformContinuous.uniformContinuousOn (hf : UniformContinuous f) : Uniform
ContinuousOn f s
参数：hf : UniformContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_inf_left`：tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α
} {y : Filter β} (h : Tendsto f x₁ y) : Tendsto f (x₁ ⊓ x₂) y
-/
lemma UniformContinuous.uniformContinuousOn (hf : UniformContinuous f) :
    UniformContinuousOn f s :=
  tendsto_inf_left hf
/-
**UniformContinuousOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformContinuousOn.mono (hf : UniformContinuousOn f s) (ht : t subseteq s
) : UniformContinuousOn f t
参数：hf : UniformContinuousOn f s；ht : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma UniformContinuousOn.mono (hf : UniformContinuousOn f s) (ht : t ⊆ s) :
    UniformContinuousOn f t :=
  Tendsto.mono_left hf (inf_le_inf le_rfl (by simp [ht]))
/-
**UniformContinuousOn.congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformContinuousOn.congr {f g : α -> β} {s : Set α} (hf : UniformContinuo
usOn f s) (h : EqOn f g s) : UniformContinuousOn g s
参数：hf : UniformContinuousOn f s；h : EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma UniformContinuousOn.congr {f g : α → β} {s : Set α}
    (hf : UniformContinuousOn f s) (h : EqOn f g s) :
    UniformContinuousOn g s := by
  apply hf.congr'
  apply EventuallyEq.filter_mono _ inf_le_right
  filter_upwards [mem_principal_self _] with ⟨a, b⟩ ⟨ha, hb⟩ using by simp [h ha, h hb]

@[fun_prop]
/-
**UniformContinuousOn.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformContinuousOn.comp {g : β -> γ} {t : Set β} (hg : UniformContinuousO
n g t) (hf : UniformContinuousOn f s) (hst : MapsTo f s t) : UniformContinuousOn
 (g ∘ f) s
参数：hg : UniformContinuousOn g t；hf : UniformContinuousOn f s；hst : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.tendsto_inf_right`：tendsto_inf_right {f : α -> β} {x₁ x₂ : Filter
 α} {y : Filter β} (h : Tendsto f x₂ y) : Tendsto f (x₁ ⊓ x₂) y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma UniformContinuousOn.comp {g : β → γ} {t : Set β} (hg : UniformContinuousOn g t)
    (hf : UniformContinuousOn f s) (hst : MapsTo f s t) : UniformContinuousOn (g ∘ f) s := by
  change Tendsto ((fun x ↦ (g x.1, g x.2)) ∘ (fun x ↦ (f x.1, f x.2))) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 γ)
  apply Tendsto.comp hg
  refine tendsto_inf.2 ⟨hf, tendsto_inf_right ?_⟩
  simp only [tendsto_principal, mem_prod, eventually_principal, and_imp, Prod.forall]
  exact fun a b ha hb ↦ ⟨hst ha, hst hb⟩

@[fun_prop]
/-
**UniformContinuous.comp_uniformContinuousOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformContinuous.comp_uniformContinuousOn {g : β -> γ} (hg : UniformConti
nuous g) (hf : UniformContinuousOn f s) : UniformContinuousOn (g ∘ f) s
参数：hg : UniformContinuous g；hf : UniformContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformContinuousOn.comp`：UniformContinuousOn.comp {g : β -> γ} {t : Set
 β} (hg : UniformContinuousOn g t) (hf : UniformContinuousOn f s) (hst : MapsTo 
f s t) : Unifo…
· 使用引理 `UniformContinuous.uniformContinuousOn`：UniformContinuous.uniformContinuo
usOn (hf : UniformContinuous f) : UniformContinuousOn f s
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
lemma UniformContinuous.comp_uniformContinuousOn {g : β → γ}
    (hg : UniformContinuous g) (hf : UniformContinuousOn f s) : UniformContinuousOn (g ∘ f) s :=
  (hg.uniformContinuousOn (s := univ)).comp hf (mapsTo_univ _ _)

end

/-- Uniform space structure on `ULift α`. -/
/-
**ULift.uniformSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.uniformSpace [UniformSpace α] : UniformSpace (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniform space structure on `ULift α`.
-/
instance ULift.uniformSpace [UniformSpace α] : UniformSpace (ULift α) :=
  UniformSpace.comap ULift.down ‹_›

/-- Uniform space structure on `αᵒᵈ`. -/
/-
**OrderDual.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instUniformSpace [UniformSpace α] : UniformSpace (αᵒᵈ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniform space structure on `αᵒᵈ`.
-/
instance OrderDual.instUniformSpace [UniformSpace α] : UniformSpace (αᵒᵈ) :=
  ‹UniformSpace α›

section UniformContinuousInfi

-- TODO: add an `iff` lemma?
/-
**UniformContinuous.inf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.inf_rng {f : α -> β} {u₁ : UniformSpace α} {u₂ u₃ : Unif
ormSpace β} (h₁ : UniformContinuous[u₁, u₂] f) (h₂ : UniformContinuous[u₁, u₃] f
) : UniformContinuous[u₁, u₂ ⊓ u₃] f
参数：h₁ : UniformContinuous[u₁, u₂] f；h₂ : UniformContinuous[u₁, u₃] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
-/
theorem UniformContinuous.inf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ u₃ : UniformSpace β}
    (h₁ : UniformContinuous[u₁, u₂] f) (h₂ : UniformContinuous[u₁, u₃] f) :
    UniformContinuous[u₁, u₂ ⊓ u₃] f :=
  tendsto_inf.mpr ⟨h₁, h₂⟩
/-
**UniformContinuous.inf_dom_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.inf_dom_left {f : α -> β} {u₁ u₂ : UniformSpace α} {u₃ :
 UniformSpace β} (hf : UniformContinuous[u₁, u₃] f) : UniformContinuous[u₁ ⊓ u₂,
 u₃] f
参数：hf : UniformContinuous[u₁, u₃] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_inf_left`：tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α
} {y : Filter β} (h : Tendsto f x₁ y) : Tendsto f (x₁ ⊓ x₂) y
-/
theorem UniformContinuous.inf_dom_left {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : UniformContinuous[u₁, u₃] f) : UniformContinuous[u₁ ⊓ u₂, u₃] f :=
  tendsto_inf_left hf
/-
**UniformContinuous.inf_dom_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.inf_dom_right {f : α -> β} {u₁ u₂ : UniformSpace α} {u₃ 
: UniformSpace β} (hf : UniformContinuous[u₂, u₃] f) : UniformContinuous[u₁ ⊓ u₂
, u₃] f
参数：hf : UniformContinuous[u₂, u₃] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_inf_right`：tendsto_inf_right {f : α -> β} {x₁ x₂ : Filter
 α} {y : Filter β} (h : Tendsto f x₂ y) : Tendsto f (x₁ ⊓ x₂) y
-/
theorem UniformContinuous.inf_dom_right {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : UniformContinuous[u₂, u₃] f) : UniformContinuous[u₁ ⊓ u₂, u₃] f :=
  tendsto_inf_right hf
/-
**uniformContinuous_sInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_sInf_dom {f : α -> β} {u₁ : Set (UniformSpace α)} {u₂ : 
UniformSpace β} {u : UniformSpace α} (h₁ : u in u₁) (hf : UniformContinuous[u, u
₂] f) : UniformContinuous[sInf u₁, u₂] f
参数：UniformSpace α；h₁ : u in u₁；hf : UniformContinuous[u, u₂] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `Filter.tendsto_iInf'`：tendsto_iInf' {f : α -> β} {x : ι -> Filter α} {y 
: Filter β} (i : ι) (hi : Tendsto f (x i) y) : Tendsto f (⨅ i, x i) y
-/
theorem uniformContinuous_sInf_dom {f : α → β} {u₁ : Set (UniformSpace α)} {u₂ : UniformSpace β}
    {u : UniformSpace α} (h₁ : u ∈ u₁) (hf : UniformContinuous[u, u₂] f) :
    UniformContinuous[sInf u₁, u₂] f := by
  delta UniformContinuous
  rw [sInf_eq_iInf', iInf_uniformity]
  exact tendsto_iInf' ⟨u, h₁⟩ hf
/-
**uniformContinuous_sInf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_sInf_rng {f : α -> β} {u₁ : UniformSpace α} {u₂ : Set (U
niformSpace β)} : UniformContinuous[u₁, sInf u₂] f ↔ forall u in u₂, UniformCont
inuous[u₁, u] f
参数：UniformSpace β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `Filter.tendsto_iInf`：tendsto_iInf {f : α -> β} {x : Filter α} {y : ι -> 
Filter β} : Tendsto f x (⨅ i, y i) ↔ forall i, Tendsto f x (y i)
· 使用定理 `SetCoe.forall`：SetCoe.forall {s : Set α} {p : s -> Prop} : (forall x : s
, p x) ↔ forall (x) (h : x in s), p ⟨x, h⟩
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformContinuous_sInf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : Set (UniformSpace β)} :
    UniformContinuous[u₁, sInf u₂] f ↔ ∀ u ∈ u₂, UniformContinuous[u₁, u] f := by
  delta UniformContinuous
  rw [sInf_eq_iInf', iInf_uniformity, tendsto_iInf, SetCoe.forall]
/-
**uniformContinuous_iInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_iInf_dom {f : α -> β} {u₁ : ι -> UniformSpace α} {u₂ : U
niformSpace β} {i : ι} (hf : UniformContinuous[u₁ i, u₂] f) : UniformContinuous[
iInf u₁, u₂] f
参数：hf : UniformContinuous[u₁ i, u₂] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `Filter.tendsto_iInf'`：tendsto_iInf' {f : α -> β} {x : ι -> Filter α} {y 
: Filter β} (i : ι) (hi : Tendsto f (x i) y) : Tendsto f (⨅ i, x i) y
-/
theorem uniformContinuous_iInf_dom {f : α → β} {u₁ : ι → UniformSpace α} {u₂ : UniformSpace β}
    {i : ι} (hf : UniformContinuous[u₁ i, u₂] f) : UniformContinuous[iInf u₁, u₂] f := by
  delta UniformContinuous
  rw [iInf_uniformity]
  exact tendsto_iInf' i hf
/-
**uniformContinuous_iInf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_iInf_rng {f : α -> β} {u₁ : UniformSpace α} {u₂ : ι -> U
niformSpace β} : UniformContinuous[u₁, iInf u₂] f ↔ forall i, UniformContinuous[
u₁, u₂ i] f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `Filter.tendsto_iInf`：tendsto_iInf {f : α -> β} {x : Filter α} {y : ι -> 
Filter β} : Tendsto f x (⨅ i, y i) ↔ forall i, Tendsto f x (y i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformContinuous_iInf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : ι → UniformSpace β} :
    UniformContinuous[u₁, iInf u₂] f ↔ ∀ i, UniformContinuous[u₁, u₂ i] f := by
  delta UniformContinuous
  rw [iInf_uniformity, tendsto_iInf]

end UniformContinuousInfi

/-- A uniform space with the discrete uniformity has the discrete topology. -/
/-
**discreteTopology_of_discrete_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discreteTopology_of_discrete_uniformity [hα : UniformSpace α] (h : uniform
ity α = 𝓟 SetRel.id) : DiscreteTopology α
参数：h : uniformity α = 𝓟 SetRel.id。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A uniform space with the discrete uniformity has the discrete topology.
-/
theorem discreteTopology_of_discrete_uniformity [hα : UniformSpace α]
    (h : uniformity α = 𝓟 SetRel.id) : DiscreteTopology α :=
  ⟨(UniformSpace.ext h.symm : ⊥ = hα) ▸ rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformSpace Empty := ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformSpace PUnit := ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformSpace Bool := ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformSpace ℕ := ⊥
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformSpace ℤ := ⊥

section

variable [UniformSpace α]

open Additive Multiplicative

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformSpace (Additive α) := ‹UniformSpace α›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformSpace (Multiplicative α) := ‹UniformSpace α›

@[fun_prop]
/-
**uniformContinuous_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_ofMul : UniformContinuous (ofMul : α -> Additive α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_ofMul : UniformContinuous (ofMul : α → Additive α) :=
  uniformContinuous_id

@[fun_prop]
/-
**uniformContinuous_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_toMul : UniformContinuous (toMul : Additive α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_toMul : UniformContinuous (toMul : Additive α → α) :=
  uniformContinuous_id

@[fun_prop]
/-
**uniformContinuous_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_ofAdd : UniformContinuous (ofAdd : α -> Multiplicative α
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_ofAdd : UniformContinuous (ofAdd : α → Multiplicative α) :=
  uniformContinuous_id

@[fun_prop]
/-
**uniformContinuous_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_toAdd : UniformContinuous (toAdd : Multiplicative α -> α
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_toAdd : UniformContinuous (toAdd : Multiplicative α → α) :=
  uniformContinuous_id
/-
**uniformity_additive** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_additive : 𝓤 (Additive α) = (𝓤 α).map (Prod.map ofMul ofMul)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_additive : 𝓤 (Additive α) = (𝓤 α).map (Prod.map ofMul ofMul) := rfl
/-
**uniformity_multiplicative** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_multiplicative : 𝓤 (Multiplicative α) = (𝓤 α).map (Prod.map ofA
dd ofAdd)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_multiplicative : 𝓤 (Multiplicative α) = (𝓤 α).map (Prod.map ofAdd ofAdd) := rfl

end

/-
**instUniformSpaceSubtype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instUniformSpaceSubtype {p : α -> Prop} [t : UniformSpace α] : UniformSpac
e (Subtype p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniformSpaceSubtype {p : α → Prop} [t : UniformSpace α] : UniformSpace (Subtype p) :=
  UniformSpace.comap Subtype.val t
/-
**uniformity_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_subtype {p : α -> Prop} [UniformSpace α] : 𝓤 (Subtype p) = coma
p (fun q : Subtype p × Subtype p => (q.1.1, q.2.1)) (𝓤 α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_subtype {p : α → Prop} [UniformSpace α] :
    𝓤 (Subtype p) = comap (fun q : Subtype p × Subtype p => (q.1.1, q.2.1)) (𝓤 α) :=
  rfl
/-
**uniformity_setCoe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_setCoe {s : Set α} [UniformSpace α] : 𝓤 s = comap (Prod.map ((↑
) : s -> α) ((↑) : s -> α)) (𝓤 α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_setCoe {s : Set α} [UniformSpace α] :
    𝓤 s = comap (Prod.map ((↑) : s → α) ((↑) : s → α)) (𝓤 α) :=
  rfl
/-
**map_uniformity_set_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_uniformity_set_coe {s : Set α} [UniformSpace α] : map (Prod.map (↑) (↑
)) (𝓤 s) = 𝓤 α ⊓ 𝓟 (s ×ˢ s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_setCoe`：uniformity_setCoe {s : Set α} [UniformSpace α] : 𝓤 s 
= comap (Prod.map ((↑) : s -> α) ((↑) : s -> α)) (𝓤 α)
· 使用定理 `Filter.map_comap`：map_comap (f : Filter β) (m : α -> β) : (f.comap m).ma
p m = f ⊓ 𝓟 (range m)
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem map_uniformity_set_coe {s : Set α} [UniformSpace α] :
    map (Prod.map (↑) (↑)) (𝓤 s) = 𝓤 α ⊓ 𝓟 (s ×ˢ s) := by
  rw [uniformity_setCoe, map_comap, range_prodMap, Subtype.range_val]

@[fun_prop]
/-
**uniformContinuous_subtype_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_subtype_val {p : α -> Prop} [UniformSpace α] : UniformCo
ntinuous (Subtype.val : { a : α // p a } -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap`：uniformContinuous_comap {f : α -> β} [u : Unifo
rmSpace β] : @UniformContinuous α β (UniformSpace.comap f u) u f
-/
theorem uniformContinuous_subtype_val {p : α → Prop} [UniformSpace α] :
    UniformContinuous (Subtype.val : { a : α // p a } → α) :=
  uniformContinuous_comap

@[fun_prop]
/-
**UniformContinuous.subtype_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.subtype_mk {p : α -> Prop} [UniformSpace α] [UniformSpac
e β] {f : β -> α} (hf : UniformContinuous f) (h : forall x, p (f x)) : UniformCo
ntinuous (fun x => ⟨f x, h x⟩ : β -> Subtype p)
参数：hf : UniformContinuous f；h : forall x, p (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap'`：uniformContinuous_comap' {f : γ -> β} {g : α -
> γ} [v : UniformSpace β] [u : UniformSpace α] (h : UniformContinuous (f ∘ g)) :
 @UniformConti…
-/
theorem UniformContinuous.subtype_mk {p : α → Prop} [UniformSpace α] [UniformSpace β] {f : β → α}
    (hf : UniformContinuous f) (h : ∀ x, p (f x)) :
    UniformContinuous (fun x => ⟨f x, h x⟩ : β → Subtype p) :=
  uniformContinuous_comap' hf
/-
**UniformContinuous.subtype_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.subtype_map [UniformSpace α] [UniformSpace β] {p : α -> 
Prop} {q : β -> Prop} {f : α -> β} (hf : UniformContinuous f) (h : forall x, p x
 -> q (f x)) : UniformContinuous (Subtype.map f h)
参数：hf : UniformContinuous f；h : forall x, p x -> q (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.subtype_mk`：UniformContinuous.subtype_mk {p : α -> Pro
p} [UniformSpace α] [UniformSpace β] {f : β -> α} (hf : UniformContinuous f) (h 
: forall x, p (f x…
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `uniformContinuous_subtype_val`：uniformContinuous_subtype_val {p : α -> P
rop} [UniformSpace α] : UniformContinuous (Subtype.val : { a : α // p a } -> α)
-/
theorem UniformContinuous.subtype_map [UniformSpace α] [UniformSpace β] {p : α → Prop}
    {q : β → Prop} {f : α → β} (hf : UniformContinuous f) (h : ∀ x, p x → q (f x)) :
    UniformContinuous (Subtype.map f h) :=
  (hf.comp uniformContinuous_subtype_val).subtype_mk _
/-
**uniformContinuousOn_iff_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuousOn_iff_restrict [UniformSpace α] [UniformSpace β] {f : α 
-> β} {s : Set α} : UniformContinuousOn f s ↔ UniformContinuous (s.domRestrict f
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_uniformity_set_coe`：map_uniformity_set_coe {s : Set α} [UniformSpace
 α] : map (Prod.map (↑) (↑)) (𝓤 s) = 𝓤 α ⊓ 𝓟 (s ×ˢ s)
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformContinuousOn_iff_restrict [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔ UniformContinuous (s.domRestrict f) := by
  delta UniformContinuousOn UniformContinuous
  rw [← map_uniformity_set_coe, tendsto_map'_iff]; rfl

alias ⟨UniformContinuousOn.restrict, UniformContinuousOn.of_restrict⟩ :=
  uniformContinuousOn_iff_restrict
/-
**tendsto_of_uniformContinuous_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_of_uniformContinuous_subtype [UniformSpace α] [UniformSpace β] {f 
: α -> β} {s : Set α} {a : α} (hf : UniformContinuous fun x : s => f x.val) (ha 
: s in 𝓝 a) : Tendsto f (𝓝 a) (𝓝 (f a))
参数：hf : UniformContinuous fun x : s => f x.val；ha : s in 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_nhds_subtype_coe_eq_nhds`：map_nhds_subtype_coe_eq_nhds {x : X} (hx :
 p x) (h : forallᶠ x in 𝓝 x, p x) : map ((↑) : Subtype p -> X) (𝓝 ⟨x, hx⟩) = 𝓝 x
· 使用定理 `Filter.tendsto_map'`：tendsto_map'_iff {f : β -> γ} {g : α -> β} {x : Fil
ter α} {y : Filter γ} : Tendsto f (map g x) y ↔ Tendsto (f ∘ g) x y
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
-/
theorem tendsto_of_uniformContinuous_subtype [UniformSpace α] [UniformSpace β] {f : α → β}
    {s : Set α} {a : α} (hf : UniformContinuous fun x : s => f x.val) (ha : s ∈ 𝓝 a) :
    Tendsto f (𝓝 a) (𝓝 (f a)) := by
  rw [(@map_nhds_subtype_coe_eq_nhds α _ (· ∈ s) a (mem_of_mem_nhds ha) ha).symm]
  exact tendsto_map' hf.continuous.continuousAt

@[fun_prop]
/-
**UniformContinuousOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuousOn.continuousOn [UniformSpace α] [UniformSpace β] {f : α 
-> β} {s : Set α} (h : UniformContinuousOn f s) : ContinuousOn f s
参数：h : UniformContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `uniformContinuousOn_iff_restrict`：uniformContinuousOn_iff_restrict [Unif
ormSpace α] [UniformSpace β] {f : α -> β} {s : Set α} : UniformContinuousOn f s 
↔ UniformContinuous (s…
-/
theorem UniformContinuousOn.continuousOn [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α}
    (h : UniformContinuousOn f s) : ContinuousOn f s := by
  rw [uniformContinuousOn_iff_restrict] at h
  rw [continuousOn_iff_continuous_domRestrict]
  exact h.continuous
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [UniformSpace α] [(𝓤 α).IsCountablyGenerated] (s : Set α) : (𝓤 s).IsCountablyGenerated :=
  Filter.comap.isCountablyGenerated _ _

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [UniformSpace α] : UniformSpace αᵐᵒᵖ :=
  UniformSpace.comap MulOpposite.unop ‹_›

@[to_additive]
/-
**uniformity_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_mulOpposite [UniformSpace α] : 𝓤 αᵐᵒᵖ = comap (fun q : αᵐᵒᵖ × α
ᵐᵒᵖ => (q.1.unop, q.2.unop)) (𝓤 α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_mulOpposite [UniformSpace α] :
    𝓤 αᵐᵒᵖ = comap (fun q : αᵐᵒᵖ × αᵐᵒᵖ => (q.1.unop, q.2.unop)) (𝓤 α) :=
  rfl

@[to_additive (attr := simp)]
/-
**comap_uniformity_mulOpposite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_uniformity_mulOpposite [UniformSpace α] : comap (fun p : α × α => (M
ulOpposite.op p.1, MulOpposite.op p.2)) (𝓤 αᵐᵒᵖ) = 𝓤 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Filter.comap_id`：comap_id : comap id f = f
-/
theorem comap_uniformity_mulOpposite [UniformSpace α] :
    comap (fun p : α × α => (MulOpposite.op p.1, MulOpposite.op p.2)) (𝓤 αᵐᵒᵖ) = 𝓤 α := by
  simpa [uniformity_mulOpposite, comap_comap, (· ∘ ·)] using! comap_id

namespace MulOpposite

@[to_additive (attr := fun_prop)]
/-
**MulOpposite.uniformContinuous_unop** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：uniformContinuous_unop [UniformSpace α] : UniformContinuous (unop : αᵐᵒᵖ -
> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap`：uniformContinuous_comap {f : α -> β} [u : Unifo
rmSpace β] : @UniformContinuous α β (UniformSpace.comap f u) u f
-/
theorem uniformContinuous_unop [UniformSpace α] : UniformContinuous (unop : αᵐᵒᵖ → α) :=
  uniformContinuous_comap

@[to_additive (attr := fun_prop)]
/-
**MulOpposite.uniformContinuous_op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：uniformContinuous_op [UniformSpace α] : UniformContinuous (op : α -> αᵐᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap'`：uniformContinuous_comap' {f : γ -> β} {g : α -
> γ} [v : UniformSpace β] [u : UniformSpace α] (h : UniformContinuous (f ∘ g)) :
 @UniformConti…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_op [UniformSpace α] : UniformContinuous (op : α → αᵐᵒᵖ) :=
  uniformContinuous_comap' uniformContinuous_id

end MulOpposite

section Prod

open UniformSpace

/-! a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/
/-
**instUniformSpaceProd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instUniformSpaceProd [u₁ : UniformSpace α] [u₂ : UniformSpace β] : Uniform
Space (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
a similar product space is possible on the function space (uniformity of pointwi
se convergence),
  but we want to have the uniformity of uniform convergence on function spaces
-/
instance instUniformSpaceProd [u₁ : UniformSpace α] [u₂ : UniformSpace β] : UniformSpace (α × β) :=
  u₁.comap Prod.fst ⊓ u₂.comap Prod.snd

-- check the above produces no diamond for `simp` and typeclass search
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [UniformSpace α] [UniformSpace β] :
    (instTopologicalSpaceProd : TopologicalSpace (α × β)) = UniformSpace.toTopologicalSpace := by
  with_reducible_and_instances rfl
/-
**uniformity_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_prod [UniformSpace α] [UniformSpace β] : 𝓤 (α × β) = ((𝓤 α).com
ap fun p : (α × β) × α × β => (p.1.1, p.2.1)) ⊓ (𝓤 β).comap fun p : (α × β) × α 
× β => (p.1.2, p.2.2)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformity_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) =
      ((𝓤 α).comap fun p : (α × β) × α × β => (p.1.1, p.2.1)) ⊓
        (𝓤 β).comap fun p : (α × β) × α × β => (p.1.2, p.2.2) :=
  rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [UniformSpace α] [IsCountablyGenerated (𝓤 α)]
    [UniformSpace β] [IsCountablyGenerated (𝓤 β)] : IsCountablyGenerated (𝓤 (α × β)) := by
  rw [uniformity_prod]
  infer_instance
/-
**uniformity_prod_eq_comap_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_prod_eq_comap_prod [UniformSpace α] [UniformSpace β] : 𝓤 (α × β
) = comap (fun p : (α × β) × α × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 
𝓤 β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformity_prod_eq_comap_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) =
      comap (fun p : (α × β) × α × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 𝓤 β) := by
  simp_rw [uniformity_prod, prod_eq_inf, Filter.comap_inf, Filter.comap_comap, Function.comp_def]
/-
**uniformity_prod_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_prod_eq_prod [UniformSpace α] [UniformSpace β] : 𝓤 (α × β) = ma
p (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 𝓤 β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_swap4_eq_comap`：map_swap4_eq_comap {f : Filter ((α × β) × γ ×
 δ)} : map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f = com
ap (fun p : (α …
· 使用定理 `uniformity_prod_eq_comap_prod`：uniformity_prod_eq_comap_prod [UniformSpa
ce α] [UniformSpace β] : 𝓤 (α × β) = comap (fun p : (α × β) × α × β => ((p.1.1, 
p.2.1), (p.1.2, p.2…
-/
theorem uniformity_prod_eq_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 𝓤 β) := by
  rw [map_swap4_eq_comap, uniformity_prod_eq_comap_prod]
/-
**mem_uniformity_of_uniformContinuous_invariant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_uniformity_of_uniformContinuous_invariant [UniformSpace α] [UniformSpa
ce β] {s : SetRel β β} {f : α -> α -> β} (hf : UniformContinuous fun p : α × α =
> f p.1 p.2) (hs : s in 𝓤 β) : exists u in 𝓤 α, forall a b c, (a, b) in u -> (f 
a c, f b c) in s
参数：hf : UniformContinuous fun p : α × α => f p.1 p.2；hs : s in 𝓤 β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `uniformity_prod_eq_prod`：uniformity_prod_eq_prod [UniformSpace α] [Unifo
rmSpace β] : 𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2
, p.2.2))) (𝓤…
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s
-/
theorem mem_uniformity_of_uniformContinuous_invariant [UniformSpace α] [UniformSpace β]
    {s : SetRel β β} {f : α → α → β} (hf : UniformContinuous fun p : α × α => f p.1 p.2)
    (hs : s ∈ 𝓤 β) : ∃ u ∈ 𝓤 α, ∀ a b c, (a, b) ∈ u → (f a c, f b c) ∈ s := by
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff] at hf
  rcases mem_prod_iff.1 (mem_map.1 <| hf hs) with ⟨u, hu, v, hv, huvt⟩
  exact ⟨u, hu, fun a b c hab => @huvt ((_, _), (_, _)) ⟨hab, refl_mem_uniformity hv⟩⟩

/-- An entourage of the diagonal in `α` and an entourage in `β` yield an entourage in `α × β`
once we permute coordinates. -/
/-
**entourageProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：entourageProd (u : SetRel α α) (v : SetRel β β) : SetRel (α × β) (α × β)
参数：u : SetRel α α；v : SetRel β β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An entourage of the diagonal in `α` and an entourage in `β` yield an entourage i
n `α × β`
once we permute coordinates.
-/
def entourageProd (u : SetRel α α) (v : SetRel β β) : SetRel (α × β) (α × β) :=
  {((a₁, b₁), (a₂, b₂)) | (a₁, a₂) ∈ u ∧ (b₁, b₂) ∈ v}
/-
**mem_entourageProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_entourageProd {u : SetRel α α} {v : SetRel β β} {p : (α × β) × α × β} 
: p in entourageProd u v ↔ (p.1.1, p.2.1) in u ∧ (p.1.2, p.2.2) in v
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_entourageProd {u : SetRel α α} {v : SetRel β β} {p : (α × β) × α × β} :
    p ∈ entourageProd u v ↔ (p.1.1, p.2.1) ∈ u ∧ (p.1.2, p.2.2) ∈ v := Iff.rfl
/-
**entourageProd_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：entourageProd_mem_uniformity [t₁ : UniformSpace α] [t₂ : UniformSpace β] {
u : SetRel α α} {v : SetRel β β} (hu : u in 𝓤 α) (hv : v in 𝓤 β) : entourageProd
 u v in 𝓤 (α × β)
参数：hu : u in 𝓤 α；hv : v in 𝓤 β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformity_prod`：uniformity_prod [UniformSpace α] [UniformSpace β] : 𝓤 (
α × β) = ((𝓤 α).comap fun p : (α × β) × α × β => (p.1.1, p.2.1)) ⊓ (𝓤 β).comap f
un p …
· 使用定理 `Filter.inter_mem_inf`：inter_mem_inf {α : Type u} {f g : Filter α} {s t :
 Set α} (hs : s in f) (ht : t in g) : s inter t in f ⊓ g
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
-/
theorem entourageProd_mem_uniformity [t₁ : UniformSpace α] [t₂ : UniformSpace β] {u : SetRel α α}
    {v : SetRel β β} (hu : u ∈ 𝓤 α) (hv : v ∈ 𝓤 β) :
    entourageProd u v ∈ 𝓤 (α × β) := by
  rw [uniformity_prod]; exact inter_mem_inf (preimage_mem_comap hu) (preimage_mem_comap hv)
/-
**ball_entourageProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_entourageProd (u : SetRel α α) (v : SetRel β β) (x : α × β) : ball x 
(entourageProd u v) = ball x.1 u ×ˢ ball x.2 v
参数：u : SetRel α α；v : SetRel β β；x : α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ball_entourageProd (u : SetRel α α) (v : SetRel β β) (x : α × β) :
    ball x (entourageProd u v) = ball x.1 u ×ˢ ball x.2 v := by
  ext p; simp only [ball, entourageProd, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_preimage]
/-
**IsSymm_entourageProd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsSymm_entourageProd {u : SetRel α α} {v : SetRel β β} [u.IsSymm] [v.IsSym
m] : (entourageProd u v).IsSymm where symm _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
-/
instance IsSymm_entourageProd {u : SetRel α α} {v : SetRel β β} [u.IsSymm] [v.IsSymm] :
    (entourageProd u v).IsSymm where
  symm _ _ := .imp u.symm v.symm

@[simp]
/-
**inv_entourageProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_entourageProd (u : SetRel α α) (v : SetRel β β) : (entourageProd u v).
inv = entourageProd u.inv v.inv
参数：u : SetRel α α；v : SetRel β β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_entourageProd (u : SetRel α α) (v : SetRel β β) :
    (entourageProd u v).inv = entourageProd u.inv v.inv :=
  rfl

@[simp]
/-
**image_entourageProd_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_entourageProd_prod (u : SetRel α α) (v : SetRel β β) (s : Set α) (t 
: Set β) : (entourageProd u v).image (s ×ˢ t) = u.image s ×ˢ v.image t
参数：u : SetRel α α；v : SetRel β β；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem image_entourageProd_prod (u : SetRel α α) (v : SetRel β β) (s : Set α) (t : Set β) :
    (entourageProd u v).image (s ×ˢ t) = u.image s ×ˢ v.image t := by
  ext
  simp only [mem_entourageProd, SetRel.mem_image, Set.mem_prod, Prod.exists]
  grind

@[simp]
/-
**preimage_entourageProd_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_entourageProd_prod (u : SetRel α α) (v : SetRel β β) (s : Set α) 
(t : Set β) : (entourageProd u v).preimage (s ×ˢ t) = u.preimage s ×ˢ v.preimage
 t
参数：u : SetRel α α；v : SetRel β β；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_entourageProd_prod`：image_entourageProd_prod (u : SetRel α α) (v :
 SetRel β β) (s : Set α) (t : Set β) : (entourageProd u v).image (s ×ˢ t) = u.im
age s ×ˢ v.ima…
-/
theorem preimage_entourageProd_prod (u : SetRel α α) (v : SetRel β β) (s : Set α) (t : Set β) :
    (entourageProd u v).preimage (s ×ˢ t) = u.preimage s ×ˢ v.preimage t :=
  image_entourageProd_prod u.inv v.inv s t
/-
**Filter.HasBasis.uniformity_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformity_prod {ιa ιb : Type*} [UniformSpace α] [UniformS
pace β] {pa : ιa -> Prop} {pb : ιb -> Prop} {sa : ιa -> SetRel α α} {sb : ιb -> 
SetRel β β} (ha : (𝓤 α).HasBasis pa sa) (hb : (𝓤 β).HasBasis pb sb) : (𝓤 (α × β)
).HasBasis (fun i : ιa × ιb => pa i.1 ∧ pb i.2) (fun i => entourageProd (sa i.1)
 (sb i.2))
参数：ha : (𝓤 α).HasBasis pa sa；hb : (𝓤 β).HasBasis pb sb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.inf`：∀ {α : Type u_1} {l l' : Filter α} {ι : Type u_6} {
ι' : Type u_7} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set 
α},   l.H…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
-/
theorem Filter.HasBasis.uniformity_prod {ιa ιb : Type*} [UniformSpace α] [UniformSpace β]
    {pa : ιa → Prop} {pb : ιb → Prop} {sa : ιa → SetRel α α} {sb : ιb → SetRel β β}
    (ha : (𝓤 α).HasBasis pa sa) (hb : (𝓤 β).HasBasis pb sb) :
    (𝓤 (α × β)).HasBasis (fun i : ιa × ιb ↦ pa i.1 ∧ pb i.2)
    (fun i ↦ entourageProd (sa i.1) (sb i.2)) :=
  (ha.comap _).inf (hb.comap _)
/-
**entourageProd_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：entourageProd_subset [UniformSpace α] [UniformSpace β] {s : Set ((α × β) ×
 α × β)} (h : s in 𝓤 (α × β)) : exists u in 𝓤 α, exists v in 𝓤 β, entourageProd 
u v subseteq s
参数：(α × β) × α × β；h : s in 𝓤 (α × β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff'`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (t : Set α), t ∈ l ↔ ∃ i, 
p i ∧ s i ⊆ t
· 使用定理 `Filter.HasBasis.uniformity_prod`：Filter.HasBasis.uniformity_prod {ιa ιb 
: Type*} [UniformSpace α] [UniformSpace β] {pa : ιa -> Prop} {pb : ιb -> Prop} {
sa : ιa -> SetRel α α…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem entourageProd_subset [UniformSpace α] [UniformSpace β]
    {s : Set ((α × β) × α × β)} (h : s ∈ 𝓤 (α × β)) :
    ∃ u ∈ 𝓤 α, ∃ v ∈ 𝓤 β, entourageProd u v ⊆ s := by
  rcases (((𝓤 α).basis_sets.uniformity_prod (𝓤 β).basis_sets).mem_iff' s).1 h with ⟨w, hw⟩
  use w.1, hw.1.1, w.2, hw.1.2, hw.2
/-
**tendsto_prod_uniformity_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_prod_uniformity_fst [UniformSpace α] [UniformSpace β] : Tendsto (f
un p : (α × β) × α × β => (p.1.1, p.2.1)) (𝓤 (α × β)) (𝓤 α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Filter.map_comap_le`：map_comap_le : map m (comap m g) <= g
-/
theorem tendsto_prod_uniformity_fst [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.1, p.2.1)) (𝓤 (α × β)) (𝓤 α) :=
  le_trans (map_mono inf_le_left) map_comap_le
/-
**tendsto_prod_uniformity_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_prod_uniformity_snd [UniformSpace α] [UniformSpace β] : Tendsto (f
un p : (α × β) × α × β => (p.1.2, p.2.2)) (𝓤 (α × β)) (𝓤 β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Filter.map_comap_le`：map_comap_le : map m (comap m g) <= g
-/
theorem tendsto_prod_uniformity_snd [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.2, p.2.2)) (𝓤 (α × β)) (𝓤 β) :=
  le_trans (map_mono inf_le_right) map_comap_le

@[fun_prop]
/-
**uniformContinuous_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_fst [UniformSpace α] [UniformSpace β] : UniformContinuou
s fun p : α × β => p.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_prod_uniformity_fst`：tendsto_prod_uniformity_fst [UniformSpace α
] [UniformSpace β] : Tendsto (fun p : (α × β) × α × β => (p.1.1, p.2.1)) (𝓤 (α ×
 β)) (𝓤 α)
-/
theorem uniformContinuous_fst [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.1 :=
  tendsto_prod_uniformity_fst

@[fun_prop]
/-
**uniformContinuous_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_snd [UniformSpace α] [UniformSpace β] : UniformContinuou
s fun p : α × β => p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_prod_uniformity_snd`：tendsto_prod_uniformity_snd [UniformSpace α
] [UniformSpace β] : Tendsto (fun p : (α × β) × α × β => (p.1.2, p.2.2)) (𝓤 (α ×
 β)) (𝓤 β)
-/
theorem uniformContinuous_snd [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.2 :=
  tendsto_prod_uniformity_snd

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

@[fun_prop]
/-
**UniformContinuous.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α -> γ} (h₁ : UniformContinuo
us f₁) (h₂ : UniformContinuous f₂) : UniformContinuous fun a => (f₁ a, f₂ a)
参数：h₁ : UniformContinuous f₁；h₂ : UniformContinuous f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用定理 `uniformity_prod`：uniformity_prod [UniformSpace α] [UniformSpace β] : 𝓤 (
α × β) = ((𝓤 α).comap fun p : (α × β) × α × β => (p.1.1, p.2.1)) ⊓ (𝓤 β).comap f
un p …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
-/
theorem UniformContinuous.prodMk {f₁ : α → β} {f₂ : α → γ} (h₁ : UniformContinuous f₁)
    (h₂ : UniformContinuous f₂) : UniformContinuous fun a => (f₁ a, f₂ a) := by
  rw [UniformContinuous, uniformity_prod]
  exact tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩
/-
**UniformContinuous.prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.prodMk_left {f : α × β -> γ} (h : UniformContinuous f) (
b) : UniformContinuous fun a => f (a, b)
参数：h : UniformContinuous f；b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `UniformContinuous.prodMk`：UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α
 -> γ} (h₁ : UniformContinuous f₁) (h₂ : UniformContinuous f₂) : UniformContinuo
us fun a => (f…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
-/
theorem UniformContinuous.prodMk_left {f : α × β → γ} (h : UniformContinuous f) (b) :
    UniformContinuous fun a => f (a, b) :=
  h.comp (uniformContinuous_id.prodMk uniformContinuous_const)
/-
**UniformContinuous.prodMk_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.prodMk_right {f : α × β -> γ} (h : UniformContinuous f) 
(a) : UniformContinuous fun b => f (a, b)
参数：h : UniformContinuous f；a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `UniformContinuous.prodMk`：UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α
 -> γ} (h₁ : UniformContinuous f₁) (h₂ : UniformContinuous f₂) : UniformContinuo
us fun a => (f…
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem UniformContinuous.prodMk_right {f : α × β → γ} (h : UniformContinuous f) (a) :
    UniformContinuous fun b => f (a, b) :=
  h.comp (uniformContinuous_const.prodMk uniformContinuous_id)

@[fun_prop]
/-
**UniformContinuous.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.prodMap [UniformSpace δ] {f : α -> γ} {g : β -> δ} (hf :
 UniformContinuous f) (hg : UniformContinuous g) : UniformContinuous (Prod.map f
 g)
参数：hf : UniformContinuous f；hg : UniformContinuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.prodMk`：UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α
 -> γ} (h₁ : UniformContinuous f₁) (h₂ : UniformContinuous f₂) : UniformContinuo
us fun a => (f…
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `uniformContinuous_fst`：uniformContinuous_fst [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.1
· 使用定理 `uniformContinuous_snd`：uniformContinuous_snd [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.2
-/
theorem UniformContinuous.prodMap [UniformSpace δ] {f : α → γ} {g : β → δ}
    (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformContinuous (Prod.map f g) :=
  (hf.comp uniformContinuous_fst).prodMk (hg.comp uniformContinuous_snd)

@[fun_prop]
/-
**uniformContinuous_swap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniformContinuous_swap : UniformContinuous (Prod.swap : α × β -> β × α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.prodMk`：UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α
 -> γ} (h₁ : UniformContinuous f₁) (h₂ : UniformContinuous f₂) : UniformContinuo
us fun a => (f…
· 使用定理 `uniformContinuous_snd`：uniformContinuous_snd [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.2
· 使用定理 `uniformContinuous_fst`：uniformContinuous_fst [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.1
-/
lemma uniformContinuous_swap :
    UniformContinuous (Prod.swap : α × β → β × α) :=
  uniformContinuous_snd.prodMk uniformContinuous_fst
/-
**toTopologicalSpace_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toTopologicalSpace_prod {α} {β} [u : UniformSpace α] [v : UniformSpace β] 
: @UniformSpace.toTopologicalSpace (α × β) instUniformSpaceProd = @instTopologic
alSpaceProd α β u.toTopologicalSpace v.toTopologicalSpace
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopologicalSpace_prod {α} {β} [u : UniformSpace α] [v : UniformSpace β] :
    @UniformSpace.toTopologicalSpace (α × β) instUniformSpaceProd =
      @instTopologicalSpaceProd α β u.toTopologicalSpace v.toTopologicalSpace :=
  rfl

/-- A version of `UniformContinuous.inf_dom_left` for binary functions -/
/-
**uniformContinuous_inf_dom_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `UniformContinuous.inf_dom_left` for binary functions
-/
theorem uniformContinuous_inf_dom_left₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua1; haveI := ub1; exact UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_left₂`
  have ha := @UniformContinuous.inf_dom_left _ _ id ua1 ua2 ua1 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_left _ _ id ub1 ub2 ub1 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prodMap _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua1 ub1 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id

/-- A version of `UniformContinuous.inf_dom_right` for binary functions -/
/-
**uniformContinuous_inf_dom_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `UniformContinuous.inf_dom_right` for binary functions
-/
theorem uniformContinuous_inf_dom_right₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua2; haveI := ub2; exact UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_right₂`
  have ha := @UniformContinuous.inf_dom_right _ _ id ua1 ua2 ua2 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_right _ _ id ub1 ub2 ub2 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prodMap _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua2 ub2 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id

/-- A version of `uniformContinuous_sInf_dom` for binary functions -/
/-
**uniformContinuous_sInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_sInf_dom {f : α -> β} {u₁ : Set (UniformSpace α)} {u₂ : 
UniformSpace β} {u : UniformSpace α} (h₁ : u in u₁) (hf : UniformContinuous[u, u
₂] f) : UniformContinuous[sInf u₁, u₂] f
参数：UniformSpace α；h₁ : u in u₁；hf : UniformContinuous[u, u₂] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `Filter.tendsto_iInf'`：tendsto_iInf' {f : α -> β} {x : ι -> Filter α} {y 
: Filter β} (i : ι) (hi : Tendsto f (x i) y) : Tendsto f (⨅ i, x i) y

--- 原说明 ---
A version of `uniformContinuous_sInf_dom` for binary functions
-/
theorem uniformContinuous_sInf_dom₂ {α β γ} {f : α → β → γ} {uas : Set (UniformSpace α)}
    {ubs : Set (UniformSpace β)} {ua : UniformSpace α} {ub : UniformSpace β} {uc : UniformSpace γ}
    (ha : ua ∈ uas) (hb : ub ∈ ubs) (hf : UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := sInf uas; haveI := sInf ubs
      exact @UniformContinuous _ _ _ uc fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_sInf_dom`
  have ha := uniformContinuous_sInf_dom ha uniformContinuous_id
  have hb := uniformContinuous_sInf_dom hb uniformContinuous_id
  have h_unif_cont_id := @UniformContinuous.prodMap _ _ _ _ (sInf uas) (sInf ubs) ua ub _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ hf h_unif_cont_id

end Prod

section

open UniformSpace Function

variable {δ' : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]
  [UniformSpace δ']
local notation f " ∘₂ " g => Function.bicompr f g

/-- Uniform continuity for functions of two variables. -/
@[fun_prop]
/-
**UniformContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformContinuous (f : α -> β)
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniform continuity for functions of two variables.
-/
def UniformContinuous₂ (f : α → β → γ) :=
  UniformContinuous (uncurry f)
/-
**uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformContinuous₂_def (f : α → β → γ) :
    UniformContinuous₂ f ↔ UniformContinuous (uncurry f) :=
  Iff.rfl
/-
**UniformContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformContinuous (f : α -> β)
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UniformContinuous₂.uniformContinuous {f : α → β → γ} (h : UniformContinuous₂ f) :
    UniformContinuous (uncurry f) :=
  h
/-
**uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformContinuous₂_curry (f : α × β → γ) :
    UniformContinuous₂ (Function.curry f) ↔ UniformContinuous f := by
  rw [UniformContinuous₂, uncurry_curry]

@[fun_prop]
/-
**UniformContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformContinuous (f : α -> β)
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UniformContinuous₂.comp {f : α → β → γ} {g : γ → δ} (hg : UniformContinuous g)
    (hf : UniformContinuous₂ f) : UniformContinuous₂ (g ∘₂ f) :=
  hg.comp hf

@[fun_prop]
/-
**UniformContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformContinuous (f : α -> β)
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UniformContinuous₂.bicompl {f : α → β → γ} {ga : δ → α} {gb : δ' → β}
    (hf : UniformContinuous₂ f) (hga : UniformContinuous ga) (hgb : UniformContinuous gb) :
    UniformContinuous₂ (bicompl f ga gb) :=
  hf.uniformContinuous.comp (hga.prodMap hgb)

end

/-
**toTopologicalSpace_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toTopologicalSpace_subtype [u : UniformSpace α] {p : α -> Prop} : @Uniform
Space.toTopologicalSpace (Subtype p) instUniformSpaceSubtype = @instTopologicalS
paceSubtype α p u.toTopologicalSpace
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopologicalSpace_subtype [u : UniformSpace α] {p : α → Prop} :
    @UniformSpace.toTopologicalSpace (Subtype p) instUniformSpaceSubtype =
      @instTopologicalSpaceSubtype α p u.toTopologicalSpace :=
  rfl

section Sum

variable [UniformSpace α] [UniformSpace β]

open Sum

-- Obsolete auxiliary definitions and lemmas

/-- Uniformity on a disjoint union. Entourages of the diagonal in the union are obtained
by taking independently an entourage of the diagonal in the first part, and an entourage of
the diagonal in the second part. -/
/-
**Sum.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sum.instUniformSpace : UniformSpace (α oplus β) where uniformity
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniformity on a disjoint union. Entourages of the diagonal in the union are obta
ined
by taking independently an entourage of the diagonal in the first part, and an e
ntourage of
the diagonal in the second part.
-/
instance Sum.instUniformSpace : UniformSpace (α ⊕ β) where
  uniformity := map (fun p : α × α => (inl p.1, inl p.2)) (𝓤 α) ⊔
    map (fun p : β × β => (inr p.1, inr p.2)) (𝓤 β)
  symm := fun _ hs ↦ ⟨symm_le_uniformity hs.1, symm_le_uniformity hs.2⟩
  comp := fun s hs ↦ by
    rcases comp_mem_uniformity_sets hs.1 with ⟨tα, htα, Htα⟩
    rcases comp_mem_uniformity_sets hs.2 with ⟨tβ, htβ, Htβ⟩
    filter_upwards [mem_lift' (union_mem_sup (image_mem_map htα) (image_mem_map htβ))]
    rintro ⟨_, _⟩ ⟨z, ⟨⟨a, b⟩, hab, ⟨⟩⟩ | ⟨⟨a, b⟩, hab, ⟨⟩⟩, ⟨⟨_, c⟩, hbc, ⟨⟩⟩ | ⟨⟨_, c⟩, hbc, ⟨⟩⟩⟩
    exacts [@Htα (_, _) ⟨b, hab, hbc⟩, @Htβ (_, _) ⟨b, hab, hbc⟩]
  nhds_eq_comap_uniformity x := by
    ext
    cases x <;> simp [mem_comap', -mem_comap, nhds_inl, nhds_inr, nhds_eq_comap_uniformity,
      Prod.ext_iff]

/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage
of the diagonal. -/
/-
**union_mem_uniformity_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：union_mem_uniformity_sum {a : SetRel α α} (ha : a in 𝓤 α) {b : SetRel β β}
 (hb : b in 𝓤 β) : Prod.map inl inl '' a union Prod.map inr inr '' b in 𝓤 (α opl
us β)
参数：ha : a in 𝓤 α；hb : b in 𝓤 β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.union_mem_sup`：union_mem_sup {f g : Filter α} {s t : Set α} (hs :
 s in f) (ht : t in g) : s union t in f ⊔ g
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f

--- 原说明 ---
The union of an entourage of the diagonal in each set of a disjoint union is aga
in an entourage
of the diagonal.
-/
theorem union_mem_uniformity_sum {a : SetRel α α} (ha : a ∈ 𝓤 α) {b : SetRel β β} (hb : b ∈ 𝓤 β) :
    Prod.map inl inl '' a ∪ Prod.map inr inr '' b ∈ 𝓤 (α ⊕ β) :=
  union_mem_sup (image_mem_map ha) (image_mem_map hb)
/-
**Sum.uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sum.uniformity : 𝓤 (α oplus β) = map (Prod.map inl inl) (𝓤 α) ⊔ map (Prod.
map inr inr) (𝓤 β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sum.uniformity : 𝓤 (α ⊕ β) = map (Prod.map inl inl) (𝓤 α) ⊔ map (Prod.map inr inr) (𝓤 β) :=
  rfl
/-
**uniformContinuous_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type ua} {β : Type ub} [inst : UniformSpace α] [inst_1 : UniformSpa
ce β], UniformContinuous Sum.inl
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
@[fun_prop] lemma uniformContinuous_inl : UniformContinuous (Sum.inl : α → α ⊕ β) := le_sup_left
/-
**uniformContinuous_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type ua} {β : Type ub} [inst : UniformSpace α] [inst_1 : UniformSpa
ce β], UniformContinuous Sum.inr
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
@[fun_prop] lemma uniformContinuous_inr : UniformContinuous (Sum.inr : β → α ⊕ β) := le_sup_right
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCountablyGenerated (𝓤 α)] [IsCountablyGenerated (𝓤 β)] :
    IsCountablyGenerated (𝓤 (α ⊕ β)) := by
  rw [Sum.uniformity]
  infer_instance

end Sum

end Constructions

/-!
### Expressing continuity properties in uniform spaces

We reformulate the various continuity properties of functions taking values in a uniform space
in terms of the uniformity in the target. Since the same lemmas (essentially with the same names)
also exist for metric spaces and emetric spaces (reformulating things in terms of the distance or
the edistance in the target), we put them in a namespace `Uniform` here.

In the metric and emetric space setting, there are also similar lemmas where one assumes that
both the source and the target are metric spaces, reformulating things in terms of the distance
on both sides. These lemmas are generally written without primes, and the versions where only
the target is a metric space is primed. We follow the same convention here, thus giving lemmas
with primes.
-/


namespace Uniform

variable [UniformSpace α]

/-
**Uniform.tendsto_nhds_right** 是 Mathlib 中的一个定理，位于命名空间 `Uniform`。
形式化陈述：tendsto_nhds_right {f : Filter β} {u : β -> α} {a : α} : Tendsto u f (𝓝 a)
 ↔ Tendsto (fun x => (a, u x)) f (𝓤 α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_nhds_right {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α) := by
  rw [nhds_eq_comap_uniformity, tendsto_comap_iff]; rfl
/-
**Uniform.tendsto_nhds_left** 是 Mathlib 中的一个定理，位于命名空间 `Uniform`。
形式化陈述：tendsto_nhds_left {f : Filter β} {u : β -> α} {a : α} : Tendsto u f (𝓝 a) 
↔ Tendsto (fun x => (u x, a)) f (𝓤 α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity'`：nhds_eq_comap_uniformity' {x : α} : 𝓝 x = (𝓤 
α).comap fun y => (y, x)
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_nhds_left {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (u x, a)) f (𝓤 α) := by
  rw [nhds_eq_comap_uniformity', tendsto_comap_iff]; rfl
/-
**Uniform.continuousAt_iff'_right** 是 Mathlib 中的一个定理，位于命名空间 `Uniform`。
形式化陈述：∀ {α : Type ua} {β : Type ub} [inst : UniformSpace α] [inst_1 : Topologica
lSpace β] {f : β → α} {b : β},   ContinuousAt f b ↔ Filter.Tendsto (fun x => (f 
b, f x)) (nhds b) (uniformity α)
参数：fun x => (f b, f x)；nhds b；uniformity α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Uniform.tendsto_nhds_right`：tendsto_nhds_right {f : Filter β} {u : β -> 
α} {a : α} : Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousAt_iff'_right [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt, tendsto_nhds_right]
/-
**Uniform.continuousAt_iff'_left** 是 Mathlib 中的一个定理，位于命名空间 `Uniform`。
形式化陈述：∀ {α : Type ua} {β : Type ub} [inst : UniformSpace α] [inst_1 : Topologica
lSpace β] {f : β → α} {b : β},   ContinuousAt f b ↔ Filter.Tendsto (fun x => (f 
x, f b)) (nhds b) (uniformity α)
参数：fun x => (f x, f b)；nhds b；uniformity α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Uniform.tendsto_nhds_left`：tendsto_nhds_left {f : Filter β} {u : β -> α}
 {a : α} : Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (u x, a)) f (𝓤 α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousAt_iff'_left [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt, tendsto_nhds_left]
/-
**Uniform.continuousAt_iff_prod** 是 Mathlib 中的一个定理，位于命名空间 `Uniform`。
形式化陈述：continuousAt_iff_prod [TopologicalSpace β] {f : β -> α} {b : β} : Continuo
usAt f b ↔ Tendsto (fun x : β × β => (f x.1, f x.2)) (𝓝 (b, b)) (𝓤 α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ContinuousAt.prodMap'`：ContinuousAt.prodMap' {f : X -> Z} {g : Y -> W} {
x : X} {y : Y} (hf : ContinuousAt f x) (hg : ContinuousAt g y) : ContinuousAt (P
rod.map f g…
· 使用定理 `nhds_le_uniformity`：nhds_le_uniformity (x : α) : 𝓝 (x, x) <= 𝓤 α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Uniform.continuousAt_iff'_left`：∀ {α : Type ua} {β : Type ub} [inst : Un
iformSpace α] [inst_1 : TopologicalSpace β] {f : β → α} {b : β},   ContinuousAt 
f b ↔ Filter.Tendsto…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem continuousAt_iff_prod [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x : β × β => (f x.1, f x.2)) (𝓝 (b, b)) (𝓤 α) :=
  ⟨fun H => le_trans (H.prodMap' H) (nhds_le_uniformity _), fun H =>
    continuousAt_iff'_left.2 <| H.comp <| tendsto_id.prodMk_nhds tendsto_const_nhds⟩
/-
**Uniform.continuousWithinAt_iff'_right** 是 Mathlib 中的一个定理，位于命名空间 `Uniform`。
形式化陈述：∀ {α : Type ua} {β : Type ub} [inst : UniformSpace α] [inst_1 : Topologica
lSpace β] {f : β → α} {b : β} {s : Set β},   ContinuousWithinAt f s b ↔ Filter.T
endsto (fun x => (f b, f x)) (nhdsWithin b s) (uniformity α)
参数：fun x => (f b, f x)；nhdsWithin b s；uniformity α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Uniform.tendsto_nhds_right`：tendsto_nhds_right {f : Filter β} {u : β -> 
α} {a : α} : Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_iff'_right [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_right]
/-
**Uniform.continuousWithinAt_iff'_left** 是 Mathlib 中的一个定理，位于命名空间 `Uniform`。
形式化陈述：∀ {α : Type ua} {β : Type ub} [inst : UniformSpace α] [inst_1 : Topologica
lSpace β] {f : β → α} {b : β} {s : Set β},   ContinuousWithinAt f s b ↔ Filter.T
endsto (fun x => (f x, f b)) (nhdsWithin b s) (uniformity α)
参数：fun x => (f x, f b)；nhdsWithin b s；uniformity α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Uniform.tendsto_nhds_left`：tendsto_nhds_left {f : Filter β} {u : β -> α}
 {a : α} : Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (u x, a)) f (𝓤 α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_iff'_left [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_left]
/-
**Uniform.continuousOn_iff'_right** 是 Mathlib 中的一个定理，位于命名空间 `Uniform`。
形式化陈述：∀ {α : Type ua} {β : Type ub} [inst : UniformSpace α] [inst_1 : Topologica
lSpace β] {f : β → α} {s : Set β},   ContinuousOn f s ↔ ∀ b ∈ s, Filter.Tendsto 
(fun x => (f b, f x)) (nhdsWithin b s) (uniformity α)
参数：fun x => (f b, f x)；nhdsWithin b s；uniformity α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousOn_iff'_right [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuousWithinAt_iff'_right]
/-
**Uniform.continuousOn_iff'_left** 是 Mathlib 中的一个定理，位于命名空间 `Uniform`。
形式化陈述：∀ {α : Type ua} {β : Type ub} [inst : UniformSpace α] [inst_1 : Topologica
lSpace β] {f : β → α} {s : Set β},   ContinuousOn f s ↔ ∀ b ∈ s, Filter.Tendsto 
(fun x => (f x, f b)) (nhdsWithin b s) (uniformity α)
参数：fun x => (f x, f b)；nhdsWithin b s；uniformity α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousOn_iff'_left [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuousWithinAt_iff'_left]
/-
**Uniform.continuous_iff'_right** 是 Mathlib 中的一个定理，位于命名空间 `Uniform`。
形式化陈述：∀ {α : Type ua} {β : Type ub} [inst : UniformSpace α] [inst_1 : Topologica
lSpace β] {f : β → α},   Continuous f ↔ ∀ (b : β), Filter.Tendsto (fun x => (f b
, f x)) (nhds b) (uniformity α)
参数：b : β；fun x => (f b, f x)；nhds b；uniformity α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Uniform.tendsto_nhds_right`：tendsto_nhds_right {f : Filter β} {u : β -> 
α} {a : α} : Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α)
-/
theorem continuous_iff'_right [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds_right
/-
**Uniform.continuous_iff'_left** 是 Mathlib 中的一个定理，位于命名空间 `Uniform`。
形式化陈述：∀ {α : Type ua} {β : Type ub} [inst : UniformSpace α] [inst_1 : Topologica
lSpace β] {f : β → α},   Continuous f ↔ ∀ (b : β), Filter.Tendsto (fun x => (f x
, f b)) (nhds b) (uniformity α)
参数：b : β；fun x => (f x, f b)；nhds b；uniformity α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Uniform.tendsto_nhds_left`：tendsto_nhds_left {f : Filter β} {u : β -> α}
 {a : α} : Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (u x, a)) f (𝓤 α)
-/
theorem continuous_iff'_left [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds_left

/-- Consider two functions `f` and `g` which coincide on a set `s` and are continuous there.
Then there is an open neighborhood of `s` on which `f` and `g` are uniformly close. -/
/-
**Uniform.exists_is_open_mem_uniformity_of_forall_mem_eq** 是 Mathlib 中的一个引理，位于命名
空间 `Uniform`。
形式化陈述：exists_is_open_mem_uniformity_of_forall_mem_eq [TopologicalSpace β] {r : S
etRel α α} {s : Set β} {f g : β -> α} (hf : forall x in s, ContinuousAt f x) (hg
 : forall x in s, ContinuousAt g x) (hfg : s.EqOn f g) (hr : r in 𝓤 α) : exists 
t, IsOpen t ∧ s subseteq t ∧ forall x in t, (f x, g x) in r
参数：hf : forall x in s, ContinuousAt f x；hg : forall x in s, ContinuousAt g x；hfg
 : s.EqOn f g；hr : r in 𝓤 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `mem_nhds_left`：mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : {
 y : α | (x, y) in s } in 𝓝 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `SetRel.prodMk_mem_comp`：prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c
) : a ~[R ○ S] c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Consider two functions `f` and `g` which coincide on a set `s` and are continuou
s there.
Then there is an open neighborhood of `s` on which `f` and `g` are uniformly clo
se.
-/
lemma exists_is_open_mem_uniformity_of_forall_mem_eq
    [TopologicalSpace β] {r : SetRel α α} {s : Set β}
    {f g : β → α} (hf : ∀ x ∈ s, ContinuousAt f x) (hg : ∀ x ∈ s, ContinuousAt g x)
    (hfg : s.EqOn f g) (hr : r ∈ 𝓤 α) :
    ∃ t, IsOpen t ∧ s ⊆ t ∧ ∀ x ∈ t, (f x, g x) ∈ r := by
  have A : ∀ x ∈ s, ∃ t, IsOpen t ∧ x ∈ t ∧ ∀ z ∈ t, (f z, g z) ∈ r := by
    intro x hx
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    have A : {z | (f x, f z) ∈ t} ∈ 𝓝 x := (hf x hx).preimage_mem_nhds (mem_nhds_left (f x) ht)
    have B : {z | (g x, g z) ∈ t} ∈ 𝓝 x := (hg x hx).preimage_mem_nhds (mem_nhds_left (g x) ht)
    rcases _root_.mem_nhds_iff.1 (inter_mem A B) with ⟨u, hu, u_open, xu⟩
    refine ⟨u, u_open, xu, fun y hy ↦ ?_⟩
    have I1 : (f y, f x) ∈ t := SetRel.symm t (hu hy).1
    have I2 : (g x, g y) ∈ t := (hu hy).2
    rw [hfg hx] at I1
    exact htr (SetRel.prodMk_mem_comp I1 I2)
  choose! t t_open xt ht using A
  refine ⟨⋃ x ∈ s, t x, isOpen_biUnion t_open, fun x hx ↦ mem_biUnion hx (xt x hx), ?_⟩
  rintro x hx
  simp only [mem_iUnion, exists_prop] at hx
  rcases hx with ⟨y, ys, hy⟩
  exact ht y ys x hy

end Uniform

/-
**Filter.Tendsto.congr_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.congr_uniformity {α β} [UniformSpace β] {f g : α -> β} {l :
 Filter α} {b : β} (hf : Tendsto f l (𝓝 b)) (hg : Tendsto (fun x => (f x, g x)) 
l (𝓤 β)) : Tendsto g l (𝓝 b)
参数：hf : Tendsto f l (𝓝 b)；hg : Tendsto (fun x => (f x, g x)) l (𝓤 β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Uniform.tendsto_nhds_right`：tendsto_nhds_right {f : Filter β} {u : β -> 
α} {a : α} : Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α)
· 使用定理 `Filter.Tendsto.uniformity_trans`：Filter.Tendsto.uniformity_trans {l : Fi
lter β} {f₁ f₂ f₃ : β -> α} (h₁₂ : Tendsto (fun x => (f₁ x, f₂ x)) l (𝓤 α)) (h₂₃
 : Tendsto (fun x => …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Filter.Tendsto.congr_uniformity {α β} [UniformSpace β] {f g : α → β} {l : Filter α} {b : β}
    (hf : Tendsto f l (𝓝 b)) (hg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto g l (𝓝 b) :=
  Uniform.tendsto_nhds_right.2 <| (Uniform.tendsto_nhds_right.1 hf).uniformity_trans hg
/-
**Uniform.tendsto_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Uniform.tendsto_congr {α β} [UniformSpace β] {f g : α -> β} {l : Filter α}
 {b : β} (hfg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto f l (𝓝 b) ↔ Ten
dsto g l (𝓝 b)
参数：hfg : Tendsto (fun x => (f x, g x)) l (𝓤 β)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr_uniformity`：Filter.Tendsto.congr_uniformity {α β} [
UniformSpace β] {f g : α -> β} {l : Filter α} {b : β} (hf : Tendsto f l (𝓝 b)) (
hg : Tendsto (fun x =…
· 使用定理 `Filter.Tendsto.uniformity_symm`：Filter.Tendsto.uniformity_symm {l : Filt
er β} {f : β -> α × α} (h : Tendsto f l (𝓤 α)) : Tendsto (fun x => ((f x).2, (f 
x).1)) l (𝓤 α)
-/
theorem Uniform.tendsto_congr {α β} [UniformSpace β] {f g : α → β} {l : Filter α} {b : β}
    (hfg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto f l (𝓝 b) ↔ Tendsto g l (𝓝 b) :=
  ⟨fun h => h.congr_uniformity hfg, fun h => h.congr_uniformity hfg.uniformity_symm⟩
