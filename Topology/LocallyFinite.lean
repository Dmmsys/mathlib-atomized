/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Topology.ContinuousOn

/-!
### Locally finite families of sets

We say that a family of sets in a topological space is *locally finite* if at every point `x : X`,
there is a neighborhood of `x` which meets only finitely many sets in the family.

In this file we give the definition and prove basic properties of locally finite families of sets.
-/

@[expose] public section

-- locally finite family [General Topology (Bourbaki, 1995)]
open Set Function Filter Topology

variable {ι ι' α X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : ι → Set X}

/-- A family of sets in `Set X` is locally finite if at every point `x : X`,
there is a neighborhood of `x` which meets only finitely many sets in the family. -/
/-
**LocallyFinite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyFinite (f : ι -> Set X)
参数：f : ι -> Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of sets in `Set X` is locally finite if at every point `x : X`,
there is a neighborhood of `x` which meets only finitely many sets in the family
.
-/
def LocallyFinite (f : ι → Set X) :=
  ∀ x : X, ∃ t ∈ 𝓝 x, { i | (f i ∩ t).Nonempty }.Finite
/-
**locallyFinite_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyFinite_of_finite [Finite ι] (f : ι -> Set X) : LocallyFinite f
参数：f : ι -> Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem locallyFinite_of_finite [Finite ι] (f : ι → Set X) : LocallyFinite f := fun _ =>
  ⟨univ, univ_mem, toFinite _⟩

namespace LocallyFinite

/-
**LocallyFinite.point_finite** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：point_finite (hf : LocallyFinite f) (x : X) : { b | x in f b }.Finite
参数：hf : LocallyFinite f；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem point_finite (hf : LocallyFinite f) (x : X) : { b | x ∈ f b }.Finite :=
  let ⟨_t, hxt, ht⟩ := hf x
  ht.subset fun _b hb => ⟨x, hb, mem_of_mem_nhds hxt⟩
/-
**LocallyFinite.subset** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_4} [inst : TopologicalSpace X] {f g : ι → Set
 X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → LocallyFinite g
参数：∀ (i : ι), g i ⊆ f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
protected theorem subset (hf : LocallyFinite f) (hg : ∀ i, g i ⊆ f i) : LocallyFinite g := fun a =>
  let ⟨t, ht₁, ht₂⟩ := hf a
  ⟨t, ht₁, ht₂.subset fun i hi => hi.mono <| inter_subset_inter (hg i) Subset.rfl⟩
/-
**LocallyFinite.comp_injOn** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：comp_injOn {g : ι' -> ι} (hf : LocallyFinite f) (hg : InjOn g { i | (f (g 
i)).Nonempty }) : LocallyFinite (f ∘ g)
参数：hf : LocallyFinite f；hg : InjOn g { i | (f (g i)).Nonempty }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.Nonempty.left`：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempty → s.No
nempty
-/
theorem comp_injOn {g : ι' → ι} (hf : LocallyFinite f) (hg : InjOn g { i | (f (g i)).Nonempty }) :
    LocallyFinite (f ∘ g) := fun x => by
  let ⟨t, htx, htf⟩ := hf x
  refine ⟨t, htx, htf.preimage <| ?_⟩
  exact hg.mono fun i (hi : Set.Nonempty _) => hi.left
/-
**LocallyFinite.comp_injective** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：comp_injective {g : ι' -> ι} (hf : LocallyFinite f) (hg : Injective g) : L
ocallyFinite (f ∘ g)
参数：hf : LocallyFinite f；hg : Injective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.comp_injOn`：comp_injOn {g : ι' -> ι} (hf : LocallyFinite f
) (hg : InjOn g { i | (f (g i)).Nonempty }) : LocallyFinite (f ∘ g)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem comp_injective {g : ι' → ι} (hf : LocallyFinite f) (hg : Injective g) :
    LocallyFinite (f ∘ g) :=
  hf.comp_injOn hg.injOn
/-
**LocallyFinite.of_comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：of_comp_surjective {g : ι' -> ι} (hg : Surjective g) (hfg : LocallyFinite 
(f ∘ g)) : LocallyFinite f
参数：hg : Surjective g；hfg : LocallyFinite (f ∘ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `LocallyFinite.comp_injective`：comp_injective {g : ι' -> ι} (hf : Locally
Finite f) (hg : Injective g) : LocallyFinite (f ∘ g)
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
-/
theorem of_comp_surjective {g : ι' → ι} (hg : Surjective g) (hfg : LocallyFinite (f ∘ g)) :
    LocallyFinite f := by
  simpa only [comp_def, surjInv_eq hg] using hfg.comp_injective (injective_surjInv hg)
/-
**LocallyFinite.on_range** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：on_range (hf : LocallyFinite f) : LocallyFinite ((↑) : range f -> Set X)
参数：hf : LocallyFinite f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.of_comp_surjective`：of_comp_surjective {g : ι' -> ι} (hg :
 Surjective g) (hfg : LocallyFinite (f ∘ g)) : LocallyFinite f
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
-/
theorem on_range (hf : LocallyFinite f) : LocallyFinite ((↑) : range f → Set X) :=
  of_comp_surjective rangeFactorization_surjective hf
/-
**LocallyFinite._root_.locallyFinite_iff_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `Lo
callyFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.locallyFinite_iff_smallSets :
    LocallyFinite f ↔ ∀ x, ∀ᶠ s in (𝓝 x).smallSets, { i | (f i ∩ s).Nonempty }.Finite :=
  forall_congr' fun _ => Iff.symm <|
    eventually_smallSets' fun _s _t hst ht =>
      ht.subset fun _i hi => hi.mono <| inter_subset_inter_right _ hst
/-
**LocallyFinite.eventually_smallSets** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_4} [inst : TopologicalSpace X] {f : ι → Set X
},   LocallyFinite f → ∀ (x : X), ∀ᶠ (s : Set X) in (nhds x).smallSets, {i | (f 
i ∩ s).Nonempty}.Finite
参数：x : X；s : Set X；nhds x；f i ∩ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `locallyFinite_iff_smallSets`：∀ {ι : Type u_1} {X : Type u_4} [inst : Top
ologicalSpace X] {f : ι → Set X},   LocallyFinite f ↔ ∀ (x : X), ∀ᶠ (s : Set X) 
in (nhds x).small…
-/
protected theorem eventually_smallSets (hf : LocallyFinite f) (x : X) :
    ∀ᶠ s in (𝓝 x).smallSets, { i | (f i ∩ s).Nonempty }.Finite :=
  locallyFinite_iff_smallSets.mp hf x
/-
**LocallyFinite.exists_mem_basis** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：exists_mem_basis {ι' : Sort*} (hf : LocallyFinite f) {p : ι' -> Prop} {s :
 ι' -> Set X} {x : X} (hb : (𝓝 x).HasBasis p s) : exists i, p i ∧ { j | (f j int
er s i).Nonempty }.Finite
参数：hf : LocallyFinite f；hb : (𝓝 x).HasBasis p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.smallSets`：∀ {α : Type u_1} {ι : Sort u_3} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l.smallSets.HasBasis p fun 
i => 𝒫 s i
· 使用定理 `LocallyFinite.eventually_smallSets`：∀ {ι : Type u_1} {X : Type u_4} [ins
t : TopologicalSpace X] {f : ι → Set X},   LocallyFinite f → ∀ (x : X), ∀ᶠ (s : 
Set X) in (nhds x).small…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem exists_mem_basis {ι' : Sort*} (hf : LocallyFinite f) {p : ι' → Prop} {s : ι' → Set X}
    {x : X} (hb : (𝓝 x).HasBasis p s) : ∃ i, p i ∧ { j | (f j ∩ s i).Nonempty }.Finite :=
  let ⟨i, hpi, hi⟩ := hb.smallSets.eventually_iff.mp (hf.eventually_smallSets x)
  ⟨i, hpi, hi Subset.rfl⟩
/-
**LocallyFinite.nhdsWithin_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_4} [inst : TopologicalSpace X] {f : ι → Set X
},   LocallyFinite f → ∀ (a : X), nhdsWithin a (⋃ i, f i) = ⨆ i, nhdsWithin a (f
 i)
参数：a : X；⋃ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `nhdsWithin_inter_of_mem'`：nhdsWithin_inter_of_mem' {a : α} {s t : Set α}
 (h : t in 𝓝[s] a) : 𝓝[s inter t] a = 𝓝[s] a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_nonempty_self`：iUnion_nonempty_self (s : Set α) : ⋃ _ : s.Non
empty, s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `nhdsWithin_biUnion`：nhdsWithin_biUnion {ι} {I : Set ι} (hI : I.Finite) (
s : ι -> Set α) (a : α) : 𝓝[⋃ i in I, s i] a = ⨆ i in I, 𝓝[s i] a
· 使用定理 `iSup₂_le_iSup`：iSup₂_le_iSup (κ : ι -> Sort*) (f : ι -> α) : ⨆ (i) (_ : 
κ i), f i <= ⨆ i, f i
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Monotone.le_map_iSup`：Monotone.le_map_iSup [CompleteLattice β] {f : α ->
 β} (hf : Monotone f) : ⨆ i, f (s i) <= f (iSup s)
-/
protected theorem nhdsWithin_iUnion (hf : LocallyFinite f) (a : X) :
    𝓝[⋃ i, f i] a = ⨆ i, 𝓝[f i] a := by
  rcases hf a with ⟨U, haU, hfin⟩
  refine le_antisymm ?_ (Monotone.le_map_iSup fun _ _ ↦ nhdsWithin_mono _)
  calc
    𝓝[⋃ i, f i] a = 𝓝[⋃ i, f i ∩ U] a := by
      rw [← iUnion_inter, ← nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds haU)]
    _ = 𝓝[⋃ i ∈ {j | (f j ∩ U).Nonempty}, (f i ∩ U)] a := by
      simp only [mem_ofPred_eq, iUnion_nonempty_self]
    _ = ⨆ i ∈ {j | (f j ∩ U).Nonempty}, 𝓝[f i ∩ U] a := nhdsWithin_biUnion hfin _ _
    _ ≤ ⨆ i, 𝓝[f i ∩ U] a := iSup₂_le_iSup _ _
    _ ≤ ⨆ i, 𝓝[f i] a := iSup_mono fun i ↦ nhdsWithin_mono _ inter_subset_left
/-
**LocallyFinite.continuousOn_iUnion'** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：continuousOn_iUnion' {g : X -> Y} (hf : LocallyFinite f) (hc : forall i x,
 x in closure (f i) -> ContinuousWithinAt g (f i) x) : ContinuousOn g (⋃ i, f i)
参数：hf : LocallyFinite f；hc : forall i x, x in closure (f i) -> ContinuousWithinA
t g (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `LocallyFinite.nhdsWithin_iUnion`：∀ {ι : Type u_1} {X : Type u_4} [inst :
 TopologicalSpace X] {f : ι → Set X},   LocallyFinite f → ∀ (a : X), nhdsWithin 
a (⋃ i, f i) = ⨆ i, n…
· 使用定理 `Filter.tendsto_iSup`：tendsto_iSup {f : α -> β} {x : ι -> Filter α} {y : 
Filter β} : Tendsto f (⨆ i, x i) y ↔ forall i, Tendsto f (x i) y
· 使用定理 `Filter.not_neBot`：not_neBot {f : Filter α} : ¬f.NeBot ↔ f = ⊥
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `Filter.tendsto_bot`：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f 
⊥ l
-/
theorem continuousOn_iUnion' {g : X → Y} (hf : LocallyFinite f)
    (hc : ∀ i x, x ∈ closure (f i) → ContinuousWithinAt g (f i) x) :
    ContinuousOn g (⋃ i, f i) := by
  rintro x -
  rw [ContinuousWithinAt, hf.nhdsWithin_iUnion, tendsto_iSup]
  intro i
  by_cases hx : x ∈ closure (f i)
  · exact hc i _ hx
  · rw [mem_closure_iff_nhdsWithin_neBot, not_neBot] at hx
    rw [hx]
    exact tendsto_bot
/-
**LocallyFinite.continuousOn_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：continuousOn_iUnion {g : X -> Y} (hf : LocallyFinite f) (h_cl : forall i, 
IsClosed (f i)) (h_cont : forall i, ContinuousOn g (f i)) : ContinuousOn g (⋃ i,
 f i)
参数：hf : LocallyFinite f；h_cl : forall i, IsClosed (f i)；h_cont : forall i, Conti
nuousOn g (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.continuousOn_iUnion'`：continuousOn_iUnion' {g : X -> Y} (h
f : LocallyFinite f) (hc : forall i x, x in closure (f i) -> ContinuousWithinAt 
g (f i) x) : ContinuousO…
· 使用定理 `IsClosed.closure_subset`：IsClosed.closure_subset (hs : IsClosed s) : clo
sure s subseteq s
-/
theorem continuousOn_iUnion {g : X → Y} (hf : LocallyFinite f) (h_cl : ∀ i, IsClosed (f i))
    (h_cont : ∀ i, ContinuousOn g (f i)) : ContinuousOn g (⋃ i, f i) :=
  hf.continuousOn_iUnion' fun i x hx ↦ h_cont i x <| (h_cl i).closure_subset hx
/-
**LocallyFinite.continuous'** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_4} {Y : Type u_5} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y] {f : ι → Set X}   {g : X → Y},   LocallyFinite f 
→ ⋃ i, f i = Set.univ → (∀ (i : ι), ∀ x ∈ closure (f i), ContinuousWithinAt g (f
 i) x) → Continuous g
参数：∀ (i : ι), ∀ x ∈ closure (f i), ContinuousWithinAt g (f i) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `LocallyFinite.continuousOn_iUnion'`：continuousOn_iUnion' {g : X -> Y} (h
f : LocallyFinite f) (hc : forall i x, x in closure (f i) -> ContinuousWithinAt 
g (f i) x) : ContinuousO…
-/
protected theorem continuous' {g : X → Y} (hf : LocallyFinite f) (h_cov : ⋃ i, f i = univ)
    (hc : ∀ i x, x ∈ closure (f i) → ContinuousWithinAt g (f i) x) :
    Continuous g :=
  continuousOn_univ.1 <| h_cov ▸ hf.continuousOn_iUnion' hc
/-
**LocallyFinite.continuous** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_4} {Y : Type u_5} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y] {f : ι → Set X}   {g : X → Y},   LocallyFinite f 
→ ⋃ i, f i = Set.univ → (∀ (i : ι), IsClosed (f i)) → (∀ (i : ι), ContinuousOn g
 (f i)) → Continuous g
参数：∀ (i : ι), IsClosed (f i)；∀ (i : ι), ContinuousOn g (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `LocallyFinite.continuousOn_iUnion`：continuousOn_iUnion {g : X -> Y} (hf 
: LocallyFinite f) (h_cl : forall i, IsClosed (f i)) (h_cont : forall i, Continu
ousOn g (f i)) : Contin…
-/
protected theorem continuous {g : X → Y} (hf : LocallyFinite f) (h_cov : ⋃ i, f i = univ)
    (h_cl : ∀ i, IsClosed (f i)) (h_cont : ∀ i, ContinuousOn g (f i)) :
    Continuous g :=
  continuousOn_univ.1 <| h_cov ▸ hf.continuousOn_iUnion h_cl h_cont
/-
**LocallyFinite.closure** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_4} [inst : TopologicalSpace X] {f : ι → Set X
},   LocallyFinite f → LocallyFinite fun i => closure (f i)
参数：f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `interior_mem_nhds`：interior_mem_nhds : interior s in 𝓝 x ↔ s in 𝓝 x
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Set.Nonempty.of_closure`：∀ {X : Type u} [inst : TopologicalSpace X] {s :
 Set X}, (closure s).Nonempty → s.Nonempty
· 使用定理 `IsOpen.closure_inter`：IsOpen.closure_inter (h : IsOpen t) : closure s in
ter t subseteq closure (s inter t)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
protected theorem closure (hf : LocallyFinite f) : LocallyFinite fun i => closure (f i) := by
  intro x
  rcases hf x with ⟨s, hsx, hsf⟩
  refine ⟨interior s, interior_mem_nhds.2 hsx, hsf.subset fun i hi => ?_⟩
  exact (hi.mono isOpen_interior.closure_inter).of_closure.mono
    (inter_subset_inter_right _ interior_subset)
/-
**LocallyFinite.closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：closure_iUnion (h : LocallyFinite f) : closure (⋃ i, f i) = ⋃ i, closure (
f i)
参数：h : LocallyFinite f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocallyFinite.nhdsWithin_iUnion`：∀ {ι : Type u_1} {X : Type u_4} [inst :
 TopologicalSpace X] {f : ι → Set X},   LocallyFinite f → ∀ (a : X), nhdsWithin 
a (⋃ i, f i) = ⨆ i, n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem closure_iUnion (h : LocallyFinite f) : closure (⋃ i, f i) = ⋃ i, closure (f i) := by
  ext x
  simp only [mem_closure_iff_nhdsWithin_neBot, h.nhdsWithin_iUnion, iSup_neBot, mem_iUnion]
/-
**LocallyFinite.isClosed_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：isClosed_iUnion (hf : LocallyFinite f) (hc : forall i, IsClosed (f i)) : I
sClosed (⋃ i, f i)
参数：hf : LocallyFinite f；hc : forall i, IsClosed (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocallyFinite.closure_iUnion`：closure_iUnion (h : LocallyFinite f) : clo
sure (⋃ i, f i) = ⋃ i, closure (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isClosed_iUnion (hf : LocallyFinite f) (hc : ∀ i, IsClosed (f i)) :
    IsClosed (⋃ i, f i) := by
  simp only [← closure_eq_iff_isClosed, hf.closure_iUnion, (hc _).closure_eq]

/-- If `f : β → Set α` is a locally finite family of closed sets, then for any `x : α`, the
intersection of the complements to `f i`, `x ∉ f i`, is a neighbourhood of `x`. -/
/-
**LocallyFinite.iInter_compl_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：iInter_compl_mem_nhds (hf : LocallyFinite f) (hc : forall i, IsClosed (f i
)) (x : X) : (⋂ (i) (_ : x ∉ f i), (f i)ᶜ) in 𝓝 x
参数：hf : LocallyFinite f；hc : forall i, IsClosed (f i)；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `LocallyFinite.isClosed_iUnion`：isClosed_iUnion (hf : LocallyFinite f) (h
c : forall i, IsClosed (f i)) : IsClosed (⋃ i, f i)
· 使用定理 `LocallyFinite.comp_injective`：comp_injective {g : ι' -> ι} (hf : Locally
Finite f) (hg : Injective g) : LocallyFinite (f ∘ g)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_subtype`：iInter_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j

--- 原说明 ---
If `f : β → Set α` is a locally finite family of closed sets, then for any `x : 
α`, the
intersection of the complements to `f i`, `x ∉ f i`, is a neighbourhood of `x`.
-/
theorem iInter_compl_mem_nhds (hf : LocallyFinite f) (hc : ∀ i, IsClosed (f i)) (x : X) :
    (⋂ (i) (_ : x ∉ f i), (f i)ᶜ) ∈ 𝓝 x := by
  refine IsOpen.mem_nhds ?_ (mem_iInter₂.2 fun i => id)
  suffices IsClosed (⋃ i : { i // x ∉ f i }, f i) by
    rwa [← isOpen_compl_iff, compl_iUnion, iInter_subtype] at this
  exact (hf.comp_injective Subtype.val_injective).isClosed_iUnion fun i => hc _

/-- Let `f : ℕ → Π a, β a` be a sequence of (dependent) functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F : Π a, β a` such that for any `x`, we have `f n x = F x` on the product of an infinite
interval `[N, +∞)` and a neighbourhood of `x`.

We formulate the conclusion in terms of the product of filter `Filter.atTop` and `𝓝 x`. -/
/-
**LocallyFinite.exists_forall_eventually_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `Loca
llyFinite`。
形式化陈述：exists_forall_eventually_eq_prod {π : X -> Sort*} {f : Nat -> forall x : X
, π x} (hf : LocallyFinite fun n => { x | f (n + 1) x != f n x }) : exists F : f
orall x : X, π x, forall x, forallᶠ p : Nat × X in atTop ×ˢ 𝓝 x, f p.1 p.2 = F p
.2
参数：hf : LocallyFinite fun n => { x | f (n + 1) x != f n x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Let `f : ℕ → Π a, β a` be a sequence of (dependent) functions on a topological s
pace. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. The
n there exists a
function `F : Π a, β a` such that for any `x`, we have `f n x = F x` on the prod
uct of an infinite
interval `[N, +∞)` and a neighbourhood of `x`.

We formulate the conclusion in terms of the product of filter `Filter.atTop` and
 `𝓝 x`.
-/
theorem exists_forall_eventually_eq_prod {π : X → Sort*} {f : ℕ → ∀ x : X, π x}
    (hf : LocallyFinite fun n => { x | f (n + 1) x ≠ f n x }) :
    ∃ F : ∀ x : X, π x, ∀ x, ∀ᶠ p : ℕ × X in atTop ×ˢ 𝓝 x, f p.1 p.2 = F p.2 := by
  choose U hUx hU using hf
  choose N hN using fun x => (hU x).bddAbove
  replace hN : ∀ (x), ∀ n > N x, ∀ y ∈ U x, f (n + 1) y = f n y :=
    fun x n hn y hy => by_contra fun hne => hn.lt.not_ge <| hN x ⟨y, hne, hy⟩
  replace hN : ∀ (x), ∀ n ≥ N x + 1, ∀ y ∈ U x, f n y = f (N x + 1) y :=
    fun x n hn y hy => Nat.le_induction rfl (fun k hle => (hN x _ hle _ hy).trans) n hn
  refine ⟨fun x => f (N x + 1) x, fun x => ?_⟩
  filter_upwards [Filter.prod_mem_prod (eventually_gt_atTop (N x)) (hUx x)]
  rintro ⟨n, y⟩ ⟨hn : N x < n, hy : y ∈ U x⟩
  calc
    f n y = f (N x + 1) y := hN _ _ hn _ hy
    _ = f (max (N x + 1) (N y + 1)) y := (hN _ _ (le_max_left _ _) _ hy).symm
    _ = f (N y + 1) y := hN _ _ (le_max_right _ _) _ (mem_of_mem_nhds <| hUx y)

/-- Let `f : ℕ → Π a, β a` be a sequence of (dependent) functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F : Π a, β a` such that for any `x`, for sufficiently large values of `n`, we have
`f n y = F y` in a neighbourhood of `x`. -/
/-
**LocallyFinite.exists_forall_eventually_atTop_eventually_eq'** 是 Mathlib 中的一个定理
，位于命名空间 `LocallyFinite`。
形式化陈述：exists_forall_eventually_atTop_eventually_eq' {π : X -> Sort*} {f : Nat ->
 forall x : X, π x} (hf : LocallyFinite fun n => { x | f (n + 1) x != f n x }) :
 exists F : forall x : X, π x, forall x, forallᶠ n : Nat in atTop, forallᶠ y : X
 in 𝓝 x, f n y = F y
参数：hf : LocallyFinite fun n => { x | f (n + 1) x != f n x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Filter.Eventually.curry`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α}
 {lb : Filter β} {p : α × β → Prop},   (∀ᶠ (x : α × β) in la ×ˢ lb, p x) → ∀ᶠ (x
 : α) in la, …
· 使用定理 `LocallyFinite.exists_forall_eventually_eq_prod`：exists_forall_eventually
_eq_prod {π : X -> Sort*} {f : Nat -> forall x : X, π x} (hf : LocallyFinite fun
 n => { x | f (n + 1) x != f n x }) …

--- 原说明 ---
Let `f : ℕ → Π a, β a` be a sequence of (dependent) functions on a topological s
pace. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. The
n there exists a
function `F : Π a, β a` such that for any `x`, for sufficiently large values of 
`n`, we have
`f n y = F y` in a neighbourhood of `x`.
-/
theorem exists_forall_eventually_atTop_eventually_eq' {π : X → Sort*} {f : ℕ → ∀ x : X, π x}
    (hf : LocallyFinite fun n => { x | f (n + 1) x ≠ f n x }) :
    ∃ F : ∀ x : X, π x, ∀ x, ∀ᶠ n : ℕ in atTop, ∀ᶠ y : X in 𝓝 x, f n y = F y :=
  hf.exists_forall_eventually_eq_prod.imp fun _F hF x => (hF x).curry

/-- Let `f : ℕ → α → β` be a sequence of functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. Then there exists a
function `F :  α → β` such that for any `x`, for sufficiently large values of `n`, we have
`f n =ᶠ[𝓝 x] F`. -/
/-
**LocallyFinite.exists_forall_eventually_atTop_eventuallyEq** 是 Mathlib 中的一个定理，位
于命名空间 `LocallyFinite`。
形式化陈述：exists_forall_eventually_atTop_eventuallyEq {f : Nat -> X -> α} (hf : Loca
llyFinite fun n => { x | f (n + 1) x != f n x }) : exists F : X -> α, forall x, 
forallᶠ n : Nat in atTop, f n =ᶠ[𝓝 x] F
参数：hf : LocallyFinite fun n => { x | f (n + 1) x != f n x }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.exists_forall_eventually_atTop_eventually_eq'`：exists_fora
ll_eventually_atTop_eventually_eq' {π : X -> Sort*} {f : Nat -> forall x : X, π 
x} (hf : LocallyFinite fun n => { x | f (n + 1) x…

--- 原说明 ---
Let `f : ℕ → α → β` be a sequence of functions on a topological space. Suppose
that the family of sets `s n = {x | f (n + 1) x ≠ f n x}` is locally finite. The
n there exists a
function `F :  α → β` such that for any `x`, for sufficiently large values of `n
`, we have
`f n =ᶠ[𝓝 x] F`.
-/
theorem exists_forall_eventually_atTop_eventuallyEq {f : ℕ → X → α}
    (hf : LocallyFinite fun n => { x | f (n + 1) x ≠ f n x }) :
    ∃ F : X → α, ∀ x, ∀ᶠ n : ℕ in atTop, f n =ᶠ[𝓝 x] F :=
  hf.exists_forall_eventually_atTop_eventually_eq'
/-
**LocallyFinite.preimage_continuous** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：preimage_continuous {g : Y -> X} (hf : LocallyFinite f) (hg : Continuous g
) : LocallyFinite (g ⁻¹' f ·)
参数：hf : LocallyFinite f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
-/
theorem preimage_continuous {g : Y → X} (hf : LocallyFinite f) (hg : Continuous g) :
    LocallyFinite (g ⁻¹' f ·) := fun x =>
  let ⟨s, hsx, hs⟩ := hf (g x)
  ⟨g ⁻¹' s, hg.continuousAt hsx, hs.subset fun _ ⟨y, hy⟩ => ⟨g y, hy⟩⟩
/-
**LocallyFinite.prod_right** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：prod_right (hf : LocallyFinite f) (g : ι -> Set Y) : LocallyFinite (fun i 
=> f i ×ˢ g i)
参数：hf : LocallyFinite f；g : ι -> Set Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `LocallyFinite.preimage_continuous`：preimage_continuous {g : Y -> X} (hf 
: LocallyFinite f) (hg : Continuous g) : LocallyFinite (g ⁻¹' f ·)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Set.prod_subset_preimage_fst`：prod_subset_preimage_fst (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.fst ⁻¹' s
-/
theorem prod_right (hf : LocallyFinite f) (g : ι → Set Y) : LocallyFinite (fun i ↦ f i ×ˢ g i) :=
  (hf.preimage_continuous continuous_fst).subset fun _ ↦ prod_subset_preimage_fst _ _
/-
**LocallyFinite.prod_left** 是 Mathlib 中的一个定理，位于命名空间 `LocallyFinite`。
形式化陈述：prod_left {g : ι -> Set Y} (hg : LocallyFinite g) (f : ι -> Set X) : Local
lyFinite (fun i => f i ×ˢ g i)
参数：hg : LocallyFinite g；f : ι -> Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `LocallyFinite.preimage_continuous`：preimage_continuous {g : Y -> X} (hf 
: LocallyFinite f) (hg : Continuous g) : LocallyFinite (g ⁻¹' f ·)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `Set.prod_subset_preimage_snd`：prod_subset_preimage_snd (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.snd ⁻¹' t
-/
theorem prod_left {g : ι → Set Y} (hg : LocallyFinite g) (f : ι → Set X) :
    LocallyFinite (fun i ↦ f i ×ˢ g i) :=
  (hg.preimage_continuous continuous_snd).subset fun _ ↦ prod_subset_preimage_snd _ _

end LocallyFinite

@[simp]
/-
**Equiv.locallyFinite_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.locallyFinite_comp_iff (e : ι' ≃ ι) : LocallyFinite (f ∘ e) ↔ Locall
yFinite f
参数：e : ι' ≃ ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `LocallyFinite.comp_injective`：comp_injective {g : ι' -> ι} (hf : Locally
Finite f) (hg : Injective g) : LocallyFinite (f ∘ g)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem Equiv.locallyFinite_comp_iff (e : ι' ≃ ι) : LocallyFinite (f ∘ e) ↔ LocallyFinite f :=
  ⟨fun h => by simpa only [comp_def, e.apply_symm_apply] using h.comp_injective e.symm.injective,
    fun h => h.comp_injective e.injective⟩
/-
**locallyFinite_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyFinite_sum {f : ι oplus ι' -> Set X} : LocallyFinite f ↔ LocallyFin
ite (f ∘ Sum.inl) ∧ LocallyFinite (f ∘ Sum.inr)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem locallyFinite_sum {f : ι ⊕ ι' → Set X} :
    LocallyFinite f ↔ LocallyFinite (f ∘ Sum.inl) ∧ LocallyFinite (f ∘ Sum.inr) := by
  simp only [locallyFinite_iff_smallSets, ← forall_and, ← finite_preimage_inl_and_inr,
    preimage_ofPred_eq, (· ∘ ·), eventually_and]
/-
**LocallyFinite.sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LocallyFinite.sumElim {g : ι' -> Set X} (hf : LocallyFinite f) (hg : Local
lyFinite g) : LocallyFinite (Sum.elim f g)
参数：hf : LocallyFinite f；hg : LocallyFinite g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `locallyFinite_sum`：locallyFinite_sum {f : ι oplus ι' -> Set X} : Locally
Finite f ↔ LocallyFinite (f ∘ Sum.inl) ∧ LocallyFinite (f ∘ Sum.inr)
-/
theorem LocallyFinite.sumElim {g : ι' → Set X} (hf : LocallyFinite f) (hg : LocallyFinite g) :
    LocallyFinite (Sum.elim f g) :=
  locallyFinite_sum.mpr ⟨hf, hg⟩
/-
**locallyFinite_option** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyFinite_option {f : Option ι -> Set X} : LocallyFinite f ↔ LocallyFi
nite (f ∘ some)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.locallyFinite_comp_iff`：Equiv.locallyFinite_comp_iff (e : ι' ≃ ι) 
: LocallyFinite (f ∘ e) ↔ LocallyFinite f
· 使用定理 `locallyFinite_sum`：locallyFinite_sum {f : ι oplus ι' -> Set X} : Locally
Finite f ↔ LocallyFinite (f ∘ Sum.inl) ∧ LocallyFinite (f ∘ Sum.inr)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem locallyFinite_option {f : Option ι → Set X} :
    LocallyFinite f ↔ LocallyFinite (f ∘ some) := by
  rw [← (Equiv.optionEquivSumPUnit.{0, _} ι).symm.locallyFinite_comp_iff, locallyFinite_sum]
  simp only [locallyFinite_of_finite, and_true]
  rfl
/-
**LocallyFinite.option_elim'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LocallyFinite.option_elim' (hf : LocallyFinite f) (s : Set X) : LocallyFin
ite (Option.elim' s f)
参数：hf : LocallyFinite f；s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `locallyFinite_option`：locallyFinite_option {f : Option ι -> Set X} : Loc
allyFinite f ↔ LocallyFinite (f ∘ some)
-/
theorem LocallyFinite.option_elim' (hf : LocallyFinite f) (s : Set X) :
    LocallyFinite (Option.elim' s f) :=
  locallyFinite_option.2 hf
/-
**LocallyFinite.eventually_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LocallyFinite.eventually_subset {s : ι -> Set X} (hs : LocallyFinite s) (h
s' : forall i, IsClosed (s i)) (x : X) : forallᶠ y in 𝓝 x, {i | y in s i} subset
eq {i | x in s i}
参数：hs : LocallyFinite s；hs' : forall i, IsClosed (s i)；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `LocallyFinite.iInter_compl_mem_nhds`：iInter_compl_mem_nhds (hf : Locally
Finite f) (hc : forall i, IsClosed (f i)) (x : X) : (⋂ (i) (_ : x ∉ f i), (f i)ᶜ
) in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem LocallyFinite.eventually_subset {s : ι → Set X}
    (hs : LocallyFinite s) (hs' : ∀ i, IsClosed (s i)) (x : X) :
    ∀ᶠ y in 𝓝 x, {i | y ∈ s i} ⊆ {i | x ∈ s i} := by
  filter_upwards [hs.iInter_compl_mem_nhds hs' x] with y hy i hi
  push _ ∈ _ at hy
  exact not_imp_not.mp (hy i) hi
