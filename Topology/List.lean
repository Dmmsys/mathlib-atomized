/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Order.Filter.ListTraverse
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Data.Vector.Basic

/-!
# Topology on lists and vectors

-/

@[expose] public section


open TopologicalSpace Set Filter

open Topology

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (List α) :=
  TopologicalSpace.mkOfNhds (traverse nhds)
/-
**nhds_list** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_list (as : List α) : 𝓝 as = traverse 𝓝 as
参数：as : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.nhds_mkOfNhds`：nhds_mkOfNhds (n : α -> Filter α) (a : α
) (h₀ : pure <= n) (h₁ : forall a, forall s in n a, forallᶠ y in n a, s in n y) 
: @nhds α (Topologic…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Filter.seq_mono`：seq_mono {f₁ f₂ : Filter (α -> β)} {g₁ g₂ : Filter α} (
hf : f₁ <= f₂) (hg : g₁ <= g₂) : f₁.seq g₁ <= f₂.seq g₂
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `Filter.instLawfulApplicative`：LawfulApplicative Filter
· 使用定理 `LawfulApplicative.pure_seq`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : f α),   pure g <
*> x = g <$> x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_traverse_iff`：mem_traverse_iff (fs : List β) (t : Set (List α
)) : t in traverse f fs ↔ exists us : List (Set α), Forall₂ (fun b (s : Set α) =
> s in f b) f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `trivial`：True
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.seq_mono`：seq_mono {s₀ s₁ : Set (α -> β)} {t₀ t₁ : Set α} (hs : s₀ s
ubseteq s₁) (ht : t₀ subseteq t₁) : seq s₀ t₀ subseteq seq s₁ t₁
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Filter.mem_traverse`：∀ {α β γ : Type u} {f : β → Filter α} {s : γ → Set 
α} (fs : List β) (us : List γ),   List.Forall₂ (fun b c => s c ∈ f b) fs us → tr
averse s …
· 使用定理 `List.Forall₂.imp`：∀ {α : Type u_1} {β : Type u_2} {R S : α → β → Prop}, 
  (∀ (a : α) (b : β), R a b → S a b) → ∀ {l₁ : List α} {l₂ : List β}, List.Foral
l₂ R l…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `List.mem_traverse`：∀ {α' β' : Type u} {f : α' → Set β'} (l : List α') (n
 : List β'),   n ∈ traverse f l ↔ List.Forall₂ (fun b a => b ∈ f a) n l
· 使用定理 `List.Forall₂.flip`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} {a
 : List α} {b : List β},   List.Forall₂ (flip R) b a → List.Forall₂ R a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
-/
theorem nhds_list (as : List α) : 𝓝 as = traverse 𝓝 as := by
  refine nhds_mkOfNhds _ _ ?_ ?_
  · intro l
    induction l with
    | nil => exact le_rfl
    | cons a l ih =>
      suffices List.cons <$> pure a <*> pure l ≤ List.cons <$> 𝓝 a <*> traverse 𝓝 l by
        simpa only [functor_norm] using! this
      exact Filter.seq_mono (Filter.map_mono <| pure_le_nhds a) ih
  · intro l s hs
    rcases (mem_traverse_iff _ _).1 hs with ⟨u, hu, hus⟩
    clear as hs
    have : ∃ v : List (Set α), l.Forall₂ (fun a s => IsOpen s ∧ a ∈ s) v ∧ sequence v ⊆ s := by
      induction hu generalizing s with
      | nil =>
        exists []
        simp only [List.forall₂_nil_left_iff]
        exact ⟨trivial, hus⟩
      | cons ht _ ih =>
        rcases mem_nhds_iff.1 ht with ⟨u, hut, hu⟩
        rcases ih _ Subset.rfl with ⟨v, hv, hvss⟩
        exact
          ⟨u::v, List.Forall₂.cons hu hv,
            Subset.trans (Set.seq_mono (Set.image_mono hut) hvss) hus⟩
    rcases this with ⟨v, hv, hvs⟩
    have : ∀ᶠ y in traverse 𝓝 l, y ∈ sequence v :=
      mem_traverse _ _ <| hv.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha
    refine Eventually.mono this fun u hu ↦ ?_
    have hu := (List.mem_traverse _ _).1 hu
    have : List.Forall₂ (fun a s => IsOpen s ∧ a ∈ s) u v := by
      refine List.Forall₂.flip ?_
      replace hv := hv.flip
      simp only [List.forall₂_and_left, Function.flip_def] at hv ⊢
      exact ⟨hv.1, hu.flip⟩
    grw [← hvs]
    exact mem_traverse _ _ (this.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha)

@[simp]
/-
**nhds_nil** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_nil : 𝓝 ([] : List α) = pure []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_list`：nhds_list (as : List α) : 𝓝 as = traverse 𝓝 as
· 使用定理 `List.traverse_nil`：traverse_nil : traverse f ([] : List α') = (pure [] :
 F (List β'))
-/
theorem nhds_nil : 𝓝 ([] : List α) = pure [] := by
  rw [nhds_list, List.traverse_nil _]
/-
**nhds_cons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_cons (a : α) (l : List α) : 𝓝 (a::l) = List.cons < > 𝓝 a <*> 𝓝 l
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_list`：nhds_list (as : List α) : 𝓝 as = traverse 𝓝 as
· 使用定理 `List.traverse_cons`：traverse_cons (a : α') (l : List α') : traverse f (a
 :: l) = (· :: ·) < > f a <*> traverse f l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nhds_cons (a : α) (l : List α) : 𝓝 (a::l) = List.cons <$> 𝓝 a <*> 𝓝 l := by
  rw [nhds_list, List.traverse_cons _, ← nhds_list]
/-
**List.tendsto_cons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.tendsto_cons {a : α} {l : List α} : Tendsto (fun p : α × List α => Li
st.cons p.1 p.2) (𝓝 a ×ˢ 𝓝 l) (𝓝 (a::l))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_cons`：nhds_cons (a : α) (l : List α) : 𝓝 (a::l) = List.cons < > 𝓝 a
 <*> 𝓝 l
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `Filter.map_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (m : α ×
 β → γ) (f : Filter α) (g : Filter β),   Filter.map m (f ×ˢ g) = (Filter.map (fu
n a b…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem List.tendsto_cons {a : α} {l : List α} :
    Tendsto (fun p : α × List α => List.cons p.1 p.2) (𝓝 a ×ˢ 𝓝 l) (𝓝 (a::l)) := by
  rw [nhds_cons, Tendsto, Filter.map_prod]; exact le_rfl
/-
**Filter.Tendsto.cons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.cons {α : Type*} {f : α -> β} {g : α -> List β} {a : Filter
 α} {b : β} {l : List β} (hf : Tendsto f a (𝓝 b)) (hg : Tendsto g a (𝓝 l)) : Ten
dsto (fun a => List.cons (f a) (g a)) a (𝓝 (b::l))
参数：hf : Tendsto f a (𝓝 b)；hg : Tendsto g a (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `List.tendsto_cons`：List.tendsto_cons {a : α} {l : List α} : Tendsto (fun
 p : α × List α => List.cons p.1 p.2) (𝓝 a ×ˢ 𝓝 l) (𝓝 (a::l))
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
-/
theorem Filter.Tendsto.cons {α : Type*} {f : α → β} {g : α → List β} {a : Filter α} {b : β}
    {l : List β} (hf : Tendsto f a (𝓝 b)) (hg : Tendsto g a (𝓝 l)) :
    Tendsto (fun a => List.cons (f a) (g a)) a (𝓝 (b::l)) :=
  List.tendsto_cons.comp (Tendsto.prodMk hf hg)

namespace List

/-
**List.tendsto_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tendsto_cons_iff {β : Type*} {f : List α -> β} {b : Filter β} {a : α} {l :
 List α} : Tendsto f (𝓝 (a::l)) b ↔ Tendsto (fun p : α × List α => f (p.1::p.2))
 (𝓝 a ×ˢ 𝓝 l) b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_cons`：nhds_cons (a : α) (l : List α) : 𝓝 (a::l) = List.cons < > 𝓝 a
 <*> 𝓝 l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.prod_eq`：prod_eq : f ×ˢ g = (f.map Prod.mk).seq g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_def`：map_def {α β} (m : α -> β) (f : Filter α) : m < > f = ma
p m f
· 使用定理 `Filter.seq_eq_filter_seq`：seq_eq_filter_seq {α β : Type u} (f : Filter (
α -> β)) (g : Filter α) : f <*> g = seq f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_seq`：map_seq (f : β -> γ) (x : F (α -> β)) (y : F α) : f < > (x <*> 
y) = (f ∘ ·) < > x <*> y
· 使用定理 `Filter.instLawfulApplicative`：LawfulApplicative Filter
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `Filter.instLawfulFunctor`：LawfulFunctor Filter
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_cons_iff {β : Type*} {f : List α → β} {b : Filter β} {a : α} {l : List α} :
    Tendsto f (𝓝 (a::l)) b ↔ Tendsto (fun p : α × List α => f (p.1::p.2)) (𝓝 a ×ˢ 𝓝 l) b := by
  have : 𝓝 (a::l) = (𝓝 a ×ˢ 𝓝 l).map fun p : α × List α => p.1::p.2 := by
    simp only [nhds_cons, Filter.prod_eq, (Filter.map_def _ _).symm,
      (Filter.seq_eq_filter_seq _ _).symm]
    simp [-Filter.map_def, Function.comp_def, functor_norm]
  rw [this, Filter.tendsto_map'_iff]; rfl
/-
**List.continuous_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：continuous_cons : Continuous fun x : α × List α => (x.1::x.2 : List α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Filter.Tendsto.cons`：Filter.Tendsto.cons {α : Type*} {f : α -> β} {g : α
 -> List β} {a : Filter α} {b : β} {l : List β} (hf : Tendsto f a (𝓝 b)) (hg : T
endsto g …
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p
· 使用定理 `continuousAt_snd`：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p
-/
theorem continuous_cons : Continuous fun x : α × List α => (x.1::x.2 : List α) :=
  continuous_iff_continuousAt.mpr fun ⟨_x, _y⟩ => continuousAt_fst.cons continuousAt_snd
/-
**List.tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {β : Type u_3} {f : List α → 
β} {r : List α → Filter β},   Filter.Tendsto f (pure []) (r []) →     (∀ (l : Li
st α) (a : α),         Filter.Tendsto f (nhds l) (r l) → Filter.Tendsto (fun p =
> f (p.1 :: p.2)) (nhds a ×ˢ nhds l) (r (a :: l))) →       ∀ (l : List α), Filte
r.Tendsto f (nhds l) (r l)
参数：pure []；r []；∀ (l : List α) (a : α),         Filter.Tendsto f (nhds l) (r l) 
→ Filter.Tendsto (fun p => f (p.1 :: p.2)) (nhds a ×ˢ nhds l) (r (a :: l))；l : L
ist α；nhds l；r l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_nhds {β : Type*} {f : List α → β} {r : List α → Filter β}
    (h_nil : Tendsto f (pure []) (r []))
    (h_cons :
      ∀ l a,
        Tendsto f (𝓝 l) (r l) →
          Tendsto (fun p : α × List α => f (p.1::p.2)) (𝓝 a ×ˢ 𝓝 l) (r (a::l))) :
    ∀ l, Tendsto f (𝓝 l) (r l)
  | [] => by rwa [nhds_nil]
  | a::l => by
    rw [tendsto_cons_iff]; exact h_cons l a (@tendsto_nhds _ _ _ h_nil h_cons l)
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DiscreteTopology α] : DiscreteTopology (List α) := by
  rw [discreteTopology_iff_nhds]; intro l; induction l <;> simp [*, nhds_cons]
/-
**List.continuousAt_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：continuousAt_length : forall l : List α, ContinuousAt List.length l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `List.tendsto_nhds`：∀ {α : Type u_1} [inst : TopologicalSpace α] {β : Typ
e u_3} {f : List α → β} {r : List α → Filter β},   Filter.Tendsto f (pure []) (r
 []) → …
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
-/
theorem continuousAt_length : ∀ l : List α, ContinuousAt List.length l := by
  simp only [ContinuousAt, nhds_discrete]
  refine tendsto_nhds ?_ ?_
  · exact tendsto_pure_pure _ _
  · intro l a ih
    dsimp only [List.length]
    refine Tendsto.comp (tendsto_pure_pure (fun x => x + 1) _) ?_
    exact Tendsto.comp ih tendsto_snd

/-- Continuity of `insertIdx` in terms of `Tendsto`. -/
/-
**List.tendsto_insertIdx'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tendsto_insertIdx' {a : α} : forall {n : Nat} {l : List α}, Tendsto (fun p
 : α × List α => p.2.insertIdx n p.1) (𝓝 a ×ˢ 𝓝 l) (𝓝 (l.insertIdx n a)) | 0, _ 
=> tendsto_cons | n + 1, [] => by simp | n + 1, a'::l => by have : 𝓝 a ×ˢ 𝓝 (a':
:l) = (𝓝 a ×ˢ (𝓝 a' ×ˢ 𝓝 l)).map fun p : α × α × List α => (p.1, p.2.1::p.2.2)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuity of `insertIdx` in terms of `Tendsto`.
-/
theorem tendsto_insertIdx' {a : α} :
    ∀ {n : ℕ} {l : List α},
      Tendsto (fun p : α × List α => p.2.insertIdx n p.1) (𝓝 a ×ˢ 𝓝 l) (𝓝 (l.insertIdx n a))
  | 0, _ => tendsto_cons
  | n + 1, [] => by simp
  | n + 1, a'::l => by
    have : 𝓝 a ×ˢ 𝓝 (a'::l) =
        (𝓝 a ×ˢ (𝓝 a' ×ˢ 𝓝 l)).map fun p : α × α × List α => (p.1, p.2.1::p.2.2) := by
      simp only [nhds_cons, Filter.prod_eq, ← Filter.map_def, ← Filter.seq_eq_filter_seq]
      simp [-Filter.map_def, Function.comp_def, functor_norm]
    rw [this, tendsto_map'_iff]
    exact
      (tendsto_fst.comp tendsto_snd).cons
        ((@tendsto_insertIdx' _ n l).comp <| tendsto_fst.prodMk <| tendsto_snd.comp tendsto_snd)
/-
**List.tendsto_insertIdx** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tendsto_insertIdx {β} {n : Nat} {a : α} {l : List α} {f : β -> α} {g : β -
> List α} {b : Filter β} (hf : Tendsto f b (𝓝 a)) (hg : Tendsto g b (𝓝 l)) : Ten
dsto (fun b : β => (g b).insertIdx n (f b)) b (𝓝 (l.insertIdx n a))
参数：hf : Tendsto f b (𝓝 a)；hg : Tendsto g b (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `List.tendsto_insertIdx'`：tendsto_insertIdx' {a : α} : forall {n : Nat} {
l : List α}, Tendsto (fun p : α × List α => p.2.insertIdx n p.1) (𝓝 a ×ˢ 𝓝 l) (𝓝
 (l.insertIdx…
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
-/
theorem tendsto_insertIdx {β} {n : ℕ} {a : α} {l : List α} {f : β → α} {g : β → List α}
    {b : Filter β} (hf : Tendsto f b (𝓝 a)) (hg : Tendsto g b (𝓝 l)) :
    Tendsto (fun b : β => (g b).insertIdx n (f b)) b (𝓝 (l.insertIdx n a)) :=
  tendsto_insertIdx'.comp (hf.prodMk hg)
/-
**List.continuous_insertIdx** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：continuous_insertIdx {n : Nat} : Continuous fun p : α × List α => p.2.inse
rtIdx n p.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `List.tendsto_insertIdx'`：tendsto_insertIdx' {a : α} : forall {n : Nat} {
l : List α}, Tendsto (fun p : α × List α => p.2.insertIdx n p.1) (𝓝 a ×ˢ 𝓝 l) (𝓝
 (l.insertIdx…
-/
theorem continuous_insertIdx {n : ℕ} : Continuous fun p : α × List α => p.2.insertIdx n p.1 :=
  continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt, nhds_prod_eq]; exact tendsto_insertIdx'
/-
**List.tendsto_eraseIdx** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {n : ℕ} {l : List α},   Filte
r.Tendsto (fun x => x.eraseIdx n) (nhds l) (nhds (l.eraseIdx n))
参数：fun x => x.eraseIdx n；nhds l；nhds (l.eraseIdx n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_eraseIdx :
    ∀ {n : ℕ} {l : List α}, Tendsto (eraseIdx · n) (𝓝 l) (𝓝 (eraseIdx l n))
  | _, [] => by rw [nhds_nil]; exact tendsto_pure_nhds _ _
  | 0, a::l => by rw [tendsto_cons_iff]; exact tendsto_snd
  | n + 1, a::l => by
    rw [tendsto_cons_iff]
    dsimp [eraseIdx]
    exact tendsto_fst.cons ((@tendsto_eraseIdx n l).comp tendsto_snd)
/-
**List.continuous_eraseIdx** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：continuous_eraseIdx {n : Nat} : Continuous fun l : List α => eraseIdx l n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `List.tendsto_eraseIdx`：∀ {α : Type u_1} [inst : TopologicalSpace α] {n :
 ℕ} {l : List α},   Filter.Tendsto (fun x => x.eraseIdx n) (nhds l) (nhds (l.era
seIdx n))
-/
theorem continuous_eraseIdx {n : ℕ} : Continuous fun l : List α => eraseIdx l n :=
  continuous_iff_continuousAt.mpr fun _a => tendsto_eraseIdx

@[to_additive]
/-
**List.tendsto_prod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tendsto_prod [MulOneClass α] [ContinuousMul α] {l : List α} : Tendsto List
.prod (𝓝 l) (𝓝 l.prod)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_nil`：nhds_nil : 𝓝 ([] : List α) = pure []
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem tendsto_prod [MulOneClass α] [ContinuousMul α] {l : List α} :
    Tendsto List.prod (𝓝 l) (𝓝 l.prod) := by
  induction l with
  | nil => simp +contextual [nhds_nil, mem_of_mem_nhds, tendsto_pure_left]
  | cons x l ih =>
    simp_rw [tendsto_cons_iff, prod_cons]
    have := continuous_iff_continuousAt.mp continuous_mul (x, l.prod)
    rw [ContinuousAt, nhds_prod_eq] at this
    exact this.comp (tendsto_id.prodMap ih)

@[to_additive]
/-
**List.continuous_prod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：continuous_prod [MulOneClass α] [ContinuousMul α] : Continuous (prod : Lis
t α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `List.tendsto_prod`：tendsto_prod [MulOneClass α] [ContinuousMul α] {l : L
ist α} : Tendsto List.prod (𝓝 l) (𝓝 l.prod)
-/
theorem continuous_prod [MulOneClass α] [ContinuousMul α] : Continuous (prod : List α → α) :=
  continuous_iff_continuousAt.mpr fun _l => tendsto_prod

end List

namespace List.Vector

/-
**List.Vector.** 是 Mathlib 中的一个实例，位于命名空间 `List.Vector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : TopologicalSpace (Vector α n) :=
  inferInstanceAs <| TopologicalSpace (Subtype _)

set_option backward.isDefEq.respectTransparency false in
/-
**List.Vector.tendsto_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：tendsto_cons {n : Nat} {a : α} {l : Vector α n} : Tendsto (fun p : α × Vec
tor α n => p.1 ::ᵥ p.2) (𝓝 a ×ˢ 𝓝 l) (𝓝 (a ::ᵥ l))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_subtype_rng`：∀ {X : Type u} [inst : TopologicalSpace X] {Y : Typ
e u_5} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p}   {x : Subtype p}, Filt
er.Tendst…
· 使用定理 `List.Vector.cons_val`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector 
α n), ↑(a ::ᵥ v) = a :: ↑v
· 使用定理 `Filter.Tendsto.cons`：Filter.Tendsto.cons {α : Type*} {f : α -> β} {g : α
 -> List β} {a : Filter α} {b : β} {l : List β} (hf : Tendsto f a (𝓝 b)) (hg : T
endsto g …
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `continuousAt_subtype_val`：continuousAt_subtype_val {p : X -> Prop} {x : 
Subtype p} : ContinuousAt ((↑) : Subtype p -> X) x
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
-/
theorem tendsto_cons {n : ℕ} {a : α} {l : Vector α n} :
    Tendsto (fun p : α × Vector α n => p.1 ::ᵥ p.2) (𝓝 a ×ˢ 𝓝 l) (𝓝 (a ::ᵥ l)) := by
  rw [tendsto_subtype_rng, Vector.cons_val]
  exact tendsto_fst.cons (Tendsto.comp continuousAt_subtype_val tendsto_snd)

set_option backward.isDefEq.respectTransparency false in
/-
**List.Vector.tendsto_insertIdx** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {n : ℕ} {i : Fin (n + 1)} {a 
: α} {l : List.Vector α n},   Filter.Tendsto (fun p => List.Vector.insertIdx p.1
 i p.2) (nhds a ×ˢ nhds l) (nhds (List.Vector.insertIdx a i l))
参数：n + 1；fun p => List.Vector.insertIdx p.1 i p.2；nhds a ×ˢ nhds l；nhds (List.Ve
ctor.insertIdx a i l)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.insertIdx.eq_1`：∀ {α : Type u_1} {n : ℕ} (a : α) (i : Fin (n
 + 1)) (v : List.Vector α n),   List.Vector.insertIdx a i v = ⟨(↑v).insertIdx (↑
i) a, ⋯⟩
· 使用定理 `tendsto_subtype_rng`：∀ {X : Type u} [inst : TopologicalSpace X] {Y : Typ
e u_5} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p}   {x : Subtype p}, Filt
er.Tendst…
· 使用定理 `List.tendsto_insertIdx`：tendsto_insertIdx {β} {n : Nat} {a : α} {l : Lis
t α} {f : β -> α} {g : β -> List α} {b : Filter β} (hf : Tendsto f b (𝓝 a)) (hg 
: Tendsto g …
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `continuousAt_subtype_val`：continuousAt_subtype_val {p : X -> Prop} {x : 
Subtype p} : ContinuousAt ((↑) : Subtype p -> X) x
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
-/
theorem tendsto_insertIdx {n : ℕ} {i : Fin (n + 1)} {a : α} :
    ∀ {l : Vector α n},
      Tendsto (fun p : α × Vector α n => insertIdx p.1 i p.2) (𝓝 a ×ˢ 𝓝 l)
        (𝓝 (insertIdx a i l))
  | ⟨l, hl⟩ => by
    rw [insertIdx, tendsto_subtype_rng]
    simp only [insertIdx_val]
    exact List.tendsto_insertIdx tendsto_fst (Tendsto.comp continuousAt_subtype_val tendsto_snd : _)

/-- Continuity of `Vector.insertIdx`. -/
/-
**List.Vector.continuous_insertIdx'** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：continuous_insertIdx' {n : Nat} {i : Fin (n + 1)} : Continuous fun p : α ×
 Vector α n => Vector.insertIdx p.1 i p.2
参数：n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `List.Vector.tendsto_insertIdx`：∀ {α : Type u_1} [inst : TopologicalSpace
 α] {n : ℕ} {i : Fin (n + 1)} {a : α} {l : List.Vector α n},   Filter.Tendsto (f
un p => List.Vector…

--- 原说明 ---
Continuity of `Vector.insertIdx`.
-/
theorem continuous_insertIdx' {n : ℕ} {i : Fin (n + 1)} :
    Continuous fun p : α × Vector α n => Vector.insertIdx p.1 i p.2 :=
  continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt, nhds_prod_eq]; exact tendsto_insertIdx
/-
**List.Vector.continuous_insertIdx** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：continuous_insertIdx {n : Nat} {i : Fin (n + 1)} {f : β -> α} {g : β -> Ve
ctor α n} (hf : Continuous f) (hg : Continuous g) : Continuous fun b => Vector.i
nsertIdx (f b) i (g b)
参数：n + 1；hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `List.Vector.continuous_insertIdx'`：continuous_insertIdx' {n : Nat} {i : 
Fin (n + 1)} : Continuous fun p : α × Vector α n => Vector.insertIdx p.1 i p.2
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
-/
theorem continuous_insertIdx {n : ℕ} {i : Fin (n + 1)} {f : β → α} {g : β → Vector α n}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun b => Vector.insertIdx (f b) i (g b) :=
  continuous_insertIdx'.comp (hf.prodMk hg)

set_option backward.isDefEq.respectTransparency false in
/-
**List.Vector.continuousAt_eraseIdx** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {n : ℕ} {i : Fin (n + 1)} {l 
: List.Vector α (n + 1)},   ContinuousAt (List.Vector.eraseIdx i) l
参数：n + 1；n + 1；List.Vector.eraseIdx i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `List.Vector.eraseIdx.eq_1`：∀ {α : Type u_1} {n : ℕ} (i : Fin n) (l : Lis
t α) (h : l.length = n), List.Vector.eraseIdx i ⟨l, h⟩ = ⟨l.eraseIdx ↑i, ⋯⟩
· 使用定理 `tendsto_subtype_rng`：∀ {X : Type u} [inst : TopologicalSpace X] {Y : Typ
e u_5} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p}   {x : Subtype p}, Filt
er.Tendst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.Vector.eraseIdx_val`：∀ {α : Type u_1} {n : ℕ} {i : Fin n} {v : List
.Vector α n}, ↑(List.Vector.eraseIdx i v) = (↑v).eraseIdx ↑i
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `List.tendsto_eraseIdx`：∀ {α : Type u_1} [inst : TopologicalSpace α] {n :
 ℕ} {l : List α},   Filter.Tendsto (fun x => x.eraseIdx n) (nhds l) (nhds (l.era
seIdx n))
· 使用定理 `continuousAt_subtype_val`：continuousAt_subtype_val {p : X -> Prop} {x : 
Subtype p} : ContinuousAt ((↑) : Subtype p -> X) x
-/
theorem continuousAt_eraseIdx {n : ℕ} {i : Fin (n + 1)} :
    ∀ {l : Vector α (n + 1)}, ContinuousAt (Vector.eraseIdx i) l
  | ⟨l, hl⟩ => by
    rw [ContinuousAt, Vector.eraseIdx, tendsto_subtype_rng]
    simp only [Vector.eraseIdx_val]
    exact Tendsto.comp List.tendsto_eraseIdx continuousAt_subtype_val
/-
**List.Vector.continuous_eraseIdx** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：continuous_eraseIdx {n : Nat} {i : Fin (n + 1)} : Continuous (Vector.erase
Idx i : Vector α (n + 1) -> Vector α n)
参数：n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `List.Vector.continuousAt_eraseIdx`：∀ {α : Type u_1} [inst : TopologicalS
pace α] {n : ℕ} {i : Fin (n + 1)} {l : List.Vector α (n + 1)},   ContinuousAt (L
ist.Vector.eraseIdx i) …
-/
theorem continuous_eraseIdx {n : ℕ} {i : Fin (n + 1)} :
    Continuous (Vector.eraseIdx i : Vector α (n + 1) → Vector α n) :=
  continuous_iff_continuousAt.mpr fun ⟨_a, _l⟩ => continuousAt_eraseIdx

end List.Vector

