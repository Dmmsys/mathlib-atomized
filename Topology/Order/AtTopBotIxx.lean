/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.SuccPred.Limit
import Mathlib.Topology.Order.LeftRightNhds

/-!
# `Filter.atTop` and `Filter.atBot` for intervals in a linear order topology

Let `X` be a linear order with order topology.
Let `a` be a point that is either the bottom element of `X` or is not isolated on the left,
see `Order.IsSuccPrelimit`.
Then the `Filter.atTop` filter on `Set.Iio a` and `𝓝[<] a` are related by the coercion map
via pushforward and pullback, see `map_coe_Iio_atTop` and `comap_coe_Iio_nhdsLT`.

We prove several versions of this statement for `Set.Iio`, `Set.Ioi`, and `Set.Ioo`,
as well as `Filter.atTop` and `Filter.atBot`.

The assumption on `a` is automatically satisfied for densely ordered types,
see `Order.IsSuccPrelimit.of_dense`.
-/

public section

open Set Filter Order OrderDual
open scoped Topology

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
  {s : Set X} {a b : X}

/-
**comap_coe_nhdsLT_eq_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_coe_nhdsLT_eq_atTop_iff : comap ((↑) : s -> X) (𝓝[<] b) = atTop ↔ s 
subseteq Iio b ∧ (s.Nonempty -> forall a < b, (s inter Ioo a b).Nonempty)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Filter.HasBasis.ext`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l 
l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set 
α},   l.H…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `nhdsLT_basis_of_exists_lt`：nhdsLT_basis_of_exists_lt {a : α} (h : exists
 b, b < a) : (𝓝[<] a).HasBasis (· < a) (Ioo · a)
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
（共 46 条，此处仅展示前 30 条）
-/
theorem comap_coe_nhdsLT_eq_atTop_iff :
    comap ((↑) : s → X) (𝓝[<] b) = atTop ↔
      s ⊆ Iio b ∧ (s.Nonempty → ∀ a < b, (s ∩ Ioo a b).Nonempty) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp [eq_iff_true_of_subsingleton]
  have := hsne.to_subtype
  simp only [hsne, true_imp_iff]
  by_cases hsub : s ⊆ Iio b
  · simp only [hsub, true_and]
    constructor
    · intro h a ha
      have := preimage_mem_comap (m := ((↑) : s → X)) (Ioo_mem_nhdsLT ha)
      rw [h] at this
      rcases Filter.nonempty_of_mem this with ⟨⟨c, hcs⟩, hc⟩
      exact ⟨c, hcs, hc⟩
    · intro h
      refine (nhdsLT_basis_of_exists_lt (hsne.mono hsub)).comap _ |>.ext atTop_basis ?_ ?_
      · intro a hab
        rcases h a hab with ⟨c, hcs, hc⟩
        use ⟨c, hcs⟩
        simp_all [subset_def, hc.1.trans_le]
      · rintro ⟨a, has⟩ -
        use a, hsub has
        simp_all [subset_def, le_of_lt]
  · suffices ¬Tendsto (↑) (atTop : Filter s) (𝓝[<] b) by
      contrapose this
      simp_all [tendsto_iff_comap]
    intro h
    rcases not_subset_iff_exists_mem_notMem.mp hsub with ⟨a, has, ha⟩
    rcases h.eventually eventually_mem_nhdsWithin |>.and (eventually_ge_atTop ⟨a, has⟩) |>.exists
      with ⟨⟨c, hcs⟩, hcb, hac⟩
    apply lt_irrefl a
    calc
      a ≤ c := by simpa using hac
      _ < b := by simpa using hcb
      _ ≤ a := by simpa using ha
/-
**comap_coe_nhdsGT_eq_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_coe_nhdsGT_eq_atBot_iff : comap ((↑) : s -> X) (𝓝[>] b) = atBot ↔ s 
subseteq Ioi b ∧ (s.Nonempty -> forall a > b, (s inter Ioo b a).Nonempty)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `comap_coe_nhdsLT_eq_atTop_iff`：comap_coe_nhdsLT_eq_atTop_iff : comap ((↑
) : s -> X) (𝓝[<] b) = atTop ↔ s subseteq Iio b ∧ (s.Nonempty -> forall a < b, (
s inter Ioo a b).No…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.Ioo_toDual`：Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo 
b a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_coe_nhdsGT_eq_atBot_iff :
    comap ((↑) : s → X) (𝓝[>] b) = atBot ↔
      s ⊆ Ioi b ∧ (s.Nonempty → ∀ a > b, (s ∩ Ioo b a).Nonempty) := by
  refine comap_coe_nhdsLT_eq_atTop_iff (s := OrderDual.ofDual ⁻¹' s) (b := OrderDual.toDual b)
    |>.trans ?_
  simp [← preimage_inter, ofDual.surjective]
/-
**comap_coe_nhdsLT_of_Ioo_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_coe_nhdsLT_of_Ioo_subset (hsb : s subseteq Iio b) (hs : s.Nonempty -
> exists a < b, Ioo a b subseteq s) (hb : IsSuccPrelimit b
参数：hsb : s subseteq Iio b；hs : s.Nonempty -> exists a < b, Ioo a b subseteq s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `comap_coe_nhdsLT_eq_atTop_iff`：comap_coe_nhdsLT_eq_atTop_iff : comap ((↑
) : s -> X) (𝓝[<] b) = atTop ↔ s subseteq Iio b ∧ (s.Nonempty -> forall a < b, (
s inter Ioo a b).No…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.IsSuccPrelimit.lt_iff_exists_lt`：∀ {α : Type u_1} {a b : α} [inst 
: LinearOrder α], Order.IsSuccPrelimit b → (a < b ↔ ∃ c < b, a < c)
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem comap_coe_nhdsLT_of_Ioo_subset (hsb : s ⊆ Iio b) (hs : s.Nonempty → ∃ a < b, Ioo a b ⊆ s)
    (hb : IsSuccPrelimit b := by exact .of_dense _) :
    comap ((↑) : s → X) (𝓝[<] b) = atTop := by
  rw [comap_coe_nhdsLT_eq_atTop_iff]
  refine ⟨hsb, fun hsne a ha ↦ ?_⟩
  rcases hs hsne with ⟨c, hcb, hcs⟩
  rcases hb.lt_iff_exists_lt.mp (max_lt ha hcb) with ⟨x, hxb, hacx⟩
  rw [max_lt_iff] at hacx
  exact ⟨x, hcs ⟨hacx.2, hxb⟩, hacx.1, hxb⟩
/-
**comap_coe_nhdsGT_of_Ioo_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_coe_nhdsGT_of_Ioo_subset (hsa : s subseteq Ioi a) (hs : s.Nonempty -
> exists b > a, Ioo a b subseteq s) (ha : IsPredPrelimit a
参数：hsa : s subseteq Ioi a；hs : s.Nonempty -> exists b > a, Ioo a b subseteq s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comap_coe_nhdsLT_of_Ioo_subset`：comap_coe_nhdsLT_of_Ioo_subset (hsb : s 
subseteq Iio b) (hs : s.Nonempty -> exists a < b, Ioo a b subseteq s) (hb : IsSu
ccPrelimit b
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ioo_toDual`：Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo 
b a
· 使用定理 `Order.IsPredPrelimit.dual`：∀ {α : Type u_1} {a : α} [inst : LT α], Order
.IsPredPrelimit a → Order.IsSuccPrelimit (OrderDual.toDual a)
-/
theorem comap_coe_nhdsGT_of_Ioo_subset (hsa : s ⊆ Ioi a) (hs : s.Nonempty → ∃ b > a, Ioo a b ⊆ s)
    (ha : IsPredPrelimit a := by exact .of_dense _) :
    comap ((↑) : s → X) (𝓝[>] a) = atBot := by
  refine comap_coe_nhdsLT_of_Ioo_subset (show ofDual ⁻¹' s ⊆ Iio (toDual a) from hsa) ?_ ha.dual
  simpa only [OrderDual.exists, Ioo_toDual]
/-
**map_coe_atTop_of_Ioo_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_coe_atTop_of_Ioo_subset (hsb : s subseteq Iio b) (hs : forall a' < b, 
exists a < b, Ioo a b subseteq s) (hb : IsSuccPrelimit b
参数：hsb : s subseteq Iio b；hs : forall a' < b, exists a < b, Ioo a b subseteq s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.filter_eq_bot_of_isEmpty`：filter_eq_bot_of_isEmpty [IsEmpty α] (f
 : Filter α) : f = ⊥
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
· 使用定理 `nhdsWithin_empty`：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_coe_nhdsLT_of_Ioo_subset`：comap_coe_nhdsLT_of_Ioo_subset (hsb : s 
subseteq Iio b) (hs : s.Nonempty -> exists a < b, Ioo a b subseteq s) (hb : IsSu
ccPrelimit b
· 使用定理 `Filter.map_comap_of_mem`：map_comap_of_mem {f : Filter β} {m : α -> β} (h
f : range m in f) : (f.comap m).map m = f
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhdsLT_iff_exists_Ioo_subset'`：mem_nhdsLT_iff_exists_Ioo_subset' {a 
l' : α} {s : Set α} (hl' : l' < a) : s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a su
bseteq s
-/
theorem map_coe_atTop_of_Ioo_subset (hsb : s ⊆ Iio b) (hs : ∀ a' < b, ∃ a < b, Ioo a b ⊆ s)
    (hb : IsSuccPrelimit b := by exact .of_dense _) :
    map ((↑) : s → X) atTop = 𝓝[<] b := by
  rcases eq_empty_or_nonempty (Iio b) with (hb' | ⟨a, ha⟩)
  · have : IsEmpty s := ⟨fun x => hb'.subset (hsb x.2)⟩
    rw [filter_eq_bot_of_isEmpty atTop, Filter.map_bot, hb', nhdsWithin_empty]
  · rw [← comap_coe_nhdsLT_of_Ioo_subset hsb (fun _ => hs a ha) hb, map_comap_of_mem]
    rw [Subtype.range_val]
    exact (mem_nhdsLT_iff_exists_Ioo_subset' ha).2 (hs a ha)
/-
**map_coe_atBot_of_Ioo_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_coe_atBot_of_Ioo_subset (hsa : s subseteq Ioi a) (hs : forall b' > a, 
exists b > a, Ioo a b subseteq s) (ha : IsPredPrelimit a
参数：hsa : s subseteq Ioi a；hs : forall b' > a, exists b > a, Ioo a b subseteq s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_coe_atTop_of_Ioo_subset`：map_coe_atTop_of_Ioo_subset (hsb : s subset
eq Iio b) (hs : forall a' < b, exists a < b, Ioo a b subseteq s) (hb : IsSuccPre
limit b
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ioo_toDual`：Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo 
b a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `Order.IsPredPrelimit.dual`：∀ {α : Type u_1} {a : α} [inst : LT α], Order
.IsPredPrelimit a → Order.IsSuccPrelimit (OrderDual.toDual a)
-/
theorem map_coe_atBot_of_Ioo_subset (hsa : s ⊆ Ioi a) (hs : ∀ b' > a, ∃ b > a, Ioo a b ⊆ s)
    (ha : IsPredPrelimit a := by exact .of_dense _) :
    map ((↑) : s → X) atBot = 𝓝[>] a := by
  refine map_coe_atTop_of_Ioo_subset (s := ofDual ⁻¹' s) (b := toDual a) hsa ?_ ha.dual
  intro b' hb'
  simpa [OrderDual.exists] using hs (ofDual b') hb'

/-- The `atTop` filter for an open interval `Ioo a b` comes from the left-neighbourhoods filter at
the right endpoint in the ambient order. -/
@[simp]
/-
**comap_coe_Ioo_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_coe_Ioo_nhdsLT (a b : X) (hb : IsSuccPrelimit b
参数：a b : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comap_coe_nhdsLT_of_Ioo_subset`：comap_coe_nhdsLT_of_Ioo_subset (hsb : s 
subseteq Iio b) (hs : s.Nonempty -> exists a < b, Ioo a b subseteq s) (hb : IsSu
ccPrelimit b
· 使用定理 `Set.Ioo_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Iio b
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
The `atTop` filter for an open interval `Ioo a b` comes from the left-neighbourh
oods filter at
the right endpoint in the ambient order.
-/
theorem comap_coe_Ioo_nhdsLT (a b : X) (hb : IsSuccPrelimit b := by exact .of_dense _) :
    comap ((↑) : Ioo a b → X) (𝓝[<] b) = atTop :=
  comap_coe_nhdsLT_of_Ioo_subset Ioo_subset_Iio_self
    (fun h => ⟨a, h.elim fun _x hx ↦ hx.1.trans hx.2, Subset.rfl⟩) hb

/-- The `atBot` filter for an open interval `Ioo a b` comes from the right-neighbourhoods filter at
the left endpoint in the ambient order. -/
@[simp]
/-
**comap_coe_Ioo_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_coe_Ioo_nhdsGT (a b : X) (ha : IsPredPrelimit a
参数：a b : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comap_coe_nhdsGT_of_Ioo_subset`：comap_coe_nhdsGT_of_Ioo_subset (hsa : s 
subseteq Ioi a) (hs : s.Nonempty -> exists b > a, Ioo a b subseteq s) (ha : IsPr
edPrelimit a
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
The `atBot` filter for an open interval `Ioo a b` comes from the right-neighbour
hoods filter at
the left endpoint in the ambient order.
-/
theorem comap_coe_Ioo_nhdsGT (a b : X) (ha : IsPredPrelimit a := by exact .of_dense _) :
    comap ((↑) : Ioo a b → X) (𝓝[>] a) = atBot :=
  comap_coe_nhdsGT_of_Ioo_subset Ioo_subset_Ioi_self
    (fun h => ⟨b, h.elim fun _x hx ↦ hx.1.trans hx.2, Subset.rfl⟩) ha

@[simp]
/-
**comap_coe_Ioi_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_coe_Ioi_nhdsGT (a : X) (ha : IsPredPrelimit a
参数：a : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comap_coe_nhdsGT_of_Ioo_subset`：comap_coe_nhdsGT_of_Ioo_subset (hsa : s 
subseteq Ioi a) (hs : s.Nonempty -> exists b > a, Ioo a b subseteq s) (ha : IsPr
edPrelimit a
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
-/
theorem comap_coe_Ioi_nhdsGT (a : X) (ha : IsPredPrelimit a := by exact .of_dense _) :
    comap ((↑) : Ioi a → X) (𝓝[>] a) = atBot :=
  comap_coe_nhdsGT_of_Ioo_subset Subset.rfl (fun ⟨x, hx⟩ => ⟨x, hx, Ioo_subset_Ioi_self⟩) ha

@[simp]
/-
**comap_coe_Iio_nhdsLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_coe_Iio_nhdsLT (a : X) (ha : IsSuccPrelimit a
参数：a : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comap_coe_Ioi_nhdsGT`：comap_coe_Ioi_nhdsGT (a : X) (ha : IsPredPrelimit 
a
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Order.IsSuccPrelimit.dual`：∀ {α : Type u_1} {a : α} [inst : LT α], Order
.IsSuccPrelimit a → Order.IsPredPrelimit (OrderDual.toDual a)
-/
theorem comap_coe_Iio_nhdsLT (a : X) (ha : IsSuccPrelimit a := by exact .of_dense _) :
    comap ((↑) : Iio a → X) (𝓝[<] a) = atTop :=
  comap_coe_Ioi_nhdsGT (toDual a) ha.dual

@[simp]
/-
**map_coe_Ioo_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_coe_Ioo_atTop (h : a < b) (hb : IsSuccPrelimit b
参数：h : a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_coe_atTop_of_Ioo_subset`：map_coe_atTop_of_Ioo_subset (hsb : s subset
eq Iio b) (hs : forall a' < b, exists a < b, Ioo a b subseteq s) (hb : IsSuccPre
limit b
· 使用定理 `Set.Ioo_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Iio b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem map_coe_Ioo_atTop (h : a < b) (hb : IsSuccPrelimit b := by exact .of_dense _) :
    map ((↑) : Ioo a b → X) atTop = 𝓝[<] b :=
  map_coe_atTop_of_Ioo_subset Ioo_subset_Iio_self (fun _ _ => ⟨_, h, Subset.rfl⟩) hb

@[simp]
/-
**map_coe_Ioo_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_coe_Ioo_atBot (h : a < b) (ha : IsPredPrelimit a
参数：h : a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_coe_atBot_of_Ioo_subset`：map_coe_atBot_of_Ioo_subset (hsa : s subset
eq Ioi a) (hs : forall b' > a, exists b > a, Ioo a b subseteq s) (ha : IsPredPre
limit a
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem map_coe_Ioo_atBot (h : a < b) (ha : IsPredPrelimit a := by exact .of_dense _) :
    map ((↑) : Ioo a b → X) atBot = 𝓝[>] a :=
  map_coe_atBot_of_Ioo_subset Ioo_subset_Ioi_self (fun _ _ => ⟨_, h, Subset.rfl⟩) ha

@[simp]
/-
**map_coe_Ioi_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_coe_Ioi_atBot (a : X) (ha : IsPredPrelimit a
参数：a : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_coe_atBot_of_Ioo_subset`：map_coe_atBot_of_Ioo_subset (hsa : s subset
eq Ioi a) (hs : forall b' > a, exists b > a, Ioo a b subseteq s) (ha : IsPredPre
limit a
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
-/
theorem map_coe_Ioi_atBot (a : X) (ha : IsPredPrelimit a := by exact .of_dense _) :
    map ((↑) : Ioi a → X) atBot = 𝓝[>] a :=
  map_coe_atBot_of_Ioo_subset Subset.rfl (fun b hb => ⟨b, hb, Ioo_subset_Ioi_self⟩) ha

@[simp]
/-
**map_coe_Iio_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_coe_Iio_atTop (a : X) (ha : IsSuccPrelimit a
参数：a : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_coe_Ioi_atBot`：map_coe_Ioi_atBot (a : X) (ha : IsPredPrelimit a
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Order.IsSuccPrelimit.dual`：∀ {α : Type u_1} {a : α} [inst : LT α], Order
.IsSuccPrelimit a → Order.IsPredPrelimit (OrderDual.toDual a)
-/
theorem map_coe_Iio_atTop (a : X) (ha : IsSuccPrelimit a := by exact .of_dense _) :
    map ((↑) : Iio a → X) atTop = 𝓝[<] a :=
  map_coe_Ioi_atBot (toDual a) ha.dual

variable {α : Type*} {l : Filter α} {f : X → α}

@[simp]
/-
**tendsto_comp_coe_Ioo_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_comp_coe_Ioo_atTop (h : a < b) (hb : IsSuccPrelimit b
参数：h : a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_coe_Ioo_atTop`：map_coe_Ioo_atTop (h : a < b) (hb : IsSuccPrelimit b
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_comp_coe_Ioo_atTop (h : a < b) (hb : IsSuccPrelimit b := by exact .of_dense _) :
    Tendsto (fun x : Ioo a b => f x) atTop l ↔ Tendsto f (𝓝[<] b) l := by
  rw [← map_coe_Ioo_atTop h hb, tendsto_map'_iff, Function.comp_def]

@[simp]
/-
**tendsto_comp_coe_Ioo_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_comp_coe_Ioo_atBot (h : a < b) (ha : IsPredPrelimit a
参数：h : a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_coe_Ioo_atBot`：map_coe_Ioo_atBot (h : a < b) (ha : IsPredPrelimit a
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_comp_coe_Ioo_atBot (h : a < b) (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto (fun x : Ioo a b => f x) atBot l ↔ Tendsto f (𝓝[>] a) l := by
  rw [← map_coe_Ioo_atBot h ha, tendsto_map'_iff, Function.comp_def]

@[simp]
/-
**tendsto_comp_coe_Ioi_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_comp_coe_Ioi_atBot (ha : IsPredPrelimit a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_coe_Ioi_atBot`：map_coe_Ioi_atBot (a : X) (ha : IsPredPrelimit a
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_comp_coe_Ioi_atBot (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto (fun x : Ioi a => f x) atBot l ↔ Tendsto f (𝓝[>] a) l := by
  rw [← map_coe_Ioi_atBot a ha, tendsto_map'_iff, Function.comp_def]

@[simp]
/-
**tendsto_comp_coe_Iio_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_comp_coe_Iio_atTop (ha : IsSuccPrelimit a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_coe_Iio_atTop`：map_coe_Iio_atTop (a : X) (ha : IsSuccPrelimit a
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_comp_coe_Iio_atTop (ha : IsSuccPrelimit a := by exact .of_dense _) :
    Tendsto (fun x : Iio a => f x) atTop l ↔ Tendsto f (𝓝[<] a) l := by
  rw [← map_coe_Iio_atTop a ha, tendsto_map'_iff, Function.comp_def]

@[simp]
/-
**tendsto_Ioo_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_Ioo_atTop {f : α -> Ioo a b} (hb : IsSuccPrelimit b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_coe_Ioo_nhdsLT`：comap_coe_Ioo_nhdsLT (a b : X) (hb : IsSuccPrelimi
t b
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_Ioo_atTop {f : α → Ioo a b} (hb : IsSuccPrelimit b := by exact .of_dense _) :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : X)) l (𝓝[<] b) := by
  rw [← comap_coe_Ioo_nhdsLT a b hb, tendsto_comap_iff, Function.comp_def]

@[simp]
/-
**tendsto_Ioo_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_Ioo_atBot {f : α -> Ioo a b} (ha : IsPredPrelimit a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_coe_Ioo_nhdsGT`：comap_coe_Ioo_nhdsGT (a b : X) (ha : IsPredPrelimi
t a
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_Ioo_atBot {f : α → Ioo a b} (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : X)) l (𝓝[>] a) := by
  rw [← comap_coe_Ioo_nhdsGT a b ha, tendsto_comap_iff, Function.comp_def]

@[simp]
/-
**tendsto_Ioi_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_Ioi_atBot {f : α -> Ioi a} (ha : IsPredPrelimit a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_coe_Ioi_nhdsGT`：comap_coe_Ioi_nhdsGT (a : X) (ha : IsPredPrelimit 
a
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_Ioi_atBot {f : α → Ioi a} (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : X)) l (𝓝[>] a) := by
  rw [← comap_coe_Ioi_nhdsGT a ha, tendsto_comap_iff, Function.comp_def]

@[simp]
/-
**tendsto_Iio_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_Iio_atTop {f : α -> Iio a} (ha : IsSuccPrelimit a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_coe_Iio_nhdsLT`：comap_coe_Iio_nhdsLT (a : X) (ha : IsSuccPrelimit 
a
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_Iio_atTop {f : α → Iio a} (ha : IsSuccPrelimit a := by exact .of_dense _) :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : X)) l (𝓝[<] a) := by
  rw [← comap_coe_Iio_nhdsLT a ha, tendsto_comap_iff, Function.comp_def]

section LocallyFinite
variable [LinearOrder α] [LocallyFiniteOrder α] [NoMaxOrder X] [NoMinOrder X]

/-- A family of closed intervals bounded by diverging limits is locally finite. -/
/-
**locallyFinite_Icc_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyFinite_Icc_of_tendsto {f g : α -> X} (hl : Tendsto f atTop atTop) (
hu : Tendsto g atBot atBot) : LocallyFinite (fun n => Set.Icc (f n) (g n))
参数：hl : Tendsto f atTop atTop；hu : Tendsto g atBot atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Filter.Eventually.exists_forall_of_atBot`：∀ {α : Type u_3} [inst : Preor
der α] [IsCodirectedOrder α] {p : α → Prop} [Nonempty α],   (∀ᶠ (x : α) in Filte
r.atBot, p x) → ∃ a, ∀ b ≤ a, …
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Filter.Tendsto.eventually_le_atBot`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atBot → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `Filter.Eventually.exists_forall_of_atTop`：∀ {α : Type u_3} [inst : Preor
der α] [IsDirectedOrder α] {p : α → Prop} [Nonempty α],   (∀ᶠ (x : α) in Filter.
atTop, p x) → ∃ a, ∀ (b : α), …
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Set.finite_Icc`：finite_Icc : (Icc a b).Finite
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A family of closed intervals bounded by diverging limits is locally finite.
-/
theorem locallyFinite_Icc_of_tendsto {f g : α → X}
    (hl : Tendsto f atTop atTop) (hu : Tendsto g atBot atBot) :
    LocallyFinite (fun n => Set.Icc (f n) (g n)) := by
  intro x
  cases isEmpty_or_nonempty α
  · use univ
    simp [Subsingleton.elim _ (∅ : Set α)]
  obtain ⟨x_L, hx_L⟩ := exists_lt x
  obtain ⟨x_R, hx_R⟩ := exists_gt x
  obtain ⟨a_L, ha_L : ∀ a ≤ a_L, g a ≤ x_L⟩ :=
    hu.eventually_le_atBot x_L |>.exists_forall_of_atBot
  obtain ⟨a_R, ha_R : ∀ a ≥ a_R, x_R ≤ f a⟩ :=
    hl.eventually_ge_atTop x_R |>.exists_forall_of_atTop
  refine ⟨Ioo x_L x_R, Ioo_mem_nhds hx_L hx_R, (finite_Icc a_L a_R).subset ?_⟩
  rintro n ⟨y, ⟨hf, hg⟩, ⟨hxL, hxR⟩⟩
  constructor
  · contrapose! hxL
    exact hg.trans (ha_L n hxL.le)
  · contrapose! hxR
    exact (ha_R n hxR.le).trans hf

/-- A family of half-open intervals bounded by diverging limits is locally finite. -/
/-
**locallyFinite_Ico_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyFinite_Ico_of_tendsto {l u : α -> X} (hl : Tendsto l atTop atTop) (
hu : Tendsto u atBot atBot) : LocallyFinite (fun n => Set.Ico (l n) (u n))
参数：hl : Tendsto l atTop atTop；hu : Tendsto u atBot atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `locallyFinite_Icc_of_tendsto`：locallyFinite_Icc_of_tendsto {f g : α -> X
} (hl : Tendsto f atTop atTop) (hu : Tendsto g atBot atBot) : LocallyFinite (fun
 n => Set.Icc (f n…
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a

--- 原说明 ---
A family of half-open intervals bounded by diverging limits is locally finite.
-/
theorem locallyFinite_Ico_of_tendsto {l u : α → X}
    (hl : Tendsto l atTop atTop) (hu : Tendsto u atBot atBot) :
    LocallyFinite (fun n => Set.Ico (l n) (u n)) :=
  locallyFinite_Icc_of_tendsto hl hu |>.subset fun _ => Set.Ico_subset_Icc_self

/-- A family of half-open intervals bounded by diverging limits is locally finite. -/
/-
**locallyFinite_Ioc_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyFinite_Ioc_of_tendsto {l u : α -> X} (hl : Tendsto l atTop atTop) (
hu : Tendsto u atBot atBot) : LocallyFinite (fun n => Set.Ioc (l n) (u n))
参数：hl : Tendsto l atTop atTop；hu : Tendsto u atBot atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `locallyFinite_Icc_of_tendsto`：locallyFinite_Icc_of_tendsto {f g : α -> X
} (hl : Tendsto f atTop atTop) (hu : Tendsto g atBot atBot) : LocallyFinite (fun
 n => Set.Icc (f n…
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b

--- 原说明 ---
A family of half-open intervals bounded by diverging limits is locally finite.
-/
theorem locallyFinite_Ioc_of_tendsto {l u : α → X}
    (hl : Tendsto l atTop atTop) (hu : Tendsto u atBot atBot) :
    LocallyFinite (fun n => Set.Ioc (l n) (u n)) :=
  locallyFinite_Icc_of_tendsto hl hu |>.subset fun _ => Set.Ioc_subset_Icc_self

/-- A family of open intervals bounded by diverging limits is locally finite. -/
/-
**locallyFinite_Ioo_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyFinite_Ioo_of_tendsto {l u : α -> X} (hl : Tendsto l atTop atTop) (
hu : Tendsto u atBot atBot) : LocallyFinite (fun n => Set.Ioo (l n) (u n))
参数：hl : Tendsto l atTop atTop；hu : Tendsto u atBot atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `locallyFinite_Icc_of_tendsto`：locallyFinite_Icc_of_tendsto {f g : α -> X
} (hl : Tendsto f atTop atTop) (hu : Tendsto g atBot atBot) : LocallyFinite (fun
 n => Set.Icc (f n…
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b

--- 原说明 ---
A family of open intervals bounded by diverging limits is locally finite.
-/
theorem locallyFinite_Ioo_of_tendsto {l u : α → X}
    (hl : Tendsto l atTop atTop) (hu : Tendsto u atBot atBot) :
    LocallyFinite (fun n => Set.Ioo (l n) (u n)) :=
  locallyFinite_Icc_of_tendsto hl hu |>.subset fun _ => Set.Ioo_subset_Icc_self

end LocallyFinite

