/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.Star

/-!
# Topological sums and functorial constructions

Lemmas on the interaction of `tprod`, `tsum`, `HasProd`, `HasSum` etc. with products, Sigma and Pi
types, `MulOpposite`, etc.

-/

public section

noncomputable section

open Filter Finset Function

open scoped Topology

variable {α β γ : Type*} {L : SummationFilter β}


/-! ## Product, Sigma and Pi types -/

section ProdDomain

variable [CommMonoid α] [TopologicalSpace α]

@[to_additive]
/-
**hasProd_pi_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_pi_single [DecidableEq β] (b : β) (a : α) : HasProd (Pi.mulSingle 
b a) a
参数：b : β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mulSingle_apply`：mulSingle_apply (i : ι) (x : M) (i' : ι) : (mulSingl
e i x : ι -> M) i' = if i' = i then x else 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `hasProd_ite_eq`：hasProd_ite_eq (b : β) [DecidablePred (· = b)] (a : α) (
L
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
theorem hasProd_pi_single [DecidableEq β] (b : β) (a : α) : HasProd (Pi.mulSingle b a) a := by
  convert! hasProd_ite_eq (L := .unconditional β) b a
  simp [Pi.mulSingle_apply]

@[to_additive (attr := simp)]
/-
**tprod_pi_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_pi_single [DecidableEq β] (b : β) (a : α) : ∏' b', Pi.mulSingle b a 
b' = a
参数：b : β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_eq_mulSingle`：tprod_eq_mulSingle [L.LeAtTop] {f : β -> α} (b : β) 
(hf : forall b' != b, f b' = 1) : ∏'[L] b, f b = f b
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
-/
theorem tprod_pi_single [DecidableEq β] (b : β) (a : α) : ∏' b', Pi.mulSingle b a b' = a := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive tsum_setProd_singleton_left]
/-
**tprod_setProd_singleton_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_setProd_singleton_left (b : β) (t : Set γ) (f : β × γ -> α) : (∏' x 
: {b} ×ˢ t, f x) = ∏' c : t, f (b, c)
参数：b : β；t : Set γ；f : β × γ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_congr_set_coe`：tprod_congr_set_coe (f : β -> α) {s t : Set β} (h :
 s = t) : ∏' x : s, f x = ∏' x : t, f x
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
· 使用定理 `tprod_image`：tprod_image {g : γ -> β} (f : β -> α) {s : Set γ} (hg : Set
.InjOn g s) : ∏' x : g '' s, f x = ∏' x : s, f (g x)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
-/
lemma tprod_setProd_singleton_left (b : β) (t : Set γ) (f : β × γ → α) :
    (∏' x : {b} ×ˢ t, f x) = ∏' c : t, f (b, c) := by
  rw [tprod_congr_set_coe _ Set.singleton_prod, tprod_image _ (Prod.mk_right_injective b).injOn]

@[to_additive tsum_setProd_singleton_right]
/-
**tprod_setProd_singleton_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_setProd_singleton_right (s : Set β) (c : γ) (f : β × γ -> α) : (∏' x
 : s ×ˢ {c}, f x) = ∏' b : s, f (b, c)
参数：s : Set β；c : γ；f : β × γ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_congr_set_coe`：tprod_congr_set_coe (f : β -> α) {s t : Set β} (h :
 s = t) : ∏' x : s, f x = ∏' x : t, f x
· 使用定理 `Set.prod_singleton`：prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, 
b)) '' s
· 使用定理 `tprod_image`：tprod_image {g : γ -> β} (f : β -> α) {s : Set γ} (hg : Set
.InjOn g s) : ∏' x : g '' s, f x = ∏' x : s, f (g x)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Prod.mk_left_injective`：mk_left_injective {α β : Type*} (b : β) : (fun a
 => mk a b : α -> α × β).Injective
-/
lemma tprod_setProd_singleton_right (s : Set β) (c : γ) (f : β × γ → α) :
    (∏' x : s ×ˢ {c}, f x) = ∏' b : s, f (b, c) := by
  rw [tprod_congr_set_coe _ Set.prod_singleton, tprod_image _ (Prod.mk_left_injective c).injOn]

@[to_additive Summable.prod_symm]
/-
**Multipliable.prod_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.prod_symm {f : β × γ -> α} (hf : Multipliable f) : Multipliab
le fun p : γ × β => f p.swap
参数：hf : Multipliable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.multipliable_iff`：Equiv.multipliable_iff (e : γ ≃ β) : Multipliabl
e (f ∘ e) ↔ Multipliable f
-/
theorem Multipliable.prod_symm {f : β × γ → α} (hf : Multipliable f) :
    Multipliable fun p : γ × β ↦ f p.swap :=
  (Equiv.prodComm γ β).multipliable_iff.2 hf

end ProdDomain

section ProdCodomain

variable [CommMonoid α] [TopologicalSpace α] [CommMonoid γ] [TopologicalSpace γ]

@[to_additive HasSum.prodMk]
/-
**HasProd.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.prodMk {f : β -> α} {g : β -> γ} {a : α} {b : γ} (hf : HasProd f a
 L) (hg : HasProd g b L) : HasProd (fun x => (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ L
参数：hf : HasProd f a L；hg : HasProd g b L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem HasProd.prodMk {f : β → α} {g : β → γ} {a : α} {b : γ} (hf : HasProd f a L)
    (hg : HasProd g b L) : HasProd (fun x ↦ (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ L := by
  simp [HasProd, ← prod_mk_prod, Filter.Tendsto.prodMk_nhds hf hg]

end ProdCodomain

section ContinuousMul

variable [CommMonoid α] [TopologicalSpace α] [ContinuousMul α]

section Sum

@[to_additive]
/-
**HasProd.sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProd.sum {α β M : Type*} [CommMonoid M] [TopologicalSpace M] [Continuou
sMul M] {f : α oplus β -> M} {a b : M} (h₁ : HasProd (f ∘ Sum.inl) a) (h₂ : HasP
rod (f ∘ Sum.inr) b) : HasProd f (a * b)
参数：h₁ : HasProd (f ∘ Sum.inl) a；h₂ : HasProd (f ∘ Sum.inr) b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.map_atTop`：map_atTop (e : α ≃o β) : map (e : α -> β) atTop = at
Top
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_disjSum`：prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι o
plus κ -> M) : ∏ x in s.disjSum t, f x = (∏ x in s, f (Sum.inl x)) * ∏ x in t, f
 (Sum.inr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_mul`：tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p
.snd) (𝓝 (a, b)) (𝓝 (a * b))
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
-/
lemma HasProd.sum {α β M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    {f : α ⊕ β → M} {a b : M}
    (h₁ : HasProd (f ∘ Sum.inl) a) (h₂ : HasProd (f ∘ Sum.inr) b) : HasProd f (a * b) := by
  have : Tendsto ((∏ b ∈ ·, f b) ∘ sumEquiv.symm) (atTop.map sumEquiv) (nhds (a * b)) := by
    rw [Finset.sumEquiv.map_atTop, ← prod_atTop_atTop_eq]
    convert! (tendsto_mul.comp (nhds_prod_eq (x := a) (y := b) ▸ Tendsto.prodMap h₁ h₂))
    ext s
    simp
  simpa [Tendsto, ← Filter.map_map] using! this

@[to_additive /-- For the statement that `tsum` commutes with `Finset.sum`,
  see `Summable.tsum_finsetSum`. -/]
/-
**Multipliable.tprod_sum** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {M : Type u_6} [inst : CommMonoid M] [inst
_1 : TopologicalSpace M] [ContinuousMul M]   [T2Space M] {f : α ⊕ β → M},   Mult
ipliable (f ∘ Sum.inl) →     Multipliable (f ∘ Sum.inr) → ∏' (i : α ⊕ β), f i = 
(∏' (i : α), f (Sum.inl i)) * ∏' (i : β), f (Sum.inr i)
参数：f ∘ Sum.inl；f ∘ Sum.inr；i : α ⊕ β；∏' (i : α), f (Sum.inl i)；i : β；Sum.inr i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HasProd.sum`：HasProd.sum {α β M : Type*} [CommMonoid M] [TopologicalSpac
e M] [ContinuousMul M] {f : α oplus β -> M} {a b : M} (h₁ : HasProd (f ∘ Sum.inl
)…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected lemma Multipliable.tprod_sum {α β M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] {f : α ⊕ β → M} (h₁ : Multipliable (f ∘ .inl))
    (h₂ : Multipliable (f ∘ .inr)) : ∏' i, f i = (∏' i, f (.inl i)) * (∏' i, f (.inr i)) :=
  (h₁.hasProd.sum h₂.hasProd).tprod_eq

@[to_additive]
/-
**Multipliable.sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.sum {α β M : Type*} [CommMonoid M] [TopologicalSpace M] [Cont
inuousMul M] (f : α oplus β -> M) (h₁ : Multipliable (f ∘ Sum.inl)) (h₂ : Multip
liable (f ∘ Sum.inr)) : Multipliable f
参数：f : α oplus β -> M；h₁ : Multipliable (f ∘ Sum.inl)；h₂ : Multipliable (f ∘ Sum
.inr)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasProd.sum`：HasProd.sum {α β M : Type*} [CommMonoid M] [TopologicalSpac
e M] [ContinuousMul M] {f : α oplus β -> M} {a b : M} (h₁ : HasProd (f ∘ Sum.inl
)…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma Multipliable.sum {α β M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    (f : α ⊕ β → M) (h₁ : Multipliable (f ∘ Sum.inl)) (h₂ : Multipliable (f ∘ Sum.inr)) :
    Multipliable f :=
  ⟨_, .sum h₁.hasProd h₂.hasProd⟩

end Sum

section RegularSpace

variable [RegularSpace α]

@[to_additive]
/-
**HasProd.sigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} {g : β -> α} {a :
 α} (ha : HasProd f a) (hf : forall b, HasProd (fun c => f ⟨b, c⟩) (g b)) : HasP
rod g a
参数：Σ b : β, γ b；ha : HasProd f a；hf : forall b, HasProd (fun c => f ⟨b, c⟩) (g b
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `closed_nhds_basis`：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsClosed s) id
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `trivial`：True
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_sigma`：prod_sigma {σ : α -> Type*} (s : Finset α) (t : foral
l a, Finset (σ a)) (f : Sigma σ -> β) : ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in
 t a, f…
· 使用定理 `tendsto_finsetProd`：tendsto_finsetProd {f : ι -> α -> M} {x : Filter α} 
{a : ι -> M} (s : Finset ι) : (forall i in s, Tendsto (f i) x (𝓝 (a i))) -> Tend
sto (fun…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_finset_preimage_atTop_atTop`：tendsto_finset_preimage_atTo
p_atTop {f : α -> β} (hf : Function.Injective f) : Tendsto (fun s : Finset β => 
s.preimage f (hf.injOn)) atTop a…
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
theorem HasProd.sigma {γ : β → Type*} {f : (Σ b : β, γ b) → α} {g : β → α} {a : α}
    (ha : HasProd f a) (hf : ∀ b, HasProd (fun c ↦ f ⟨b, c⟩) (g b)) : HasProd g a := by
  classical
  refine (atTop_basis.tendsto_iff (closed_nhds_basis a)).mpr ?_
  rintro s ⟨hs, hsc⟩
  rcases mem_atTop_sets.mp (ha hs) with ⟨u, hu⟩
  use u.image Sigma.fst, trivial
  intro bs hbs
  simp only [Set.mem_preimage] at hu
  have : Tendsto (fun t : Finset (Σ b, γ b) ↦ ∏ p ∈ t with p.1 ∈ bs, f p) atTop
      (𝓝 <| ∏ b ∈ bs, g b) := by
    simp only [← sigma_preimage_mk, prod_sigma]
    refine tendsto_finsetProd _ fun b _ ↦ ?_
    change
      Tendsto (fun t ↦ (fun t ↦ ∏ s ∈ t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) atTop (𝓝 (g b))
    exact (hf b).comp (tendsto_finset_preimage_atTop_atTop (sigma_mk_injective))
  refine hsc.mem_of_tendsto this (eventually_atTop.2 ⟨u, fun t ht ↦ hu _ fun x hx ↦ ?_⟩)
  exact mem_filter.2 ⟨ht hx, hbs <| mem_image_of_mem _ hx⟩

/-- If a function `f` on `β × γ` has product `a` and for each `b` the restriction of `f` to
`{b} × γ` has product `g b`, then the function `g` has product `a`. -/
@[to_additive HasSum.prod_fiberwise /-- If a series `f` on `β × γ` has sum `a` and for each `b` the
restriction of `f` to `{b} × γ` has sum `g b`, then the series `g` has sum `a`. -/]
/-
**HasProd.prod_fiberwise** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.prod_fiberwise {f : β × γ -> α} {g : β -> α} {a : α} (ha : HasProd
 f a) (hf : forall b, HasProd (fun c => f (b, c)) (g b)) : HasProd g a
参数：ha : HasProd f a；hf : forall b, HasProd (fun c => f (b, c)) (g b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.sigma`：HasProd.sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} 
{g : β -> α} {a : α} (ha : HasProd f a) (hf : forall b, HasProd (fun c => f ⟨b, 
c⟩)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.hasProd_iff`：Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ H
asProd f a
-/
theorem HasProd.prod_fiberwise {f : β × γ → α} {g : β → α} {a : α} (ha : HasProd f a)
    (hf : ∀ b, HasProd (fun c ↦ f (b, c)) (g b)) : HasProd g a :=
  HasProd.sigma ((Equiv.sigmaEquivProd β γ).hasProd_iff.2 ha) hf

@[to_additive]
/-
**Multipliable.sigma'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.sigma' {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} (ha : Multi
pliable f) (hf : forall b, Multipliable fun c => f ⟨b, c⟩) : Multipliable fun b 
=> ∏' c, f ⟨b, c⟩
参数：Σ b : β, γ b；ha : Multipliable f；hf : forall b, Multipliable fun c => f ⟨b, c
⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.sigma`：HasProd.sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} 
{g : β -> α} {a : α} (ha : HasProd f a) (hf : forall b, HasProd (fun c => f ⟨b, 
c⟩)…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.sigma' {γ : β → Type*} {f : (Σ b : β, γ b) → α} (ha : Multipliable f)
    (hf : ∀ b, Multipliable fun c ↦ f ⟨b, c⟩) : Multipliable fun b ↦ ∏' c, f ⟨b, c⟩ :=
  (ha.hasProd.sigma fun b ↦ (hf b).hasProd).multipliable

end RegularSpace

section T3Space

variable [T3Space α]

@[to_additive]
/-
**HasProd.sigma_of_hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.sigma_of_hasProd {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} {g : β
 -> α} {a : α} (ha : HasProd g a) (hf : forall b, HasProd (fun c => f ⟨b, c⟩) (g
 b)) (hf' : Multipliable f) : HasProd f a
参数：Σ b : β, γ b；ha : HasProd g a；hf : forall b, HasProd (fun c => f ⟨b, c⟩) (g b
)；hf' : Multipliable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasProd.unique`：HasProd.unique {a₁ a₂ : α} : HasProd f a₁ L -> HasProd f
 a₂ L -> a₁ = a₂
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.sigma`：HasProd.sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} 
{g : β -> α} {a : α} (ha : HasProd f a) (hf : forall b, HasProd (fun c => f ⟨b, 
c⟩)…
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem HasProd.sigma_of_hasProd {γ : β → Type*} {f : (Σ b : β, γ b) → α} {g : β → α}
    {a : α} (ha : HasProd g a) (hf : ∀ b, HasProd (fun c ↦ f ⟨b, c⟩) (g b)) (hf' : Multipliable f) :
    HasProd f a := by simpa [(hf'.hasProd.sigma hf).unique ha] using hf'.hasProd

@[to_additive]
/-
**Multipliable.tprod_sigma'** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [inst_1 : Topologica
lSpace α] [ContinuousMul α] [T3Space α]   {γ : β → Type u_4} {f : (b : β) × γ b 
→ α},   (∀ (b : β), Multipliable fun c => f ⟨b, c⟩) →     Multipliable f → ∏' (p
 : (b : β) × γ b), f p = ∏' (b : β) (c : γ b), f ⟨b, c⟩
参数：b : β；∀ (b : β), Multipliable fun c => f ⟨b, c⟩；p : (b : β) × γ b；b : β；c : γ
 b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.sigma`：HasProd.sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} 
{g : β -> α} {a : α} (ha : HasProd f a) (hf : forall b, HasProd (fun c => f ⟨b, 
c⟩)…
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_sigma' {γ : β → Type*} {f : (Σ b : β, γ b) → α}
    (h₁ : ∀ b, Multipliable fun c ↦ f ⟨b, c⟩) (h₂ : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  (h₂.hasProd.sigma fun b ↦ (h₁ b).hasProd).tprod_eq.symm

@[to_additive Summable.tsum_prod']
/-
**Multipliable.tprod_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommMonoid α] [inst
_1 : TopologicalSpace α] [ContinuousMul α]   [T3Space α] {f : β × γ → α},   Mult
ipliable f → (∀ (b : β), Multipliable fun c => f (b, c)) → ∏' (p : β × γ), f p =
 ∏' (b : β) (c : γ), f (b, c)
参数：∀ (b : β), Multipliable fun c => f (b, c)；p : β × γ；b : β；c : γ；b, c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.prod_fiberwise`：HasProd.prod_fiberwise {f : β × γ -> α} {g : β -
> α} {a : α} (ha : HasProd f a) (hf : forall b, HasProd (fun c => f (b, c)) (g b
)) : HasProd…
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_prod' {f : β × γ → α} (h : Multipliable f)
    (h₁ : ∀ b, Multipliable fun c ↦ f (b, c)) :
    ∏' p, f p = ∏' (b) (c), f (b, c) :=
  (h.hasProd.prod_fiberwise fun b ↦ (h₁ b).hasProd).tprod_eq.symm

@[to_additive Summable.tsum_prod_uncurry]
/-
**Multipliable.tprod_prod_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommMonoid α] [inst
_1 : TopologicalSpace α] [ContinuousMul α]   [T3Space α] {f : β → γ → α},   Mult
ipliable (Function.uncurry f) →     (∀ (b : β), Multipliable fun c => f b c) → ∏
' (p : β × γ), Function.uncurry f p = ∏' (b : β) (c : γ), f b c
参数：Function.uncurry f；∀ (b : β), Multipliable fun c => f b c；p : β × γ；b : β；c :
 γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProd.prod_fiberwise`：HasProd.prod_fiberwise {f : β × γ -> α} {g : β -
> α} {a : α} (ha : HasProd f a) (hf : forall b, HasProd (fun c => f (b, c)) (g b
)) : HasProd…
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
protected theorem Multipliable.tprod_prod_uncurry {f : β → γ → α}
    (h : Multipliable (Function.uncurry f)) (h₁ : ∀ b, Multipliable fun c ↦ f b c) :
    ∏' p : β × γ, uncurry f p = ∏' (b) (c), f b c :=
  (h.hasProd.prod_fiberwise fun b ↦ (h₁ b).hasProd).tprod_eq.symm

@[to_additive]
/-
**Multipliable.tprod_comm'** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommMonoid α] [inst
_1 : TopologicalSpace α] [ContinuousMul α]   [T3Space α] {f : β → γ → α},   Mult
ipliable (Function.uncurry f) →     (∀ (b : β), Multipliable (f b)) →       (∀ (
c : γ), Multipliable fun b => f b c) → ∏' (c : γ) (b : β), f b c = ∏' (b : β) (c
 : γ), f b c
参数：Function.uncurry f；∀ (b : β), Multipliable (f b)；∀ (c : γ), Multipliable fun 
b => f b c；c : γ；b : β；b : β；c : γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multipliable.tprod_prod_uncurry`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} [inst : CommMonoid α] [inst_1 : TopologicalSpace α] [ContinuousMul α]   
[T3Space α] {f : β → …
· 使用定理 `Multipliable.prod_symm`：Multipliable.prod_symm {f : β × γ -> α} (hf : Mu
ltipliable f) : Multipliable fun p : γ × β => f p.swap
· 使用定理 `Equiv.tprod_eq`：Equiv.tprod_eq (e : γ ≃ β) (f : β -> α) : ∏' c, f (e c) 
= ∏' b, f b
-/
protected theorem Multipliable.tprod_comm' {f : β → γ → α} (h : Multipliable (Function.uncurry f))
    (h₁ : ∀ b, Multipliable (f b)) (h₂ : ∀ c, Multipliable fun b ↦ f b c) :
    ∏' (c) (b), f b c = ∏' (b) (c), f b c := by
  rw [← h.tprod_prod_uncurry h₁, ← h.prod_symm.tprod_prod_uncurry h₂,
    ← (Equiv.prodComm γ β).tprod_eq (uncurry f)]
  rfl

end T3Space

end ContinuousMul

section CompleteSpace

variable [CommGroup α] [UniformSpace α] [IsUniformGroup α]

@[to_additive]
/-
**HasProd.of_sigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.of_sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} {g : β -> α} {
a : α} (hf : forall b, HasProd (fun c => f ⟨b, c⟩) (g b)) (hg : HasProd g a) (h 
: CauchySeq (fun (s : Finset (Σ b : β, γ b)) => ∏ i in s, f i)) : HasProd f a
参数：Σ b : β, γ b；hf : forall b, HasProd (fun c => f ⟨b, c⟩) (g b)；hg : HasProd g 
a；h : CauchySeq (fun (s : Finset (Σ b : β, γ b)) => ∏ i in s, f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_nhds_of_cauchy_adhp`：le_nhds_of_cauchy_adhp {f : Filter α} {x : α} (h
f : Cauchy f) (adhs : ClusterPt x f) : f <= 𝓝 x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_sigma`：prod_sigma {σ : α -> Type*} (s : Finset α) (t : foral
l a, Finset (σ a)) (f : Sigma σ -> β) : ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in
 t a, f…
· 使用定理 `tendsto_finsetProd`：tendsto_finsetProd {f : ι -> α -> M} {x : Filter α} 
{a : ι -> M} (s : Finset ι) : (forall i in s, Tendsto (f i) x (𝓝 (a i))) -> Tend
sto (fun…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_finset_preimage_atTop_atTop`：tendsto_finset_preimage_atTo
p_atTop {f : α -> β} (hf : Function.Injective f) : Tendsto (fun s : Finset β => 
s.preimage f (hf.injOn)) atTop a…
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
theorem HasProd.of_sigma {γ : β → Type*} {f : (Σ b : β, γ b) → α} {g : β → α} {a : α}
    (hf : ∀ b, HasProd (fun c ↦ f ⟨b, c⟩) (g b)) (hg : HasProd g a)
    (h : CauchySeq (fun (s : Finset (Σ b : β, γ b)) ↦ ∏ i ∈ s, f i)) :
    HasProd f a := by
  classical
  apply le_nhds_of_cauchy_adhp h
  simp only [← mapClusterPt_def, mapClusterPt_iff_frequently, frequently_atTop]
  intro u hu s
  rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, hv⟩
  obtain ⟨t0, st0, ht0⟩ : ∃ t0, ∏ i ∈ t0, g i ∈ v ∧ s.image Sigma.fst ⊆ t0 := by
    have A : ∀ᶠ t0 in (atTop : Filter (Finset β)), ∏ i ∈ t0, g i ∈ v := hg (v_open.mem_nhds hv)
    exact (A.and (Ici_mem_atTop _)).exists
  have L : Tendsto (fun t : Finset (Σ b, γ b) ↦ ∏ p ∈ t with p.1 ∈ t0, f p) atTop
      (𝓝 <| ∏ b ∈ t0, g b) := by
    simp only [← sigma_preimage_mk, prod_sigma]
    refine tendsto_finsetProd _ fun b _ ↦ ?_
    change
      Tendsto (fun t ↦ (fun t ↦ ∏ s ∈ t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) atTop (𝓝 (g b))
    exact (hf b).comp (tendsto_finset_preimage_atTop_atTop (sigma_mk_injective))
  have : ∃ t, ∏ p ∈ t with p.1 ∈ t0, f p ∈ v ∧ s ⊆ t :=
    ((Tendsto.eventually_mem L (v_open.mem_nhds st0)).and (Ici_mem_atTop _)).exists
  obtain ⟨t, tv, st⟩ := this
  refine ⟨{p ∈ t | p.1 ∈ t0}, fun x hx ↦ ?_, vu tv⟩
  simpa only [mem_filter, st hx, true_and] using ht0 (mem_image_of_mem Sigma.fst hx)

variable [CompleteSpace α]

@[to_additive]
/-
**Multipliable.sigma_factor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.sigma_factor {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} (ha :
 Multipliable f) (b : β) : Multipliable fun c => f ⟨b, c⟩
参数：Σ b : β, γ b；ha : Multipliable f；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.comp_injective`：Multipliable.comp_injective {i : γ -> β} (h
f : Multipliable f) (hi : Injective i) : Multipliable (f ∘ i)
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
-/
theorem Multipliable.sigma_factor {γ : β → Type*} {f : (Σ b : β, γ b) → α}
    (ha : Multipliable f) (b : β) :
    Multipliable fun c ↦ f ⟨b, c⟩ :=
  ha.comp_injective sigma_mk_injective

@[to_additive]
/-
**Multipliable.sigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} (ha : Multip
liable f) : Multipliable fun b => ∏' c, f ⟨b, c⟩
参数：Σ b : β, γ b；ha : Multipliable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.sigma'`：Multipliable.sigma' {γ : β -> Type*} {f : (Σ b : β,
 γ b) -> α} (ha : Multipliable f) (hf : forall b, Multipliable fun c => f ⟨b, c⟩
) : Multi…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `Multipliable.sigma_factor`：Multipliable.sigma_factor {γ : β -> Type*} {f
 : (Σ b : β, γ b) -> α} (ha : Multipliable f) (b : β) : Multipliable fun c => f 
⟨b, c⟩
-/
theorem Multipliable.sigma {γ : β → Type*} {f : (Σ b : β, γ b) → α} (ha : Multipliable f) :
    Multipliable fun b ↦ ∏' c, f ⟨b, c⟩ :=
  ha.sigma' fun b ↦ ha.sigma_factor b

@[to_additive Summable.prod_factor]
/-
**Multipliable.prod_factor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.prod_factor {f : β × γ -> α} (h : Multipliable f) (b : β) : M
ultipliable fun c => f (b, c)
参数：h : Multipliable f；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.comp_injective`：Multipliable.comp_injective {i : γ -> β} (h
f : Multipliable f) (hi : Injective i) : Multipliable (f ∘ i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
-/
theorem Multipliable.prod_factor {f : β × γ → α} (h : Multipliable f) (b : β) :
    Multipliable fun c ↦ f (b, c) :=
  h.comp_injective fun _ _ h ↦ (Prod.ext_iff.1 h).2

@[to_additive Summable.prod]
/-
**Multipliable.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.prod {f : β × γ -> α} (h : Multipliable f) : Multipliable fun
 b => ∏' c, f (b, c)
参数：h : Multipliable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.sigma`：Multipliable.sigma {γ : β -> Type*} {f : (Σ b : β, γ
 b) -> α} (ha : Multipliable f) : Multipliable fun b => ∏' c, f ⟨b, c⟩
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.multipliable_iff`：Equiv.multipliable_iff (e : γ ≃ β) : Multipliabl
e (f ∘ e) ↔ Multipliable f
-/
lemma Multipliable.prod {f : β × γ → α} (h : Multipliable f) :
    Multipliable fun b ↦ ∏' c, f (b, c) :=
  ((Equiv.sigmaEquivProd β γ).multipliable_iff.mpr h).sigma

@[to_additive]
/-
**HasProd.tprod_fiberwise** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProd.tprod_fiberwise [T2Space α] {f : β -> α} {a : α} (hf : HasProd f a
) (g : β -> γ) : HasProd (fun c : γ => ∏' b : g ⁻¹' {c}, f b) a
参数：hf : HasProd f a；g : β -> γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.sigma`：HasProd.sigma {γ : β -> Type*} {f : (Σ b : β, γ b) -> α} 
{g : β -> α} {a : α} (ha : HasProd f a) (hf : forall b, HasProd (fun c => f ⟨b, 
c⟩)…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.hasProd_iff`：Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ H
asProd f a
· 使用定理 `Multipliable.hasProd_iff`：Multipliable.hasProd_iff (h : Multipliable f L
) : HasProd f a L ↔ ∏'[L] b, f b = a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Multipliable.subtype`：Multipliable.subtype (hf : Multipliable f) (p : β 
-> Prop) : Multipliable (f ∘ (↑) : Subtype p -> α)
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
-/
lemma HasProd.tprod_fiberwise [T2Space α] {f : β → α} {a : α} (hf : HasProd f a) (g : β → γ) :
    HasProd (fun c : γ ↦ ∏' b : g ⁻¹' {c}, f b) a :=
  (((Equiv.sigmaFiberEquiv g).hasProd_iff).mpr hf).sigma <|
    fun _ ↦ ((hf.multipliable.subtype _).hasProd_iff).mpr rfl

section CompleteT0Space

variable [T0Space α]

@[to_additive]
/-
**Multipliable.tprod_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommGroup α] [inst_1 : UniformSpac
e α] [IsUniformGroup α] [CompleteSpace α]   [T0Space α] {γ : β → Type u_4} {f : 
(b : β) × γ b → α},   Multipliable f → ∏' (p : (b : β) × γ b), f p = ∏' (b : β) 
(c : γ b), f ⟨b, c⟩
参数：b : β；p : (b : β) × γ b；b : β；c : γ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.tprod_sigma'`：∀ {α : Type u_1} {β : Type u_2} [inst : CommM
onoid α] [inst_1 : TopologicalSpace α] [ContinuousMul α] [T3Space α]   {γ : β → 
Type u_4} {f : …
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `Multipliable.sigma_factor`：Multipliable.sigma_factor {γ : β -> Type*} {f
 : (Σ b : β, γ b) -> α} (ha : Multipliable f) (b : β) : Multipliable fun c => f 
⟨b, c⟩
-/
protected theorem Multipliable.tprod_sigma {γ : β → Type*} {f : (Σ b : β, γ b) → α}
    (ha : Multipliable f) : ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  Multipliable.tprod_sigma' (fun b ↦ ha.sigma_factor b) ha

@[to_additive Summable.tsum_prod]
/-
**Multipliable.tprod_prod** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommGroup α] [inst_
1 : UniformSpace α] [IsUniformGroup α]   [CompleteSpace α] [T0Space α] {f : β × 
γ → α}, Multipliable f → ∏' (p : β × γ), f p = ∏' (b : β) (c : γ), f (b, c)
参数：p : β × γ；b : β；c : γ；b, c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.tprod_prod'`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
 [inst : CommMonoid α] [inst_1 : TopologicalSpace α] [ContinuousMul α]   [T3Spac
e α] {f : β × …
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `Multipliable.prod_factor`：Multipliable.prod_factor {f : β × γ -> α} (h :
 Multipliable f) (b : β) : Multipliable fun c => f (b, c)
-/
protected theorem Multipliable.tprod_prod {f : β × γ → α} (h : Multipliable f) :
    ∏' p, f p = ∏' (b) (c), f ⟨b, c⟩ :=
  h.tprod_prod' h.prod_factor

@[to_additive]
/-
**Multipliable.tprod_comm** 是 Mathlib 中的一个定理，位于命名空间 `Multipliable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : CommGroup α] [inst_
1 : UniformSpace α] [IsUniformGroup α]   [CompleteSpace α] [T0Space α] {f : β → 
γ → α},   Multipliable (Function.uncurry f) → ∏' (c : γ) (b : β), f b c = ∏' (b 
: β) (c : γ), f b c
参数：Function.uncurry f；c : γ；b : β；b : β；c : γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multipliable.tprod_comm'`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
 [inst : CommMonoid α] [inst_1 : TopologicalSpace α] [ContinuousMul α]   [T3Spac
e α] {f : β → …
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `Multipliable.prod_factor`：Multipliable.prod_factor {f : β × γ -> α} (h :
 Multipliable f) (b : β) : Multipliable fun c => f (b, c)
· 使用定理 `Multipliable.prod_symm`：Multipliable.prod_symm {f : β × γ -> α} (hf : Mu
ltipliable f) : Multipliable fun p : γ × β => f p.swap
-/
protected theorem Multipliable.tprod_comm {f : β → γ → α} (h : Multipliable (Function.uncurry f)) :
    ∏' (c) (b), f b c = ∏' (b) (c), f b c :=
  h.tprod_comm' h.prod_factor h.prod_symm.prod_factor

end CompleteT0Space

end CompleteSpace

section Pi

variable {ι : Type*} {X : α → Type*} [∀ x, CommMonoid (X x)] [∀ x, TopologicalSpace (X x)]
  {L : SummationFilter ι}

@[to_additive]
/-
**Pi.hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.hasProd {f : ι -> forall x, X x} {g : forall x, X x} : HasProd f g L ↔ 
forall x, HasProd (fun i => f i x) (g x) L
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
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Pi.hasProd {f : ι → ∀ x, X x} {g : ∀ x, X x} :
    HasProd f g L ↔ ∀ x, HasProd (fun i ↦ f i x) (g x) L := by
  simp only [HasProd, tendsto_pi_nhds, Finset.prod_apply]

@[to_additive]
/-
**Pi.multipliable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.multipliable {f : ι -> forall x, X x} : Multipliable f L ↔ forall x, Mu
ltipliable (fun i => f i x) L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Pi.multipliable {f : ι → ∀ x, X x} :
    Multipliable f L ↔ ∀ x, Multipliable (fun i ↦ f i x) L := by
  simp only [Multipliable, Pi.hasProd, Classical.skolem]

@[to_additive]
/-
**tprod_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_apply [L.NeBot] [forall x, T2Space (X x)] {f : ι -> forall x, X x} {
x : α} (hf : Multipliable f L) : (∏'[L] i, f i) x = ∏'[L] i, f i x
参数：X x；hf : Multipliable f L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.hasProd`：Pi.hasProd {f : ι -> forall x, X x} {g : forall x, X x} : Ha
sProd f g L ↔ forall x, HasProd (fun i => f i x) (g x) L
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem tprod_apply [L.NeBot] [∀ x, T2Space (X x)] {f : ι → ∀ x, X x} {x : α}
    (hf : Multipliable f L) : (∏'[L] i, f i) x = ∏'[L] i, f i x :=
  (Pi.hasProd.mp hf.hasProd x).tprod_eq.symm

end Pi


/-! ## Multiplicative opposite -/

section MulOpposite

open MulOpposite

variable [AddCommMonoid α] [TopologicalSpace α] {f : β → α} {a : α}

/-
**HasSum.op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.op (hf : HasSum f a L) : HasSum (fun a => op (f a)) (op a) L
参数：hf : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `MulOpposite.continuous_op`：continuous_op : Continuous (op : M -> Mᵐᵒᵖ)
-/
theorem HasSum.op (hf : HasSum f a L) : HasSum (fun a ↦ op (f a)) (op a) L :=
  (hf.map (@opAddEquiv α _) continuous_op :)
/-
**Summable.op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.op (hf : Summable f L) : Summable (op ∘ f) L
参数：hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.op`：HasSum.op (hf : HasSum f a L) : HasSum (fun a => op (f a)) (o
p a) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.op (hf : Summable f L) : Summable (op ∘ f) L :=
  hf.hasSum.op.summable
/-
**HasSum.unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.unop {f : β -> αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a L) : HasSum (fun a
 => unop (f a)) (unop a) L
参数：hf : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `MulOpposite.continuous_unop`：continuous_unop : Continuous (unop : Mᵐᵒᵖ -
> M)
-/
theorem HasSum.unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a L) :
    HasSum (fun a ↦ unop (f a)) (unop a) L :=
  (hf.map (@opAddEquiv α _).symm continuous_unop :)
/-
**Summable.unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.unop {f : β -> αᵐᵒᵖ} (hf : Summable f L) : Summable (unop ∘ f) L
参数：hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.unop`：HasSum.unop {f : β -> αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a L) 
: HasSum (fun a => unop (f a)) (unop a) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.unop {f : β → αᵐᵒᵖ} (hf : Summable f L) : Summable (unop ∘ f) L :=
  hf.hasSum.unop.summable

@[simp]
/-
**hasSum_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_op : HasSum (fun a => op (f a)) (op a) L ↔ HasSum f a L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.unop`：HasSum.unop {f : β -> αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a L) 
: HasSum (fun a => unop (f a)) (unop a) L
· 使用定理 `HasSum.op`：HasSum.op (hf : HasSum f a L) : HasSum (fun a => op (f a)) (o
p a) L
-/
theorem hasSum_op : HasSum (fun a ↦ op (f a)) (op a) L ↔ HasSum f a L :=
  ⟨HasSum.unop, HasSum.op⟩

@[simp]
/-
**hasSum_unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_unop {f : β -> αᵐᵒᵖ} {a : αᵐᵒᵖ} : HasSum (fun a => unop (f a)) (uno
p a) L ↔ HasSum f a L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.op`：HasSum.op (hf : HasSum f a L) : HasSum (fun a => op (f a)) (o
p a) L
· 使用定理 `HasSum.unop`：HasSum.unop {f : β -> αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a L) 
: HasSum (fun a => unop (f a)) (unop a) L
-/
theorem hasSum_unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} :
    HasSum (fun a ↦ unop (f a)) (unop a) L ↔ HasSum f a L :=
  ⟨HasSum.op, HasSum.unop⟩

@[simp]
/-
**summable_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_op : (Summable (fun a => op (f a)) L) ↔ Summable f L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.unop`：Summable.unop {f : β -> αᵐᵒᵖ} (hf : Summable f L) : Summa
ble (unop ∘ f) L
· 使用定理 `Summable.op`：Summable.op (hf : Summable f L) : Summable (op ∘ f) L
-/
theorem summable_op : (Summable (fun a ↦ op (f a)) L) ↔ Summable f L :=
  ⟨Summable.unop, Summable.op⟩
/-
**summable_unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_unop {f : β -> αᵐᵒᵖ} : (Summable (fun a => unop (f a)) L) ↔ Summa
ble f L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.op`：Summable.op (hf : Summable f L) : Summable (op ∘ f) L
· 使用定理 `Summable.unop`：Summable.unop {f : β -> αᵐᵒᵖ} (hf : Summable f L) : Summa
ble (unop ∘ f) L
-/
theorem summable_unop {f : β → αᵐᵒᵖ} : (Summable (fun a ↦ unop (f a)) L) ↔ Summable f L :=
  ⟨Summable.op, Summable.unop⟩
/-
**tsum_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_op [T2Space α] : ∑'[L] x, op (f x) = op (∑'[L] x, f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsClosedEmbedding.map_tsum`：∀ {ι : Type u_4} {α : Type u_5} {α'
 : Type u_6} {G : Type u_7} [inst : AddCommMonoid α] [inst_1 : AddCommMonoid α']
   [inst_2 : TopologicalS…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
theorem tsum_op [T2Space α] : ∑'[L] x, op (f x) = op (∑'[L] x, f x) :=
  (opHomeomorph.isClosedEmbedding.map_tsum f (g := opAddEquiv)).symm
/-
**tsum_unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_unop [T2Space α] {f : β -> αᵐᵒᵖ} : ∑'[L] x, unop (f x) = unop (∑'[L] 
x, f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_op`：tsum_op [T2Space α] : ∑'[L] x, op (f x) = op (∑'[L] x, f x)
-/
theorem tsum_unop [T2Space α] {f : β → αᵐᵒᵖ} : ∑'[L] x, unop (f x) = unop (∑'[L] x, f x) :=
  op_injective tsum_op.symm

end MulOpposite

/-! ## Interaction with the star -/

section ContinuousStar

variable [AddCommMonoid α] [TopologicalSpace α] [StarAddMonoid α] [ContinuousStar α] {f : β → α}
  {a : α}

/-
**HasSum.star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.star (h : HasSum f a L) : HasSum (fun b => star (f b)) (star a) L
参数：h : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
-/
theorem HasSum.star (h : HasSum f a L) : HasSum (fun b ↦ star (f b)) (star a) L := by
  simpa only using! h.map (starAddEquiv : α ≃+ α) continuous_star
/-
**Summable.star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.star (hf : Summable f L) : Summable (fun b => star (f b)) L
参数：hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.star`：HasSum.star (h : HasSum f a L) : HasSum (fun b => star (f b
)) (star a) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.star (hf : Summable f L) : Summable (fun b ↦ star (f b)) L :=
  hf.hasSum.star.summable
/-
**Summable.ofStar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.ofStar (hf : Summable (fun b => Star.star (f b)) L) : Summable f 
L
参数：hf : Summable (fun b => Star.star (f b)) L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Summable.star`：Summable.star (hf : Summable f L) : Summable (fun b => st
ar (f b)) L
-/
theorem Summable.ofStar (hf : Summable (fun b ↦ Star.star (f b)) L) : Summable f L := by
  simpa only [star_star] using hf.star

@[simp]
/-
**summable_star_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_star_iff : Summable (fun b => star (f b)) L ↔ Summable f L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.ofStar`：Summable.ofStar (hf : Summable (fun b => Star.star (f b
)) L) : Summable f L
· 使用定理 `Summable.star`：Summable.star (hf : Summable f L) : Summable (fun b => st
ar (f b)) L
-/
theorem summable_star_iff : Summable (fun b ↦ star (f b)) L ↔ Summable f L :=
  ⟨Summable.ofStar, Summable.star⟩

@[simp]
/-
**summable_star_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_star_iff' : Summable (star f) L ↔ Summable f L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_star_iff`：summable_star_iff : Summable (fun b => star (f b)) L 
↔ Summable f L
-/
theorem summable_star_iff' : Summable (star f) L ↔ Summable f L :=
  summable_star_iff
/-
**tsum_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_star [T2Space α] : star (∑'[L] b, f b) = ∑'[L] b, star (f b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFil
ter β} {G : Type u_…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem tsum_star [T2Space α] : star (∑'[L] b, f b) = ∑'[L] b, star (f b) :=
  Function.LeftInverse.map_tsum (g := starAddEquiv) f continuous_star continuous_star star_star

end ContinuousStar

