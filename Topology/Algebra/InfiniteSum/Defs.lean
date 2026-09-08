/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Algebra.BigOperators.Group.Finset.Preimage

/-!
# Infinite sum and product in a topological monoid

This file defines infinite products and sums for (possibly infinite) indexed families of elements
in a commutative topological monoid (resp. add monoid).

To handle convergence questions we use the formalism of *summation filters* (defined in the
file `Mathlib/Topology/Algebra/InfiniteSum/SummationFilter.lean`). These are filters on the finite
subsets of a given type, and we define a function to be *summable* for a summation filter `L` if
its partial sums over finite subsets tend to a limit along `L` (and similarly for products).

This simultaneously generalizes several different kinds of summation: for instance,
*unconditional summation* (which makes sense for any index type) where we take the limit with
respect to the `atTop` filter; but also *conditional summation* for functions on `ℕ`, where the
limit is over the partial sums `∑ i ∈ range n, f i` as `n → ∞` (so there exist
conditionally-summable sequences which are not unconditionally summable).

## Implementation notes

We say that a function `f : β → α` has a product of `a` w.r.t. the summation filter `L` if the
function `fun s : Finset β ↦ ∏ b ∈ s, f b` converges to `a` w.r.t. the filter `L.filter` on
`Finset β`.

In the most important case of unconditional summation, this translates to the following condition:
for every neighborhood `U` of `a`, there exists a finite set `s : Finset β` of indices such
that `∏ b ∈ s', f b ∈ U` for any finite set `s'` which is a superset of `s`.

This may yield some unexpected results. For example, according to this definition, the product
`∏' n : ℕ, (1 : ℝ) / 2` unconditionally exists and is equal to `0`. More strikingly,
the product `∏' n : ℕ, (n : ℝ)` unconditionally exists and is equal to `0`, because one
of its terms is `0` (even though the product of the remaining terms diverges). Users who would
prefer that these products be considered not to exist can carry them out in the unit group `ℝˣ`
rather than in `ℝ`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/

@[expose] public section

/- **NOTE**. This file is intended to be kept short, just enough to state the basic definitions and
six key lemmas relating them together, namely `Summable.hasSum`, `Multipliable.hasProd`,
`HasSum.tsum_eq`, `HasProd.tprod_eq`, `Summable.hasSum_iff`, and `Multipliable.hasProd_iff`.

Do not add further lemmas here -- add them to `InfiniteSum.Basic` or (preferably) another, more
specific file. -/

noncomputable section

open Filter Function SummationFilter

open scoped Topology

variable {α β γ : Type*}

section HasProd

variable [CommMonoid α] [TopologicalSpace α]

/-- `HasProd f a L` means that the (potentially infinite) product of the `f b` for `b : β` converges
to `a` along the SummationFilter `L`.

By default `L` is the `unconditional` one, corresponding to the limit of all finite sets towards
the entire type. So we take the product over bigger and bigger finite sets. This product operation
is invariant under permuting the terms (while products for more general summation filters usually
are not).

For the definition and many statements, `α` does not need to be a topological monoid, only a monoid
with a topology (i.e. the multiplication is not assumed to be continuous). We only add this
assumption later, for the lemmas where it is relevant.

These are defined in an identical way to infinite sums (`HasSum`). For example, we say that
the function `ℕ → ℝ` sending `n` to `1 / 2` has a product of `0`, rather than saying that it does
not converge as some authors would. -/
@[to_additive /-- `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β`
converges to `a` along the SummationFilter `L`.

By default `L` is the `unconditional` one, corresponding to the limit of all finite sets towards
the entire type. So we take the sum over bigger and bigger finite sets. This sum operation is
invariant under permuting the terms (while sums for more general summation filters usually are not).
This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

In particular, the function `ℕ → ℝ` sending `n` to `(-1) ^ n / (n + 1)` does not have a
sum for this definition, although it is summable for the `conditional` summation filter that
takes limits of sums over `n ∈ {0, ..., X}` as `X → ∞`. However, a series which is *absolutely*
convergent with respect to the conditional summation filter is in fact unconditionally summable.

For the definition and many statements, `α` does not need to be a topological additive monoid,
only an additive monoid with a topology (i.e. the addition is not assumed to be continuous). We
only add this assumption later, for the lemmas where it is relevant. -/]
/-
**HasProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasProd (f : β -> α) (a : α) (L
参数：f : β -> α；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def HasProd (f : β → α) (a : α) (L := unconditional β) : Prop :=
  Tendsto (fun s : Finset β ↦ ∏ b ∈ s, f b) L.filter (𝓝 a)

/-- `Multipliable f` means that `f` has some (infinite) product with respect to `L`. Use `tprod` to
get the value. -/
@[to_additive
/-- `Summable f` means that `f` has some (infinite) sum with respect to `L`. Use `tsum` to get the
value. -/]
/-
**Multipliable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Multipliable (f : β -> α) (L
参数：f : β -> α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Multipliable (f : β → α) (L := unconditional β) : Prop :=
  ∃ a, HasProd f a L

@[to_additive]
/-
**Multipliable.mono_filter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.mono_filter {f : β -> α} {L₁ L₂ : SummationFilter β} (hf : Mu
ltipliable f L₂) (h : L₁.filter <= L₂.filter) : Multipliable f L₁
参数：hf : Multipliable f L₂；h : L₁.filter <= L₂.filter。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
-/
lemma Multipliable.mono_filter {f : β → α} {L₁ L₂ : SummationFilter β}
    (hf : Multipliable f L₂) (h : L₁.filter ≤ L₂.filter) : Multipliable f L₁ :=
  match hf with | ⟨a, ha⟩ => ⟨a, ha.mono_left h⟩

open scoped Classical in
/-- `∏' i, f i` is the unconditional product of `f`, if it exists, or 1 otherwise.

More generally, if `L` is a `SummationFilter`, `∏'[L] i, f i` is the product of `f` with respect to
`L` if it exists, and `1` otherwise.

(Note that even if the unconditional product exists, it might not be unique if the topology is not
separated. When the multiplicative support of `f` is finite, we make the most reasonable choice,
to use the product over the multiplicative support. Otherwise, we choose arbitrarily an `a`
satisfying `HasProd f a`. Similar remarks apply to more general summation filters.) -/
@[to_additive /-- `∑' i, f i` is the unconditional sum of `f` if it exists, or 0 otherwise.

More generally, if `L` is a `SummationFilter`, `∑'[L] i, f i` is the sum of `f` with respect to
`L` if it exists, and `0` otherwise.

(Note that even if the unconditional sum exists, it might not be unique if the topology is not
separated. When the support of `f` is finite, we make the most reasonable choice, to use the sum
over the support. Otherwise, we choose arbitrarily an `a` satisfying `HasSum f a`. Similar remarks
apply to more general summation filters.)
-/]
noncomputable irreducible_def tprod (f : β → α) (L := unconditional β) :=
  if h : Multipliable f L then
    if L.HasSupport ∧ (mulSupport f ∩ L.support).Finite then finprod (L.support.mulIndicator f)
    else if HasProd f 1 L then 1
    else h.choose
  else 1

variable {L : SummationFilter β}

@[inherit_doc tprod]
notation3 "∏'[" L "]" (...)", "r:67:(scoped f => tprod f L) => r
@[inherit_doc tsum]
notation3 "∑'[" L "]" (...)", "r:67:(scoped f => tsum f L) => r

-- see note [operator precedence of big operators]
@[inherit_doc tprod]
notation3 "∏' "(...)", "r:67:(scoped f => tprod f (unconditional _)) => r
@[inherit_doc tsum]
notation3 "∑' "(...)", "r:67:(scoped f => tsum f (unconditional _)) => r

@[to_additive]
/-
**hasProd_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProd_bot (hL : ¬L.NeBot) (f : β -> α) (a : α) : HasProd f a L
参数：hL : ¬L.NeBot；f : β -> α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [ins
t_1 : TopologicalSpace α] (f : β → α) (a : α)   (L : SummationFilter β), HasProd
 f…
· 使用定理 `Filter.tendsto_bot`：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f 
⊥ l
-/
lemma hasProd_bot (hL : ¬L.NeBot) (f : β → α) (a : α) :
    HasProd f a L := by
  have : L.filter = ⊥ := by contrapose! hL; exact ⟨hL⟩
  rw [HasProd, this]
  exact tendsto_bot

@[to_additive]
/-
**multipliable_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multipliable_bot (hL : ¬L.NeBot) (f : β -> α) : Multipliable f L
参数：hL : ¬L.NeBot；f : β -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasProd_bot`：hasProd_bot (hL : ¬L.NeBot) (f : β -> α) (a : α) : HasProd 
f a L
-/
lemma multipliable_bot (hL : ¬L.NeBot) (f : β → α) :
    Multipliable f L :=
  ⟨1, hasProd_bot hL ..⟩

/-- If the summation filter is the trivial filter `⊥`, then the topological product is equal to the
finite product (which is taken to be 1 if the multiplicative support of `f` is infinite).

Note that in this case `HasProd f a` is satisfied for *every* element `a` of the target, so the
value assigned to the `tprod` is a question of conventions. -/
@[to_additive /-- If the summation filter is the trivial filter `⊥`, then the topological sum is
equal to the finite sum (which is taken to be 1 if the support of `f` is infinite).

Note that in this case `HasSum f a` is satisfied for *every* element `a` of the target, so the
value assigned to the `tsum` is a question of conventions. -/]
/-
**tprod_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_bot (hL : ¬L.NeBot) (f : β -> α) : ∏'[L] b, f b = ∏ᶠ b, f b
参数：hL : ¬L.NeBot；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `multipliable_bot`：multipliable_bot (hL : ¬L.NeBot) (f : β -> α) : Multip
liable f L
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tprod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : CommMonoid α] [inst_1
 : TopologicalSpace α] (f : β → α) (L : SummationFilter β),   tprod f L =     i…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `SummationFilter.leAtTop_of_not_NeBot`：leAtTop_of_not_NeBot (L : Summatio
nFilter β) (hL : ¬L.NeBot) : L.LeAtTop
· 使用定理 `SummationFilter.support_eq_univ`：∀ {β : Type u_2} (L : SummationFilter β
) [L.LeAtTop], L.support = Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用引理 `Set.mulIndicator_univ`：mulIndicator_univ (f : α -> M) : mulIndicator (un
iv : Set α) f = f
· 使用引理 `eq_true_intro`：eq_true_intro {a : Prop} (h : a) : a = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `hasProd_bot`：hasProd_bot (hL : ¬L.NeBot) (f : β -> α) (a : α) : HasProd 
f a L
· 使用定理 `finprod_of_infinite_mulSupport`：finprod_of_infinite_mulSupport {f : α ->
 M} (hf : (mulSupport f).Infinite) : ∏ᶠ i, f i = 1
-/
lemma tprod_bot (hL : ¬L.NeBot) (f : β → α) : ∏'[L] b, f b = ∏ᶠ b, f b := by
  simp only [tprod_def, dif_pos (multipliable_bot hL f)]
  have : L.LeAtTop := L.leAtTop_of_not_NeBot hL
  rw [L.support_eq_univ, Set.inter_univ, Set.mulIndicator_univ]
  by_cases hf : (mulSupport f).Finite
  · rw [eq_true_intro hf, if_pos]
    simp only [and_true]
    infer_instance
  · rwa [if_neg (by tauto), if_pos (hasProd_bot hL _ _), finprod_of_infinite_mulSupport]

variable {f : β → α} {a : α} {s : Finset β}

@[to_additive]
/-
**HasProd.multipliable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.multipliable (h : HasProd f a L) : Multipliable f L
参数：h : HasProd f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasProd.multipliable (h : HasProd f a L) : Multipliable f L :=
  ⟨a, h⟩

@[to_additive]
/-
**tprod_eq_one_of_not_multipliable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_eq_one_of_not_multipliable (h : ¬Multipliable f L) : ∏'[L] b, f b = 
1
参数：h : ¬Multipliable f L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : CommMonoid α] [inst_1
 : TopologicalSpace α] (f : β → α) (L : SummationFilter β),   tprod f L =     i…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tprod_eq_one_of_not_multipliable (h : ¬Multipliable f L) : ∏'[L] b, f b = 1 := by
  simp [tprod_def, h]

@[to_additive]
/-
**Function.Injective.hasProd_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.hasProd_map_iff {L : SummationFilter γ} {g : γ -> β} (h
g : Injective g) : HasProd f a (L.map ⟨g, hg⟩) ↔ HasProd (f ∘ g) a L
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SummationFilter.map_filter`：∀ {β : Type u_2} {γ : Type u_3} (L : Summati
onFilter β) (f : β ↪ γ),   (L.map f).filter = Filter.map (Finset.map f) L.filter
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Function.Injective.hasProd_map_iff {L : SummationFilter γ} {g : γ → β} (hg : Injective g) :
    HasProd f a (L.map ⟨g, hg⟩) ↔ HasProd (f ∘ g) a L := by
  simp [HasProd, Function.comp_def]

@[to_additive]
/-
**Function.Injective.hasProd_comap_iff_of_hasSupport** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：Function.Injective.hasProd_comap_iff_of_hasSupport [L.HasSupport] {g : γ -
> β} (hg : Injective g) (hf : forall x in L.support, x ∉ Set.range g -> f x = 1)
 : HasProd (f ∘ g) a (L.comap ⟨g, hg⟩) ↔ HasProd f a L
参数：hg : Injective g；hf : forall x in L.support, x ∉ Set.range g -> f x = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `SummationFilter.comap_filter`：∀ {β : Type u_2} {γ : Type u_3} (L : Summa
tionFilter β) (f : γ ↪ β),   (L.comap f).filter = Filter.map (fun s => s.preimag
e ⇑f ⋯) L.filter
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `SummationFilter.HasSupport.eventually_le_support`：∀ {β : Type u_2} {L : 
SummationFilter β} [self : L.HasSupport], ∀ᶠ (s : Finset β) in L.filter, ↑s ⊆ L.
support
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Finset.prod_preimage`：prod_preimage (f : ι -> κ) (s : Finset κ) (hf) (g 
: κ -> β) (hg : forall x in s, x ∉ Set.range f -> g x = 1) : ∏ x in s.preimage f
 hf, g (f …
-/
theorem Function.Injective.hasProd_comap_iff_of_hasSupport [L.HasSupport] {g : γ → β}
    (hg : Injective g) (hf : ∀ x ∈ L.support, x ∉ Set.range g → f x = 1) :
    HasProd (f ∘ g) a (L.comap ⟨g, hg⟩) ↔ HasProd f a L := by
  simp only [HasProd, SummationFilter.comap_filter, tendsto_map'_iff, comp_apply,
    Embedding.coeFn_mk, Function.comp_def]
  refine tendsto_congr' ?_
  filter_upwards [L.eventually_le_support] with s hs
  rw [s.prod_preimage]
  exact fun x h h' ↦ hf x (hs h) h'

@[to_additive]
/-
**Function.Injective.hasProd_comap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.hasProd_comap_iff {g : γ -> β} (hg : Injective g) (hf :
 forall x, x ∉ Set.range g -> f x = 1) : HasProd (f ∘ g) a (L.comap ⟨g, hg⟩) ↔ H
asProd f a L
参数：hg : Injective g；hf : forall x, x ∉ Set.range g -> f x = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `SummationFilter.comap_filter`：∀ {β : Type u_2} {γ : Type u_3} (L : Summa
tionFilter β) (f : γ ↪ β),   (L.comap f).filter = Filter.map (fun s => s.preimag
e ⇑f ⋯) L.filter
· 使用定理 `Filter.tendsto_congr`：tendsto_congr {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂
 : Filter β} (h : forall x, f₁ x = f₂ x) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用引理 `Finset.prod_preimage`：prod_preimage (f : ι -> κ) (s : Finset κ) (hf) (g 
: κ -> β) (hg : forall x in s, x ∉ Set.range f -> g x = 1) : ∏ x in s.preimage f
 hf, g (f …
-/
theorem Function.Injective.hasProd_comap_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ x, x ∉ Set.range g → f x = 1) :
    HasProd (f ∘ g) a (L.comap ⟨g, hg⟩) ↔ HasProd f a L := by
  simp only [HasProd, SummationFilter.comap_filter, tendsto_map'_iff, comp_apply,
    Embedding.coeFn_mk, Function.comp_def]
  refine tendsto_congr fun s ↦ ?_
  rw [s.prod_preimage]
  exact fun x _ h ↦ hf x h

@[to_additive]
/-
**Function.Injective.hasProd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.hasProd_iff {g : γ -> β} (hg : Injective g) (hf : foral
l x, x ∉ Set.range g -> f x = 1) : HasProd (f ∘ g) a ↔ HasProd f a
参数：hg : Injective g；hf : forall x, x ∉ Set.range g -> f x = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.hasProd_comap_iff`：Function.Injective.hasProd_comap_i
ff {g : γ -> β} (hg : Injective g) (hf : forall x, x ∉ Set.range g -> f x = 1) :
 HasProd (f ∘ g) a (L.coma…
· 使用定理 `SummationFilter.comap_unconditional`：∀ {γ : Type u_3} {β : Type u_4} (f 
: γ ↪ β), (SummationFilter.unconditional β).comap f = SummationFilter.unconditio
nal γ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Function.Injective.hasProd_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ x, x ∉ Set.range g → f x = 1) :
    HasProd (f ∘ g) a ↔ HasProd f a := by
  rw [← hg.hasProd_comap_iff hf, SummationFilter.comap_unconditional]

@[to_additive]
/-
**hasProd_subtype_comap_iff_of_mulSupport_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_subtype_comap_iff_of_mulSupport_subset {s : Set β} (hf : mulSuppor
t f subseteq s) : HasProd (f ∘ (↑) : s -> α) a (L.comap <| Embedding.subtype _) 
↔ HasProd f a L
参数：hf : mulSupport f subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.hasProd_comap_iff`：Function.Injective.hasProd_comap_i
ff {g : γ -> β} (hg : Injective g) (hf : forall x, x ∉ Set.range g -> f x = 1) :
 HasProd (f ∘ g) a (L.coma…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Function.mulSupport_subset_iff'`：mulSupport_subset_iff' : mulSupport f s
ubseteq s ↔ forall x ∉ s, f x = 1
-/
theorem hasProd_subtype_comap_iff_of_mulSupport_subset {s : Set β} (hf : mulSupport f ⊆ s) :
    HasProd (f ∘ (↑) : s → α) a (L.comap <| Embedding.subtype _) ↔ HasProd f a L :=
  Subtype.coe_injective.hasProd_comap_iff <| by simpa using mulSupport_subset_iff'.1 hf

@[to_additive]
/-
**hasProd_subtype_iff_of_mulSupport_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_subtype_iff_of_mulSupport_subset {s : Set β} (hf : mulSupport f su
bseteq s) : HasProd (f ∘ (↑) : s -> α) a ↔ HasProd f a
参数：hf : mulSupport f subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SummationFilter.comap_unconditional`：∀ {γ : Type u_3} {β : Type u_4} (f 
: γ ↪ β), (SummationFilter.unconditional β).comap f = SummationFilter.unconditio
nal γ
· 使用定理 `hasProd_subtype_comap_iff_of_mulSupport_subset`：hasProd_subtype_comap_if
f_of_mulSupport_subset {s : Set β} (hf : mulSupport f subseteq s) : HasProd (f ∘
 (↑) : s -> α) a (L.comap <| Embeddi…
-/
theorem hasProd_subtype_iff_of_mulSupport_subset {s : Set β} (hf : mulSupport f ⊆ s) :
    HasProd (f ∘ (↑) : s → α) a ↔ HasProd f a := by
  simpa using hasProd_subtype_comap_iff_of_mulSupport_subset hf (L := unconditional _)

@[to_additive]
/-
**hasProd_fintype_support** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_fintype_support [Fintype β] (f : β -> α) (L : SummationFilter β) [
L.HasSupport] [DecidablePred (· in L.support)] : HasProd f (∏ b in L.support, f 
b) L
参数：f : β -> α；L : SummationFilter β；· in L.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `SummationFilter.eventually_mem_or_not_mem`：eventually_mem_or_not_mem (L 
: SummationFilter β) [HasSupport L] (b : β) : (forallᶠ s in L.filter, b in s) ∨ 
(forallᶠ s in L.filter, b ∉ s)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
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
-/
theorem hasProd_fintype_support [Fintype β] (f : β → α) (L : SummationFilter β) [L.HasSupport]
    [DecidablePred (· ∈ L.support)] : HasProd f (∏ b ∈ L.support, f b) L := by
  apply tendsto_nhds_of_eventually_eq
  have h1 : ⋂ b ∈ L.support, {s | b ∈ s} ∈ L.filter :=
    (L.filter.biInter_mem L.support.toFinite).mpr (by tauto)
  have h2 : ⋂ b ∈ L.supportᶜ, {s | b ∉ s} ∈ L.filter :=
    (L.filter.biInter_mem L.supportᶜ.toFinite).mpr
      (fun b hb ↦ (L.eventually_mem_or_not_mem b).resolve_left hb)
  filter_upwards [h1, h2] with s hs hs'
  congr 1
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_compl_iff] at hs hs'
  grind

@[to_additive]
/-
**hasProd_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_fintype [Fintype β] (f : β -> α) (L
参数：f : β -> α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `SummationFilter.support_eq_univ`：∀ {β : Type u_2} (L : SummationFilter β
) [L.LeAtTop], L.support = Set.univ
· 使用定理 `Set.toFinset_univ`：toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)
] : (Set.univ : Set α).toFinset = Finset.univ
· 使用定理 `hasProd_fintype_support`：hasProd_fintype_support [Fintype β] (f : β -> α
) (L : SummationFilter β) [L.HasSupport] [DecidablePred (· in L.support)] : HasP
rod f (∏ b in…
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
-/
theorem hasProd_fintype [Fintype β] (f : β → α) (L := unconditional β) [L.LeAtTop] :
    HasProd f (∏ b, f b) L := by
  simpa using hasProd_fintype_support f L

@[to_additive]
/-
**Finset.hasProd_support** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.hasProd_support (s : Finset β) (f : β -> α) (L
参数：s : Finset β；f : β -> α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `hasProd_fintype_support`：hasProd_fintype_support [Fintype β] (f : β -> α
) (L : SummationFilter β) [L.HasSupport] [DecidablePred (· in L.support)] : HasP
rod f (∏ b in…
-/
theorem Finset.hasProd_support (s : Finset β) (f : β → α) (L := unconditional (s : Set β))
    [L.HasSupport] [DecidablePred (· ∈ L.support)] :
    HasProd (f ∘ (↑) : (↑s : Set β) → α)
      (∏ b ∈ (L.support.toFinset.map <| Embedding.subtype _), f b) L := by
  simpa [prod_attach] using hasProd_fintype_support (f ∘ Subtype.val) L

set_option backward.isDefEq.respectTransparency false in
-- note this is not deduced from `Finset.hasProd_support` to avoid needing `[DecidableEq β]`
@[to_additive]
/-
**Finset.hasProd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [inst_1 : Topologica
lSpace α] (s : Finset β) (f : β → α)   (L : optParam (SummationFilter ↑↑s) (Summ
ationFilter.unconditional ↑↑s)) [L.LeAtTop],   HasProd (f ∘ Subtype.val) (∏ b ∈ 
s, f b) L
参数：s : Finset β；f : β → α；L : optParam (SummationFilter ↑↑s) (SummationFilter.un
conditional ↑↑s)；f ∘ Subtype.val；∏ b ∈ s, f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `SummationFilter.support_eq_univ`：∀ {β : Type u_2} (L : SummationFilter β
) [L.LeAtTop], L.support = Set.univ
· 使用定理 `Set.toFinset_univ`：toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)
] : (Set.univ : Set α).toFinset = Finset.univ
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `Finset.hasProd_support`：Finset.hasProd_support (s : Finset β) (f : β -> 
α) (L
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
-/
protected theorem Finset.hasProd (s : Finset β) (f : β → α)
    (L := unconditional (s : Set β)) [L.LeAtTop] :
    HasProd (f ∘ (↑) : (↑s : Set β) → α) (∏ b ∈ s, f b) L := by
  simpa [prod_attach, Embedding.subtype] using Finset.hasProd_support s f L

/-- If a function `f` is `1` outside of a finite set `s`, then it `HasProd` `∏ b ∈ s, f b`. -/
@[to_additive /-- If a function `f` vanishes outside of a finite set `s`, then it `HasSum`
`∑ b ∈ s, f b`. -/]
/-
**hasProd_prod_support_of_ne_finset_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_prod_support_of_ne_finset_one (hf : forall b in L.support, b ∉ s -
> f b = 1) [L.HasSupport] [DecidablePred (· in L.support)] : HasProd f (∏ b in (
↑s inter L.support).toFinset, f b) L
参数：hf : forall b in L.support, b ∉ s -> f b = 1；· in L.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `SummationFilter.HasSupport.eventually_le_support`：∀ {β : Type u_2} {L : 
SummationFilter β} [self : L.HasSupport], ∀ᶠ (s : Finset β) in L.filter, ↑s ⊆ L.
support
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Finset.prod_congr_of_eq_on_inter`：prod_congr_of_eq_on_inter {ι M : Type*
} {s₁ s₂ : Finset ι} {f g : ι -> M} [CommMonoid M] (h₁ : forall a in s₁, a ∉ s₂ 
-> f a = 1) (h₂ : fora…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem hasProd_prod_support_of_ne_finset_one (hf : ∀ b ∈ L.support, b ∉ s → f b = 1)
    [L.HasSupport] [DecidablePred (· ∈ L.support)] :
    HasProd f (∏ b ∈ (↑s ∩ L.support).toFinset, f b) L := by
  apply tendsto_nhds_of_eventually_eq
  have h1 : ⋂ b ∈ (↑s ∩ L.support), {s | b ∈ s} ∈ L.filter :=
    (L.filter.biInter_mem (Set.toFinite _)).mpr (fun b hb ↦ hb.2)
  filter_upwards [h1, L.eventually_le_support] with t ht ht'
  simp only [Set.mem_iInter] at ht
  apply Finset.prod_congr_of_eq_on_inter <;> grind

/-- If a function `f` is `1` outside of a finite set `s`, then it `HasProd` `∏ b ∈ s, f b`. -/
@[to_additive /-- If a function `f` vanishes outside of a finite set `s`, then it `HasSum`
`∑ b ∈ s, f b`. -/]
/-
**hasProd_prod_of_ne_finset_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasProd_prod_of_ne_finset_one (hf : forall b ∉ s, f b = 1) [L.LeAtTop] : H
asProd f (∏ b in s, f b) L
参数：hf : forall b ∉ s, f b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasProd_subtype_iff_of_mulSupport_subset`：hasProd_subtype_iff_of_mulSupp
ort_subset {s : Set β} (hf : mulSupport f subseteq s) : HasProd (f ∘ (↑) : s -> 
α) a ↔ HasProd f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Function.mulSupport_subset_iff'`：mulSupport_subset_iff' : mulSupport f s
ubseteq s ↔ forall x ∉ s, f x = 1
· 使用定理 `Finset.hasProd`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [i
nst_1 : TopologicalSpace α] (s : Finset β) (f : β → α)   (L : optParam (Summatio
nFil…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `SummationFilter.LeAtTop.le_atTop`：∀ {β : Type u_2} {L : SummationFilter 
β} [self : L.LeAtTop], L.filter ≤ Filter.atTop
-/
theorem hasProd_prod_of_ne_finset_one (hf : ∀ b ∉ s, f b = 1) [L.LeAtTop] :
    HasProd f (∏ b ∈ s, f b) L :=
  ((hasProd_subtype_iff_of_mulSupport_subset <| mulSupport_subset_iff'.2 hf).1 <| s.hasProd f)
    |>.mono_left L.le_atTop

@[to_additive]
/-
**multipliable_of_ne_finset_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliable_of_ne_finset_one (hf : forall b ∉ s, f b = 1) [L.HasSupport] 
: Multipliable f L
参数：hf : forall b ∉ s, f b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `hasProd_prod_support_of_ne_finset_one`：hasProd_prod_support_of_ne_finset
_one (hf : forall b in L.support, b ∉ s -> f b = 1) [L.HasSupport] [DecidablePre
d (· in L.support)] : HasPr…
-/
theorem multipliable_of_ne_finset_one (hf : ∀ b ∉ s, f b = 1) [L.HasSupport] :
    Multipliable f L := by
  classical
  exact (hasProd_prod_support_of_ne_finset_one (fun b _ hb ↦ hf b hb)).multipliable

@[to_additive]
/-
**Multipliable.hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.hasProd (ha : Multipliable f L) : HasProd f (∏'[L] b, f b) L
参数：ha : Multipliable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : CommMonoid α] [inst_1
 : TopologicalSpace α] (f : β → α) (L : SummationFilter β),   tprod f L =     i…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Finset.toFinset_coe`：Finset.toFinset_coe (s : Finset α) [Fintype (s : Se
t α)] : (s : Set α).toFinset = s
· 使用定理 `finprod_eq_prod_of_mulSupport_subset`：finprod_eq_prod_of_mulSupport_subs
et (f : α -> M) {s : Finset α} (h : mulSupport f subseteq s) : ∏ᶠ i, f i = ∏ i i
n s, f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Set.mulSupport_mulIndicator`：mulSupport_mulIndicator : Function.mulSuppo
rt (s.mulIndicator f) = s inter Function.mulSupport f
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `hasProd_prod_support_of_ne_finset_one`：hasProd_prod_support_of_ne_finset
_one (hf : forall b in L.support, b ∉ s -> f b = 1) [L.HasSupport] [DecidablePre
d (· in L.support)] : HasPr…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem Multipliable.hasProd (ha : Multipliable f L) : HasProd f (∏'[L] b, f b) L := by
  -- This is quite delicate because of the fiddly special-casing for finite products.
  classical
  rw [tprod_def, dif_pos ha]
  split_ifs with h h'
  · convert! hasProd_prod_support_of_ne_finset_one (s := h.2.toFinset) (L := L) _ using 2
    · simp only [Set.inter_eq_left.mpr (show ↑h.2.toFinset ⊆ L.support by simp)]
      simp only [Set.Finite.coe_toFinset, Finset.toFinset_coe]
      rw [finprod_eq_prod_of_mulSupport_subset (s := h.2.toFinset)]
      · exact Finset.prod_congr rfl (by simp_all)
      · simp
    · grind [Set.Finite.mem_toFinset, mem_mulSupport]
    · exact h.1
  · exact h'
  · exact ha.choose_spec

variable [T2Space α] [L.NeBot]

@[to_additive]
/-
**HasProd.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.unique {a₁ a₂ : α} : HasProd f a₁ L -> HasProd f a₂ L -> a₁ = a₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
-/
theorem HasProd.unique {a₁ a₂ : α} :
    HasProd f a₁ L → HasProd f a₂ L → a₁ = a₂ := by
  exact tendsto_nhds_unique

@[to_additive]
/-
**HasProd.tprod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b = a
参数：ha : HasProd f a L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.unique`：HasProd.unique {a₁ a₂ : α} : HasProd f a₁ L -> HasProd f
 a₂ L -> a₁ = a₂
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b = a :=
  (Multipliable.hasProd ⟨a, ha⟩).unique ha

@[to_additive]
/-
**Multipliable.hasProd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multipliable.hasProd_iff (h : Multipliable f L) : HasProd f a L ↔ ∏'[L] b,
 f b = a
参数：h : Multipliable f L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem Multipliable.hasProd_iff (h : Multipliable f L) :
    HasProd f a L ↔ ∏'[L] b, f b = a :=
  Iff.intro HasProd.tprod_eq fun eq ↦ eq ▸ h.hasProd

@[to_additive]
/-
**tprod_eq_of_filter_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_eq_of_filter_le {L₁ L₂ : SummationFilter β} [L₁.NeBot] (h : L₁.filte
r <= L₂.filter) (hf : Multipliable f L₂) : ∏'[L₁] b, f b = ∏'[L₂] b, f b
参数：h : L₁.filter <= L₂.filter；hf : Multipliable f L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multipliable.hasProd_iff`：Multipliable.hasProd_iff (h : Multipliable f L
) : HasProd f a L ↔ ∏'[L] b, f b = a
· 使用引理 `Multipliable.mono_filter`：Multipliable.mono_filter {f : β -> α} {L₁ L₂ :
 SummationFilter β} (hf : Multipliable f L₂) (h : L₁.filter <= L₂.filter) : Mult
ipliable f L₁
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem tprod_eq_of_filter_le {L₁ L₂ : SummationFilter β} [L₁.NeBot]
    (h : L₁.filter ≤ L₂.filter) (hf : Multipliable f L₂) : ∏'[L₁] b, f b = ∏'[L₂] b, f b :=
  (hf.mono_filter h).hasProd_iff.mp (hf.hasProd.mono_left h)

@[to_additive]
/-
**tprod_eq_of_multipliable_unconditional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_eq_of_multipliable_unconditional [L.LeAtTop] (hf : Multipliable f) :
 ∏'[L] b, f b = ∏' b, f b
参数：hf : Multipliable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tprod_eq_of_filter_le`：tprod_eq_of_filter_le {L₁ L₂ : SummationFilter β}
 [L₁.NeBot] (h : L₁.filter <= L₂.filter) (hf : Multipliable f L₂) : ∏'[L₁] b, f 
b = ∏'[L₂] …
· 使用定理 `SummationFilter.LeAtTop.le_atTop`：∀ {β : Type u_2} {L : SummationFilter 
β} [self : L.LeAtTop], L.filter ≤ Filter.atTop
-/
theorem tprod_eq_of_multipliable_unconditional [L.LeAtTop] (hf : Multipliable f) :
     ∏'[L] b, f b = ∏' b, f b :=
  tprod_eq_of_filter_le L.le_atTop hf

end HasProd

