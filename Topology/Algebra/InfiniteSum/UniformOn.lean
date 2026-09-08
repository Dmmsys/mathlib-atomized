/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler, Andrew Yang
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.UniformConvergence
public import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Infinite sum and products that converge uniformly

## Main definitions
- `HasProdUniformlyOn f g s` : `∏ i, f i b` converges uniformly on `s` to `g`.
- `HasProdLocallyUniformlyOn f g s` : `∏ i, f i b` converges locally uniformly on `s` to `g`.
- `HasProdUniformly f g` : `∏ i, f i b` converges uniformly to `g`.
- `HasProdLocallyUniformly f g` : `∏ i, f i b` converges locally uniformly to `g`.
-/

@[expose] public section

noncomputable section

open Filter Function

open scoped Topology

variable {α β ι : Type*} [CommMonoid α] {f : ι → β → α} {g : β → α}
  {x : β} {s : Set β} {I : Finset ι} [UniformSpace α]

/-!
## Uniform convergence of sums and products
-/

section UniformlyOn

variable (f g s) in
/-- `HasProdUniformlyOn f g s` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges uniformly on `s` to `g`. -/
@[to_additive /-- `HasSumUniformlyOn f g s` means that the (potentially infinite) sum `∑' i, f i b`
for `b : β` converges uniformly on `s` to `g`. -/]
/-
**HasProdUniformlyOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasProdUniformlyOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def HasProdUniformlyOn : Prop := HasProd (UniformOnFun.ofFun {s} ∘ f) (UniformOnFun.ofFun {s} g)

variable (f g s) in
/-- `MultipliableUniformlyOn f s` means that there is some infinite product to which
`f` converges uniformly on `s`. Use `fun x ↦ ∏' i, f i x` to get the product function. -/
@[to_additive /-- `SummableUniformlyOn f s` means that there is some infinite sum to
which `f` converges uniformly on `s`. Use fun x ↦ ∑' i, f i x to get the sum function. -/]
/-
**MultipliableUniformlyOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MultipliableUniformlyOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MultipliableUniformlyOn : Prop := Multipliable (UniformOnFun.ofFun {s} ∘ f)

@[to_additive]
/-
**MultipliableUniformlyOn.exists** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MultipliableUniformlyOn.exists (h : MultipliableUniformlyOn f s) : exists 
g, HasProdUniformlyOn f g s
参数：h : MultipliableUniformlyOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MultipliableUniformlyOn.exists (h : MultipliableUniformlyOn f s) :
    ∃ g, HasProdUniformlyOn f g s :=
  h

@[to_additive]
/-
**HasProdUniformlyOn.multipliableUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProdUniformlyOn.multipliableUniformlyOn (h : HasProdUniformlyOn f g s) 
: MultipliableUniformlyOn f s
参数：h : HasProdUniformlyOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasProdUniformlyOn.multipliableUniformlyOn (h : HasProdUniformlyOn f g s) :
    MultipliableUniformlyOn f s :=
  ⟨g, h⟩

@[to_additive]
/-
**hasProdUniformlyOn_iff_tendstoUniformlyOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProdUniformlyOn_iff_tendstoUniformlyOn : HasProdUniformlyOn f g s ↔ Ten
dstoUniformlyOn (∏ i in ·, f i ·) g atTop s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_fn`：Finset.prod_fn {α : Type*} {M : α -> Type*} {ι} [forall 
a, CommMonoid (M a)] (s : Finset ι) (g : ι -> forall a, M a) : ∏ c in s, g c = f
un a…
· 使用定理 `SummationFilter.unconditional_filter`：∀ (β : Type u_2), (SummationFilter
.unconditional β).filter = Filter.atTop
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `UniformOnFun.tendsto_iff_tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type 
u_2} {ι : Type u_4} {p : Filter ι} [inst : UniformSpace β] {𝔖 : Set (Set α)}   {
F : ι → UniformOnFun α β 𝔖} {f : …
-/
lemma hasProdUniformlyOn_iff_tendstoUniformlyOn :
    HasProdUniformlyOn f g s ↔ TendstoUniformlyOn (∏ i ∈ ·, f i ·) g atTop s := by
  simpa [HasProdUniformlyOn, HasProd, ← UniformOnFun.ofFun_prod, Finset.prod_fn] using!
    UniformOnFun.tendsto_iff_tendstoUniformlyOn (𝔖 := {s})

@[to_additive]
alias ⟨HasProdUniformlyOn.tendstoUniformlyOn, _⟩ := hasProdUniformlyOn_iff_tendstoUniformlyOn

@[to_additive]
/-
**HasProdUniformlyOn.congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProdUniformlyOn.congr {f' : ι -> β -> α} (h : HasProdUniformlyOn f g s)
 (hff' : forallᶠ (n : Finset ι) in atTop, s.EqOn (∏ i in n, f i ·) (∏ i in n, f'
 i ·)) : HasProdUniformlyOn f' g s
参数：h : HasProdUniformlyOn f g s；hff' : forallᶠ (n : Finset ι) in atTop, s.EqOn (
∏ i in n, f i ·) (∏ i in n, f' i ·)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `hasProdUniformlyOn_iff_tendstoUniformlyOn`：hasProdUniformlyOn_iff_tendst
oUniformlyOn : HasProdUniformlyOn f g s ↔ TendstoUniformlyOn (∏ i in ·, f i ·) g
 atTop s
· 使用定理 `TendstoUniformlyOn.congr`：TendstoUniformlyOn.congr {F' : ι -> α -> β} (h
f : TendstoUniformlyOn F f p s) (hff' : forallᶠ n in p, Set.EqOn (F n) (F' n) s)
 : TendstoUnif…
· 使用定理 `HasProdUniformlyOn.tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} [inst : CommMonoid α] {f : ι → β → α} {g : β → α} {s : Set β}   [i
nst_1 : UniformSpace α],   …
-/
lemma HasProdUniformlyOn.congr {f' : ι → β → α}
    (h : HasProdUniformlyOn f g s)
    (hff' : ∀ᶠ (n : Finset ι) in atTop, s.EqOn (∏ i ∈ n, f i ·) (∏ i ∈ n, f' i ·)) :
    HasProdUniformlyOn f' g s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (h.tendstoUniformlyOn.congr hff')

@[to_additive]
/-
**HasProdUniformlyOn.congr_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProdUniformlyOn.congr_right {g' : β -> α} (h : HasProdUniformlyOn f g s
) (hgg' : s.EqOn g g') : HasProdUniformlyOn f g' s
参数：h : HasProdUniformlyOn f g s；hgg' : s.EqOn g g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `hasProdUniformlyOn_iff_tendstoUniformlyOn`：hasProdUniformlyOn_iff_tendst
oUniformlyOn : HasProdUniformlyOn f g s ↔ TendstoUniformlyOn (∏ i in ·, f i ·) g
 atTop s
· 使用定理 `TendstoUniformlyOn.congr_right`：TendstoUniformlyOn.congr_right {g : α ->
 β} (hf : TendstoUniformlyOn F f p s) (hfg : EqOn f g s) : TendstoUniformlyOn F 
g p s
· 使用定理 `HasProdUniformlyOn.tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} [inst : CommMonoid α] {f : ι → β → α} {g : β → α} {s : Set β}   [i
nst_1 : UniformSpace α],   …
-/
lemma HasProdUniformlyOn.congr_right {g' : β → α}
    (h : HasProdUniformlyOn f g s) (hgg' : s.EqOn g g') :
    HasProdUniformlyOn f g' s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (h.tendstoUniformlyOn.congr_right hgg')

@[to_additive]
/-
**HasProdUniformlyOn.tendstoUniformlyOn_finsetRange** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：HasProdUniformlyOn.tendstoUniformlyOn_finsetRange {f : Nat -> β -> α} (h :
 HasProdUniformlyOn f g s) : TendstoUniformlyOn (∏ i in .range ·, f i ·) g atTop
 s
参数：h : HasProdUniformlyOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_finset_range`：tendsto_finset_range : Tendsto Finset.range
 atTop atTop
· 使用定理 `HasProdUniformlyOn.tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} [inst : CommMonoid α] {f : ι → β → α} {g : β → α} {s : Set β}   [i
nst_1 : UniformSpace α],   …
-/
lemma HasProdUniformlyOn.tendstoUniformlyOn_finsetRange
    {f : ℕ → β → α} (h : HasProdUniformlyOn f g s) :
    TendstoUniformlyOn (∏ i ∈ .range ·, f i ·) g atTop s :=
  (tendsto_finset_range.eventually <| h.tendstoUniformlyOn · ·)

@[to_additive]
/-
**HasProdUniformlyOn.hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProdUniformlyOn.hasProd (h : HasProdUniformlyOn f g s) (hx : x in s) : 
HasProd (f · x) (g x)
参数：h : HasProdUniformlyOn f g s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOn.tendsto_at`：TendstoUniformlyOn.tendsto_at (h : Tendst
oUniformlyOn F f p s) (hx : x in s) : Tendsto (fun n => F n x) p 𝓝 (f x)
· 使用定理 `HasProdUniformlyOn.tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} [inst : CommMonoid α] {f : ι → β → α} {g : β → α} {s : Set β}   [i
nst_1 : UniformSpace α],   …
-/
theorem HasProdUniformlyOn.hasProd (h : HasProdUniformlyOn f g s) (hx : x ∈ s) :
    HasProd (f · x) (g x) :=
  h.tendstoUniformlyOn.tendsto_at hx

@[to_additive]
/-
**HasProdUniformlyOn.tprod_eqOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProdUniformlyOn.tprod_eqOn [T2Space α] (h : HasProdUniformlyOn f g s) :
 s.EqOn (∏' b, f b ·) g
参数：h : HasProdUniformlyOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProdUniformlyOn.hasProd`：HasProdUniformlyOn.hasProd (h : HasProdUnifo
rmlyOn f g s) (hx : x in s) : HasProd (f · x) (g x)
-/
theorem HasProdUniformlyOn.tprod_eqOn [T2Space α] (h : HasProdUniformlyOn f g s) :
    s.EqOn (∏' b, f b ·) g :=
  fun _ hx ↦ (h.hasProd hx).tprod_eq

@[to_additive]
/-
**MultipliableUniformlyOn.multipliable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultipliableUniformlyOn.multipliable (h : MultipliableUniformlyOn f s) (hx
 : x in s) : Multipliable (f · x)
参数：h : MultipliableUniformlyOn f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用引理 `MultipliableUniformlyOn.exists`：MultipliableUniformlyOn.exists (h : Mult
ipliableUniformlyOn f s) : exists g, HasProdUniformlyOn f g s
· 使用定理 `HasProdUniformlyOn.hasProd`：HasProdUniformlyOn.hasProd (h : HasProdUnifo
rmlyOn f g s) (hx : x in s) : HasProd (f · x) (g x)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem MultipliableUniformlyOn.multipliable (h : MultipliableUniformlyOn f s) (hx : x ∈ s) :
    Multipliable (f · x) :=
  (h.exists.choose_spec.hasProd hx).multipliable

@[to_additive]
/-
**MultipliableUniformlyOn.hasProdUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultipliableUniformlyOn.hasProdUniformlyOn (h : MultipliableUniformlyOn f 
s) : HasProdUniformlyOn f (∏' i, f i ·) s
参数：h : MultipliableUniformlyOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MultipliableUniformlyOn.exists`：MultipliableUniformlyOn.exists (h : Mult
ipliableUniformlyOn f s) : exists g, HasProdUniformlyOn f g s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `hasProdUniformlyOn_iff_tendstoUniformlyOn`：hasProdUniformlyOn_iff_tendst
oUniformlyOn : HasProdUniformlyOn f g s ↔ TendstoUniformlyOn (∏ i in ·, f i ·) g
 atTop s
· 使用定理 `TendstoUniformlyOn.congr_inseparable_right`：TendstoUniformlyOn.congr_ins
eparable_right {g : α -> β} (hf : TendstoUniformlyOn F f p s) (hfg : forall x in
 s, Inseparable (f x) (g x)) : T…
· 使用定理 `tendsto_nhds_unique_inseparable`：tendsto_nhds_unique_inseparable {f : Y 
-> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto 
f l (𝓝 b)) : Insepara…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProdUniformlyOn.hasProd`：HasProdUniformlyOn.hasProd (h : HasProdUnifo
rmlyOn f g s) (hx : x in s) : HasProd (f · x) (g x)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
-/
theorem MultipliableUniformlyOn.hasProdUniformlyOn (h : MultipliableUniformlyOn f s) :
    HasProdUniformlyOn f (∏' i, f i ·) s := by
  obtain ⟨g, hg⟩ := h.exists
  have hp := hg
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at hg ⊢
  exact hg.congr_inseparable_right fun x hx =>
    tendsto_nhds_unique_inseparable (hp.hasProd hx) (hp.hasProd hx).multipliable.hasProd

@[to_additive]
/-
**multipliableUniformlyOn_iff_hasProdUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliableUniformlyOn_iff_hasProdUniformlyOn : MultipliableUniformlyOn f
 s ↔ HasProdUniformlyOn f (∏' i, f i ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultipliableUniformlyOn.hasProdUniformlyOn`：MultipliableUniformlyOn.hasP
rodUniformlyOn (h : MultipliableUniformlyOn f s) : HasProdUniformlyOn f (∏' i, f
 i ·) s
· 使用定理 `HasProdUniformlyOn.multipliableUniformlyOn`：HasProdUniformlyOn.multiplia
bleUniformlyOn (h : HasProdUniformlyOn f g s) : MultipliableUniformlyOn f s
-/
theorem multipliableUniformlyOn_iff_hasProdUniformlyOn :
    MultipliableUniformlyOn f s ↔ HasProdUniformlyOn f (∏' i, f i ·) s :=
  ⟨MultipliableUniformlyOn.hasProdUniformlyOn, HasProdUniformlyOn.multipliableUniformlyOn⟩

@[to_additive]
/-
**HasProdUniformlyOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProdUniformlyOn.mono {t : Set β} (h : HasProdUniformlyOn f g t) (hst : 
s subseteq t) : HasProdUniformlyOn f g s
参数：h : HasProdUniformlyOn f g t；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `hasProdUniformlyOn_iff_tendstoUniformlyOn`：hasProdUniformlyOn_iff_tendst
oUniformlyOn : HasProdUniformlyOn f g s ↔ TendstoUniformlyOn (∏ i in ·, f i ·) g
 atTop s
· 使用定理 `TendstoUniformlyOn.mono`：TendstoUniformlyOn.mono (h : TendstoUniformlyOn
 F f p s) (h' : s' subseteq s) : TendstoUniformlyOn F f p s'
· 使用定理 `HasProdUniformlyOn.tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} [inst : CommMonoid α] {f : ι → β → α} {g : β → α} {s : Set β}   [i
nst_1 : UniformSpace α],   …
-/
lemma HasProdUniformlyOn.mono {t : Set β}
    (h : HasProdUniformlyOn f g t) (hst : s ⊆ t) : HasProdUniformlyOn f g s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr <| h.tendstoUniformlyOn.mono hst

@[to_additive]
/-
**MultipliableUniformlyOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MultipliableUniformlyOn.mono {t : Set β} (h : MultipliableUniformlyOn f t)
 (hst : s subseteq t) : MultipliableUniformlyOn f s
参数：h : MultipliableUniformlyOn f t；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProdUniformlyOn.multipliableUniformlyOn`：HasProdUniformlyOn.multiplia
bleUniformlyOn (h : HasProdUniformlyOn f g s) : MultipliableUniformlyOn f s
· 使用引理 `MultipliableUniformlyOn.exists`：MultipliableUniformlyOn.exists (h : Mult
ipliableUniformlyOn f s) : exists g, HasProdUniformlyOn f g s
· 使用引理 `HasProdUniformlyOn.mono`：HasProdUniformlyOn.mono {t : Set β} (h : HasPro
dUniformlyOn f g t) (hst : s subseteq t) : HasProdUniformlyOn f g s
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma MultipliableUniformlyOn.mono {t : Set β}
    (h : MultipliableUniformlyOn f t) (hst : s ⊆ t) : MultipliableUniformlyOn f s :=
  (h.exists.choose_spec.mono hst).multipliableUniformlyOn

end UniformlyOn

section LocallyUniformlyOn
/-!
## Locally uniform convergence of sums and products
-/

variable [TopologicalSpace β]

variable (f g s) in
/-- `HasProdLocallyUniformlyOn f g s` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges locally uniformly on `s` to `g b` (in the sense of
`TendstoLocallyUniformlyOn`). -/
@[to_additive /-- `HasSumLocallyUniformlyOn f g s` means that the (potentially infinite) sum
`∑' i, f i b` for `b : β` converges locally uniformly on `s` to `g b` (in the sense of
`TendstoLocallyUniformlyOn`). -/]
/-
**HasProdLocallyUniformlyOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasProdLocallyUniformlyOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def HasProdLocallyUniformlyOn : Prop := TendstoLocallyUniformlyOn (∏ i ∈ ·, f i ·) g atTop s

variable (f g s) in
/-- `MultipliableLocallyUniformlyOn f s` means that the product `∏' i, f i b` converges locally
uniformly on `s` to something. -/
@[to_additive /-- `SummableLocallyUniformlyOn f s` means that `∑' i, f i b` converges locally
uniformly on `s` to something. -/]
/-
**MultipliableLocallyUniformlyOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MultipliableLocallyUniformlyOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MultipliableLocallyUniformlyOn : Prop := ∃ g, HasProdLocallyUniformlyOn f g s

@[to_additive]
/-
**hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn : HasProdLocallyUn
iformlyOn f g s ↔ TendstoLocallyUniformlyOn (∏ i in ·, f i ·) g atTop s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn :
    HasProdLocallyUniformlyOn f g s ↔ TendstoLocallyUniformlyOn (∏ i ∈ ·, f i ·) g atTop s :=
  Iff.rfl

/-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∏' i, f i b` converges uniformly
to `g`, then the product converges locally uniformly on `s` to `g`. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/
@[to_additive /-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∑' i, f i b`
converges uniformly to `g`, then the sum converges locally uniformly. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/]
/-
**hasProdLocallyUniformlyOn_of_of_forall_exists_nhds** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：hasProdLocallyUniformlyOn_of_of_forall_exists_nhds (h : forall x in s, exi
sts t in 𝓝[s] x, HasProdUniformlyOn f g t) : HasProdLocallyUniformlyOn f g s
参数：h : forall x in s, exists t in 𝓝[s] x, HasProdUniformlyOn f g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tendstoLocallyUniformlyOn_of_forall_exists_nhds`：tendstoLocallyUniformly
On_of_forall_exists_nhds (h : forall x in s, exists t in 𝓝[s] x, TendstoUniforml
yOn F f p t) : TendstoLocallyUniforml…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hasProdLocallyUniformlyOn_of_of_forall_exists_nhds
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, HasProdUniformlyOn f g t) : HasProdLocallyUniformlyOn f g s :=
  tendstoLocallyUniformlyOn_of_forall_exists_nhds <| by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h
/-
**HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact (h : HasProdLoca
llyUniformlyOn f g s) (hs : IsCompact s) : HasProdUniformlyOn f g s
参数：h : HasProdLocallyUniformlyOn f g s；hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `hasProdUniformlyOn_iff_tendstoUniformlyOn`：hasProdUniformlyOn_iff_tendst
oUniformlyOn : HasProdUniformlyOn f g s ↔ TendstoUniformlyOn (∏ i in ·, f i ·) g
 atTop s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact`：tendstoLoca
llyUniformlyOn_iff_tendstoUniformlyOn_of_compact (hs : IsCompact s) : TendstoLoc
allyUniformlyOn F f p s ↔ TendstoUniformlyOn F f …
-/
lemma HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact
    (h : HasProdLocallyUniformlyOn f g s) (hs : IsCompact s) : HasProdUniformlyOn f g s := by
  rwa [hasProdUniformlyOn_iff_tendstoUniformlyOn,
    ← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs]
/-
**HasProdLocallyUniformlyOn.exists_hasProdUniformlyOn** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：HasProdLocallyUniformlyOn.exists_hasProdUniformlyOn [LocallyCompactSpace β
] (h : HasProdLocallyUniformlyOn f g s) (hx : s in 𝓝 x) : exists t in 𝓝[s] x, Ha
sProdUniformlyOn f g t
参数：h : HasProdLocallyUniformlyOn f g s；hx : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `compact_basis_nhds`：compact_basis_nhds [LocallyCompactSpace X] (x : X) :
 (𝓝 x).HasBasis (fun s => s in 𝓝 x ∧ IsCompact s) fun s => s
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用引理 `HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact`：HasProdLocall
yUniformlyOn.hasProdUniformlyOn_of_isCompact (h : HasProdLocallyUniformlyOn f g 
s) (hs : IsCompact s) : HasProdUniformlyOn f g …
· 使用定理 `TendstoLocallyUniformlyOn.mono`：TendstoLocallyUniformlyOn.mono (h : Tend
stoLocallyUniformlyOn F f p s) (h' : s' subseteq s) : TendstoLocallyUniformlyOn 
F f p s'
-/
lemma HasProdLocallyUniformlyOn.exists_hasProdUniformlyOn [LocallyCompactSpace β]
    (h : HasProdLocallyUniformlyOn f g s) (hx : s ∈ 𝓝 x) :
    ∃ t ∈ 𝓝[s] x, HasProdUniformlyOn f g t := by
  obtain ⟨K, ⟨hK1, hK2⟩, hK3⟩ := (compact_basis_nhds x).mem_iff.mp hx
  exact ⟨K, nhdsWithin_le_nhds hK1,
    HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact (h.mono hK3) hK2⟩

@[to_additive]
/-
**HasProdUniformlyOn.hasProdLocallyUniformlyOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProdUniformlyOn.hasProdLocallyUniformlyOn (h : HasProdUniformlyOn f g s
) : HasProdLocallyUniformlyOn f g s
参数：h : HasProdUniformlyOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOn.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β : Type
 u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : 
ι → α → β}   {f : α → β} {s : Set …
-/
lemma HasProdUniformlyOn.hasProdLocallyUniformlyOn (h : HasProdUniformlyOn f g s) :
    HasProdLocallyUniformlyOn f g s := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn, HasProdLocallyUniformlyOn] at *
  exact h.tendstoLocallyUniformlyOn

@[to_additive]
/-
**hasProdLocallyUniformlyOn_of_forall_compact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProdLocallyUniformlyOn_of_forall_compact (hs : IsOpen s) [LocallyCompac
tSpace β] (h : forall K subseteq s, IsCompact K -> HasProdUniformlyOn f g K) : H
asProdLocallyUniformlyOn f g s
参数：hs : IsOpen s；h : forall K subseteq s, IsCompact K -> HasProdUniformlyOn f g 
K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasProdLocallyUniformlyOn.eq_1`：∀ {α : Type u_1} {β : Type u_2} {ι : Typ
e u_3} [inst : CommMonoid α] (f : ι → β → α) (g : β → α) (s : Set β)   [inst_1 :
 UniformSpace α] [in…
· 使用定理 `tendstoLocallyUniformlyOn_iff_forall_isCompact`：tendstoLocallyUniformlyO
n_iff_forall_isCompact [LocallyCompactSpace α] (hs : IsOpen s) : TendstoLocallyU
niformlyOn F f p s ↔ forall K, K sub…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma hasProdLocallyUniformlyOn_of_forall_compact (hs : IsOpen s) [LocallyCompactSpace β]
    (h : ∀ K ⊆ s, IsCompact K → HasProdUniformlyOn f g K) : HasProdLocallyUniformlyOn f g s := by
  rw [HasProdLocallyUniformlyOn, tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
/-
**HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn (h : HasProdLocal
lyUniformlyOn f g s) : MultipliableLocallyUniformlyOn f s
参数：h : HasProdLocallyUniformlyOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
    (h : HasProdLocallyUniformlyOn f g s) : MultipliableLocallyUniformlyOn f s :=
  ⟨g, h⟩

@[to_additive]
/-
**HasProdLocallyUniformlyOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProdLocallyUniformlyOn.mono {t : Set β} (h : HasProdLocallyUniformlyOn 
f g t) (hst : s subseteq t) : HasProdLocallyUniformlyOn f g s
参数：h : HasProdLocallyUniformlyOn f g t；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.mono`：TendstoLocallyUniformlyOn.mono (h : Tend
stoLocallyUniformlyOn F f p s) (h' : s' subseteq s) : TendstoLocallyUniformlyOn 
F f p s'
-/
lemma HasProdLocallyUniformlyOn.mono {t : Set β}
    (h : HasProdLocallyUniformlyOn f g t) (hst : s ⊆ t) : HasProdLocallyUniformlyOn f g s :=
  TendstoLocallyUniformlyOn.mono h hst

@[to_additive]
/-
**MultipliableLocallyUniformlyOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MultipliableLocallyUniformlyOn.mono {t : Set β} (h : MultipliableLocallyUn
iformlyOn f t) (hst : s subseteq t) : MultipliableLocallyUniformlyOn f s
参数：h : MultipliableLocallyUniformlyOn f t；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn`：HasProdLocally
UniformlyOn.multipliableLocallyUniformlyOn (h : HasProdLocallyUniformlyOn f g s)
 : MultipliableLocallyUniformlyOn f s
· 使用引理 `HasProdLocallyUniformlyOn.mono`：HasProdLocallyUniformlyOn.mono {t : Set 
β} (h : HasProdLocallyUniformlyOn f g t) (hst : s subseteq t) : HasProdLocallyUn
iformlyOn f g s
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma MultipliableLocallyUniformlyOn.mono {t : Set β}
    (h : MultipliableLocallyUniformlyOn f t) (hst : s ⊆ t) : MultipliableLocallyUniformlyOn f s :=
  (h.choose_spec.mono hst).multipliableLocallyUniformlyOn

/-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∏' i, f i b` converges uniformly,
then the product converges locally uniformly on `s`. Note that this is not a tautology, and the
converse is only true if the domain is locally compact. -/
@[to_additive /-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∑' i, f i b`
converges uniformly, then the sum converges locally uniformly. Note that this is not a tautology,
and the converse is only true if the domain is locally compact. -/]
/-
**multipliableLocallyUniformlyOn_of_of_forall_exists_nhds** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：multipliableLocallyUniformlyOn_of_of_forall_exists_nhds (h : forall x in s
, exists t in 𝓝[s] x, MultipliableUniformlyOn f t) : MultipliableLocallyUniforml
yOn f s
参数：h : forall x in s, exists t in 𝓝[s] x, MultipliableUniformlyOn f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn`：HasProdLocally
UniformlyOn.multipliableLocallyUniformlyOn (h : HasProdLocallyUniformlyOn f g s)
 : MultipliableLocallyUniformlyOn f s
· 使用引理 `hasProdLocallyUniformlyOn_of_of_forall_exists_nhds`：hasProdLocallyUnifor
mlyOn_of_of_forall_exists_nhds (h : forall x in s, exists t in 𝓝[s] x, HasProdUn
iformlyOn f g t) : HasProdLocallyUniform…
· 使用定理 `MultipliableUniformlyOn.hasProdUniformlyOn`：MultipliableUniformlyOn.hasP
rodUniformlyOn (h : MultipliableUniformlyOn f s) : HasProdUniformlyOn f (∏' i, f
 i ·) s
-/
lemma multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, MultipliableUniformlyOn f t) :
    MultipliableLocallyUniformlyOn f s :=
  (hasProdLocallyUniformlyOn_of_of_forall_exists_nhds <| fun x hx ↦ match h x hx with
  | ⟨t, ht, htr⟩ => ⟨t, ht, htr.hasProdUniformlyOn⟩).multipliableLocallyUniformlyOn
/-
**MultipliableLocallyUniformlyOn.multipliableUniformlyOn_of_isCompact** 是 Mathli
b 中的一个引理，位于命名空间 ``。
形式化陈述：MultipliableLocallyUniformlyOn.multipliableUniformlyOn_of_isCompact (h : M
ultipliableLocallyUniformlyOn f s) (hs : IsCompact s) : MultipliableUniformlyOn 
f s
参数：h : MultipliableLocallyUniformlyOn f s；hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProdUniformlyOn.multipliableUniformlyOn`：HasProdUniformlyOn.multiplia
bleUniformlyOn (h : HasProdUniformlyOn f g s) : MultipliableUniformlyOn f s
· 使用引理 `HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact`：HasProdLocall
yUniformlyOn.hasProdUniformlyOn_of_isCompact (h : HasProdLocallyUniformlyOn f g 
s) (hs : IsCompact s) : HasProdUniformlyOn f g …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma MultipliableLocallyUniformlyOn.multipliableUniformlyOn_of_isCompact
    (h : MultipliableLocallyUniformlyOn f s) (hs : IsCompact s) : MultipliableUniformlyOn f s :=
  (h.choose_spec.hasProdUniformlyOn_of_isCompact hs).multipliableUniformlyOn
/-
**MultipliableLocallyUniformlyOn.exists_multipliableUniformlyOn** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：MultipliableLocallyUniformlyOn.exists_multipliableUniformlyOn [LocallyComp
actSpace β] (h : MultipliableLocallyUniformlyOn f s) (hx : s in 𝓝 x) : exists t 
in 𝓝[s] x, MultipliableUniformlyOn f t
参数：h : MultipliableLocallyUniformlyOn f s；hx : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasProdLocallyUniformlyOn.exists_hasProdUniformlyOn`：HasProdLocallyUnifo
rmlyOn.exists_hasProdUniformlyOn [LocallyCompactSpace β] (h : HasProdLocallyUnif
ormlyOn f g s) (hx : s in 𝓝 x) : exists t…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasProdUniformlyOn.multipliableUniformlyOn`：HasProdUniformlyOn.multiplia
bleUniformlyOn (h : HasProdUniformlyOn f g s) : MultipliableUniformlyOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma MultipliableLocallyUniformlyOn.exists_multipliableUniformlyOn [LocallyCompactSpace β]
    (h : MultipliableLocallyUniformlyOn f s) (hx : s ∈ 𝓝 x) :
    ∃ t ∈ 𝓝[s] x, MultipliableUniformlyOn f t :=
  let H := (h.choose_spec.exists_hasProdUniformlyOn hx).choose_spec
  ⟨_, H.1, H.2.multipliableUniformlyOn⟩

@[to_additive]
/-
**HasProdLocallyUniformlyOn.hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProdLocallyUniformlyOn.hasProd (h : HasProdLocallyUniformlyOn f g s) (h
x : x in s) : HasProd (f · x) (g x)
参数：h : HasProdLocallyUniformlyOn f g s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.tendsto_at`：TendstoLocallyUniformlyOn.tendsto_
at (hf : TendstoLocallyUniformlyOn F f p s) {a : α} (ha : a in s) : Tendsto (fun
 i => F i a) p (𝓝 (f a))
-/
theorem HasProdLocallyUniformlyOn.hasProd (h : HasProdLocallyUniformlyOn f g s) (hx : x ∈ s) :
    HasProd (f · x) (g x) :=
  h.tendsto_at hx

@[to_additive]
/-
**MultipliableLocallyUniformlyOn.multipliable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultipliableLocallyUniformlyOn.multipliable (h : MultipliableLocallyUnifor
mlyOn f s) (hx : x in s) : Multipliable (f · x)
参数：h : MultipliableLocallyUniformlyOn f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProdLocallyUniformlyOn.hasProd`：HasProdLocallyUniformlyOn.hasProd (h 
: HasProdLocallyUniformlyOn f g s) (hx : x in s) : HasProd (f · x) (g x)
-/
theorem MultipliableLocallyUniformlyOn.multipliable
    (h : MultipliableLocallyUniformlyOn f s) (hx : x ∈ s) : Multipliable (f · x) :=
  match h with | ⟨_, hg⟩ => (hg.hasProd hx).multipliable

@[to_additive]
/-
**MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn (h : Multipliable
LocallyUniformlyOn f s) : HasProdLocallyUniformlyOn f (∏' i, f i ·) s
参数：h : MultipliableLocallyUniformlyOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `TendstoLocallyUniformlyOn.congr_inseparable_right`：TendstoLocallyUniform
lyOn.congr_inseparable_right {g : α -> β} (hf : TendstoLocallyUniformlyOn F f p 
s) (hg : forall x in s, Inseparable (f …
· 使用定理 `tendsto_nhds_unique_inseparable`：tendsto_nhds_unique_inseparable {f : Y 
-> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto 
f l (𝓝 b)) : Insepara…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProdLocallyUniformlyOn.hasProd`：HasProdLocallyUniformlyOn.hasProd (h 
: HasProdLocallyUniformlyOn f g s) (hx : x in s) : HasProd (f · x) (g x)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
-/
theorem MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn
    (h : MultipliableLocallyUniformlyOn f s) :
    HasProdLocallyUniformlyOn f (∏' i, f i ·) s :=
  h.elim fun _ hg => hg.congr_inseparable_right fun _ hx =>
    tendsto_nhds_unique_inseparable (hg.hasProd hx) (hg.hasProd hx).multipliable.hasProd

@[to_additive]
/-
**HasProdLocallyUniformlyOn.tprod_eqOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProdLocallyUniformlyOn.tprod_eqOn [T2Space α] (h : HasProdLocallyUnifor
mlyOn f g s) : Set.EqOn (∏' i, f i ·) g s
参数：h : HasProdLocallyUniformlyOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProdLocallyUniformlyOn.hasProd`：HasProdLocallyUniformlyOn.hasProd (h 
: HasProdLocallyUniformlyOn f g s) (hx : x in s) : HasProd (f · x) (g x)
-/
theorem HasProdLocallyUniformlyOn.tprod_eqOn [T2Space α]
    (h : HasProdLocallyUniformlyOn f g s) : Set.EqOn (∏' i, f i ·) g s :=
  fun _ hx ↦ (h.hasProd hx).tprod_eq

@[to_additive]
/-
**MultipliableLocallyUniformlyOn_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MultipliableLocallyUniformlyOn_congr {f f' : ι -> β -> α} (h : forall i, s
.EqOn (f i) (f' i)) (h2 : MultipliableLocallyUniformlyOn f s) : MultipliableLoca
llyUniformlyOn f' s
参数：h : forall i, s.EqOn (f i) (f' i)；h2 : MultipliableLocallyUniformlyOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn`：HasProdLocally
UniformlyOn.multipliableLocallyUniformlyOn (h : HasProdLocallyUniformlyOn f g s)
 : MultipliableLocallyUniformlyOn f s
· 使用定理 `TendstoLocallyUniformlyOn.congr`：TendstoLocallyUniformlyOn.congr {G : ι 
-> α -> β} (hf : TendstoLocallyUniformlyOn F f p s) (hg : forall n, s.EqOn (F n)
 (G n)) : TendstoLoca…
· 使用定理 `MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn`：MultipliableLo
callyUniformlyOn.hasProdLocallyUniformlyOn (h : MultipliableLocallyUniformlyOn f
 s) : HasProdLocallyUniformlyOn f (∏' i, f i ·…
· 使用定理 `eqOn_fun_finsetProd`：eqOn_fun_finsetProd {ι α β : Type*} [CommMonoid α] 
{s : Set β} {f f' : ι -> β -> α} (h : forall (i : ι), Set.EqOn (f i) (f' i) s) (
v : Finse…
-/
lemma MultipliableLocallyUniformlyOn_congr
    {f f' : ι → β → α} (h : ∀ i, s.EqOn (f i) (f' i))
    (h2 : MultipliableLocallyUniformlyOn f s) : MultipliableLocallyUniformlyOn f' s := by
  apply HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  exact (h2.hasProdLocallyUniformlyOn).congr fun v ↦ eqOn_fun_finsetProd h v

@[to_additive]
/-
**HasProdLocallyUniformlyOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProdLocallyUniformlyOn.comp {γ : Type*} [TopologicalSpace γ] {t : Set γ
} (h : HasProdLocallyUniformlyOn f g s) (h' : γ -> β) (hh : Set.MapsTo h' t s) (
chh : ContinuousOn h' t) : HasProdLocallyUniformlyOn (fun i y => f i (h' y)) (g 
∘ h') t
参数：h : HasProdLocallyUniformlyOn f g s；h' : γ -> β；hh : Set.MapsTo h' t s；chh : 
ContinuousOn h' t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.comp`：TendstoLocallyUniformlyOn.comp [Topologi
calSpace γ] {t : Set γ} (h : TendstoLocallyUniformlyOn F f p s) (g : γ -> α) (hg
 : MapsTo g t s) (cg…
-/
theorem HasProdLocallyUniformlyOn.comp {γ : Type*} [TopologicalSpace γ] {t : Set γ}
    (h : HasProdLocallyUniformlyOn f g s) (h' : γ → β) (hh : Set.MapsTo h' t s)
    (chh : ContinuousOn h' t) :
    HasProdLocallyUniformlyOn (fun i y ↦ f i (h' y)) (g ∘ h') t :=
  TendstoLocallyUniformlyOn.comp h h' hh chh

@[to_additive]
/-
**MultipliableLocallyUniformlyOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultipliableLocallyUniformlyOn.comp {γ : Type*} [TopologicalSpace γ] {t : 
Set γ} (h : MultipliableLocallyUniformlyOn f s) (h' : γ -> β) (hh : Set.MapsTo h
' t s) (chh : ContinuousOn h' t) : MultipliableLocallyUniformlyOn (fun i y => f 
i (h' y)) t
参数：h : MultipliableLocallyUniformlyOn f s；h' : γ -> β；hh : Set.MapsTo h' t s；chh
 : ContinuousOn h' t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn`：HasProdLocally
UniformlyOn.multipliableLocallyUniformlyOn (h : HasProdLocallyUniformlyOn f g s)
 : MultipliableLocallyUniformlyOn f s
· 使用定理 `HasProdLocallyUniformlyOn.comp`：HasProdLocallyUniformlyOn.comp {γ : Type
*} [TopologicalSpace γ] {t : Set γ} (h : HasProdLocallyUniformlyOn f g s) (h' : 
γ -> β) (hh : Set.Ma…
· 使用定理 `MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn`：MultipliableLo
callyUniformlyOn.hasProdLocallyUniformlyOn (h : MultipliableLocallyUniformlyOn f
 s) : HasProdLocallyUniformlyOn f (∏' i, f i ·…
-/
theorem MultipliableLocallyUniformlyOn.comp {γ : Type*} [TopologicalSpace γ] {t : Set γ}
    (h : MultipliableLocallyUniformlyOn f s) (h' : γ → β) (hh : Set.MapsTo h' t s)
    (chh : ContinuousOn h' t) : MultipliableLocallyUniformlyOn (fun i y ↦ f i (h' y)) t :=
  (h.hasProdLocallyUniformlyOn.comp h' hh chh).multipliableLocallyUniformlyOn

@[to_additive]
/-
**HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange** 是 Mathlib 中的
一个引理，位于命名空间 ``。
形式化陈述：HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange {f : Nat -
> β -> α} (h : HasProdLocallyUniformlyOn f g s) : TendstoLocallyUniformlyOn (fun
 N b => ∏ i in Finset.range N, f i b) g atTop s
参数：h : HasProdLocallyUniformlyOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn`：hasProdLocallyU
niformlyOn_iff_tendstoLocallyUniformlyOn : HasProdLocallyUniformlyOn f g s ↔ Ten
dstoLocallyUniformlyOn (∏ i in ·, f i ·) g at…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_finset_range`：tendsto_finset_range : Tendsto Finset.range
 atTop atTop
-/
lemma HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
    {f : ℕ → β → α} (h : HasProdLocallyUniformlyOn f g s) :
    TendstoLocallyUniformlyOn (fun N b ↦ ∏ i ∈ Finset.range N, f i b) g atTop s := by
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  intro v hv r hr
  obtain ⟨t, ht, htr⟩ := h v hv r hr
  exact ⟨t, ht, Filter.tendsto_finset_range.eventually htr⟩

@[to_additive]
/-
**multipliableLocallyUniformlyOn_iff_hasProdLocallyUniformlyOn** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：multipliableLocallyUniformlyOn_iff_hasProdLocallyUniformlyOn : Multipliabl
eLocallyUniformlyOn f s ↔ HasProdLocallyUniformlyOn f (∏' i, f i ·) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn`：MultipliableLo
callyUniformlyOn.hasProdLocallyUniformlyOn (h : MultipliableLocallyUniformlyOn f
 s) : HasProdLocallyUniformlyOn f (∏' i, f i ·…
· 使用定理 `HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn`：HasProdLocally
UniformlyOn.multipliableLocallyUniformlyOn (h : HasProdLocallyUniformlyOn f g s)
 : MultipliableLocallyUniformlyOn f s
-/
theorem multipliableLocallyUniformlyOn_iff_hasProdLocallyUniformlyOn :
    MultipliableLocallyUniformlyOn f s ↔ HasProdLocallyUniformlyOn f (∏' i, f i ·) s :=
  ⟨MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn,
    HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn⟩

end LocallyUniformlyOn

section Uniformly

variable (f g) in
/-- `HasProdUniformly f g` means that
the product `∏ i, f i b` converges uniformly (wrt `b`) to `g`. -/
@[to_additive /-- `HasSumUniformly f g` means that
the sum `∑ i, f i b` converges uniformly (wrt `b`) to `g`. -/]
/-
**HasProdUniformly** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasProdUniformly : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def HasProdUniformly : Prop := HasProd (UniformFun.ofFun ∘ f) (UniformFun.ofFun g)

variable (f g) in
/-- `MultipliableUniformly f` means that there is some infinite product to which
`f` converges uniformly. Use `fun x ↦ ∏' i, f i x` to get the product function. -/
@[to_additive /-- `SummableUniformly f` means that there is some infinite sum to which
`f` converges uniformly. Use `fun x ↦ ∑' i, f i x` to get the product function. -/]
/-
**MultipliableUniformly** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MultipliableUniformly : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MultipliableUniformly : Prop := Multipliable (UniformFun.ofFun ∘ f)

@[to_additive]
/-
**MultipliableUniformly.exists** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MultipliableUniformly.exists (h : MultipliableUniformly f) : exists g, Has
ProdUniformly f g
参数：h : MultipliableUniformly f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MultipliableUniformly.exists (h : MultipliableUniformly f) :
    ∃ g, HasProdUniformly f g :=
  h

@[to_additive]
/-
**HasProdUniformly.multipliableUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProdUniformly.multipliableUniformly (h : HasProdUniformly f g) : Multip
liableUniformly f
参数：h : HasProdUniformly f g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasProdUniformly.multipliableUniformly (h : HasProdUniformly f g) :
    MultipliableUniformly f :=
  ⟨g, h⟩

@[to_additive]
/-
**hasProdUniformly_iff_tendstoUniformly** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProdUniformly_iff_tendstoUniformly : HasProdUniformly f g ↔ TendstoUnif
ormly (∏ i in ·, f i ·) g atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_fn`：Finset.prod_fn {α : Type*} {M : α -> Type*} {ι} [forall 
a, CommMonoid (M a)] (s : Finset ι) (g : ι -> forall a, M a) : ∏ c in s, g c = f
un a…
· 使用定理 `SummationFilter.unconditional_filter`：∀ (β : Type u_2), (SummationFilter
.unconditional β).filter = Filter.atTop
· 使用定理 `UniformFun.tendsto_iff_tendstoUniformly`：∀ {α : Type u_1} {β : Type u_2}
 {ι : Type u_4} {p : Filter ι} [inst : UniformSpace β] {F : ι → UniformFun α β} 
  {f : UniformFun α β}, Filte…
-/
lemma hasProdUniformly_iff_tendstoUniformly :
    HasProdUniformly f g ↔ TendstoUniformly (∏ i ∈ ·, f i ·) g atTop := by
  simpa [HasProdUniformly, HasProd, ← UniformFun.ofFun_prod, Finset.prod_fn] using!
    UniformFun.tendsto_iff_tendstoUniformly

@[to_additive]
alias ⟨HasProdUniformly.tendstoUniformly, _⟩ := hasProdUniformly_iff_tendstoUniformly

@[to_additive]
/-
**HasProdUniformly.hasProdUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProdUniformly.hasProdUniformlyOn (h : HasProdUniformly f g) : HasProdUn
iformlyOn f g s
参数：h : HasProdUniformly f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `hasProdUniformlyOn_iff_tendstoUniformlyOn`：hasProdUniformlyOn_iff_tendst
oUniformlyOn : HasProdUniformlyOn f g s ↔ TendstoUniformlyOn (∏ i in ·, f i ·) g
 atTop s
· 使用定理 `TendstoUniformly.tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type u_2} {ι 
: Type u_4} [inst : UniformSpace β] {F : ι → α → β} {f : α → β} {s : Set α}   {p
 : Filter ι}, TendstoUnif…
· 使用定理 `HasProdUniformly.tendstoUniformly`：∀ {α : Type u_1} {β : Type u_2} {ι : 
Type u_3} [inst : CommMonoid α] {f : ι → β → α} {g : β → α}   [inst_1 : UniformS
pace α], HasProdUniform…
-/
theorem HasProdUniformly.hasProdUniformlyOn (h : HasProdUniformly f g) :
    HasProdUniformlyOn f g s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr h.tendstoUniformly.tendstoUniformlyOn

@[to_additive]
/-
**hasProdUniformlyOn_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProdUniformlyOn_univ_iff : HasProdUniformlyOn f g .univ ↔ HasProdUnifor
mly f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasProdUniformlyOn_univ_iff :
    HasProdUniformlyOn f g .univ ↔ HasProdUniformly f g := by
  simp [hasProdUniformly_iff_tendstoUniformly, hasProdUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_univ]

@[to_additive]
/-
**MultipliableUniformly.multipliableUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultipliableUniformly.multipliableUniformlyOn (h : MultipliableUniformly f
) : MultipliableUniformlyOn f s
参数：h : MultipliableUniformly f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProdUniformlyOn.multipliableUniformlyOn`：HasProdUniformlyOn.multiplia
bleUniformlyOn (h : HasProdUniformlyOn f g s) : MultipliableUniformlyOn f s
· 使用引理 `MultipliableUniformly.exists`：MultipliableUniformly.exists (h : Multipli
ableUniformly f) : exists g, HasProdUniformly f g
· 使用定理 `HasProdUniformly.hasProdUniformlyOn`：HasProdUniformly.hasProdUniformlyOn
 (h : HasProdUniformly f g) : HasProdUniformlyOn f g s
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem MultipliableUniformly.multipliableUniformlyOn (h : MultipliableUniformly f) :
    MultipliableUniformlyOn f s :=
  h.exists.choose_spec.hasProdUniformlyOn.multipliableUniformlyOn

@[to_additive]
/-
**multipliableUniformlyOn_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multipliableUniformlyOn_univ_iff : MultipliableUniformlyOn f .univ ↔ Multi
pliableUniformly f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProdUniformly.multipliableUniformly`：HasProdUniformly.multipliableUni
formly (h : HasProdUniformly f g) : MultipliableUniformly f
· 使用引理 `MultipliableUniformlyOn.exists`：MultipliableUniformlyOn.exists (h : Mult
ipliableUniformlyOn f s) : exists g, HasProdUniformlyOn f g s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `hasProdUniformlyOn_univ_iff`：hasProdUniformlyOn_univ_iff : HasProdUnifor
mlyOn f g .univ ↔ HasProdUniformly f g
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `MultipliableUniformly.multipliableUniformlyOn`：MultipliableUniformly.mul
tipliableUniformlyOn (h : MultipliableUniformly f) : MultipliableUniformlyOn f s
-/
lemma multipliableUniformlyOn_univ_iff :
    MultipliableUniformlyOn f .univ ↔ MultipliableUniformly f :=
  ⟨fun h ↦ (hasProdUniformlyOn_univ_iff.mp h.exists.choose_spec).multipliableUniformly,
    MultipliableUniformly.multipliableUniformlyOn⟩

@[to_additive]
/-
**HasProdUniformly.congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProdUniformly.congr {f' : ι -> β -> α} (h : HasProdUniformly f g) (hff'
 : forallᶠ (n : Finset ι) in atTop, forall b, ∏ i in n, f i b = ∏ i in n, f' i b
) : HasProdUniformly f' g
参数：h : HasProdUniformly f g；hff' : forallᶠ (n : Finset ι) in atTop, forall b, ∏ 
i in n, f i b = ∏ i in n, f' i b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `hasProdUniformly_iff_tendstoUniformly`：hasProdUniformly_iff_tendstoUnifo
rmly : HasProdUniformly f g ↔ TendstoUniformly (∏ i in ·, f i ·) g atTop
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `tendstoUniformly_congr`：tendstoUniformly_congr {F' : ι -> α -> β} (hF : 
F =ᶠ[p] F') : TendstoUniformly F f p ↔ TendstoUniformly F' f p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma HasProdUniformly.congr {f' : ι → β → α}
    (h : HasProdUniformly f g)
    (hff' : ∀ᶠ (n : Finset ι) in atTop, ∀ b, ∏ i ∈ n, f i b = ∏ i ∈ n, f' i b) :
    HasProdUniformly f' g := by
  rw [hasProdUniformly_iff_tendstoUniformly] at *
  exact (tendstoUniformly_congr (by simpa only [EventuallyEq, funext_iff])).mp h

@[to_additive]
/-
**HasProdUniformly.tendstoUniformlyOn_finsetRange** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProdUniformly.tendstoUniformlyOn_finsetRange {f : Nat -> β -> α} (h : H
asProdUniformly f g) : TendstoUniformly (∏ i in Finset.range ·, f i ·) g atTop
参数：h : HasProdUniformly f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_finset_range`：tendsto_finset_range : Tendsto Finset.range
 atTop atTop
· 使用定理 `HasProdUniformly.tendstoUniformly`：∀ {α : Type u_1} {β : Type u_2} {ι : 
Type u_3} [inst : CommMonoid α] {f : ι → β → α} {g : β → α}   [inst_1 : UniformS
pace α], HasProdUniform…
-/
lemma HasProdUniformly.tendstoUniformlyOn_finsetRange {f : ℕ → β → α} (h : HasProdUniformly f g) :
    TendstoUniformly (∏ i ∈ Finset.range ·, f i ·) g atTop :=
  (tendsto_finset_range.eventually <| h.tendstoUniformly · ·)

@[to_additive]
/-
**HasProdUniformly.hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProdUniformly.hasProd (h : HasProdUniformly f g) : HasProd (f · x) (g x
)
参数：h : HasProdUniformly f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformly.tendsto_at`：TendstoUniformly.tendsto_at (h : TendstoUni
formly F f p) (x : α) : Tendsto (fun n => F n x) p 𝓝 (f x)
· 使用定理 `HasProdUniformly.tendstoUniformly`：∀ {α : Type u_1} {β : Type u_2} {ι : 
Type u_3} [inst : CommMonoid α] {f : ι → β → α} {g : β → α}   [inst_1 : UniformS
pace α], HasProdUniform…
-/
theorem HasProdUniformly.hasProd (h : HasProdUniformly f g) : HasProd (f · x) (g x) :=
  h.tendstoUniformly.tendsto_at _

@[to_additive]
/-
**MultipliableUniformly.multipliable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultipliableUniformly.multipliable (h : MultipliableUniformly f) : Multipl
iable (f · x)
参数：h : MultipliableUniformly f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用引理 `MultipliableUniformly.exists`：MultipliableUniformly.exists (h : Multipli
ableUniformly f) : exists g, HasProdUniformly f g
· 使用定理 `HasProdUniformly.hasProd`：HasProdUniformly.hasProd (h : HasProdUniformly
 f g) : HasProd (f · x) (g x)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem MultipliableUniformly.multipliable (h : MultipliableUniformly f) : Multipliable (f · x) :=
  h.exists.choose_spec.hasProd.multipliable

@[to_additive]
/-
**MultipliableUniformly.hasProdUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultipliableUniformly.hasProdUniformly (h : MultipliableUniformly f) : Has
ProdUniformly f (∏' i, f i ·)
参数：h : MultipliableUniformly f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `hasProdUniformlyOn_univ_iff`：hasProdUniformlyOn_univ_iff : HasProdUnifor
mlyOn f g .univ ↔ HasProdUniformly f g
· 使用定理 `MultipliableUniformlyOn.hasProdUniformlyOn`：MultipliableUniformlyOn.hasP
rodUniformlyOn (h : MultipliableUniformlyOn f s) : HasProdUniformlyOn f (∏' i, f
 i ·) s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `multipliableUniformlyOn_univ_iff`：multipliableUniformlyOn_univ_iff : Mul
tipliableUniformlyOn f .univ ↔ MultipliableUniformly f
-/
theorem MultipliableUniformly.hasProdUniformly (h : MultipliableUniformly f) :
    HasProdUniformly f (∏' i, f i ·) :=
  hasProdUniformlyOn_univ_iff.1 (multipliableUniformlyOn_univ_iff.2 h).hasProdUniformlyOn

@[to_additive]
/-
**multipliableUniformly_iff_hasProdUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multipliableUniformly_iff_hasProdUniformly : MultipliableUniformly f ↔ Has
ProdUniformly f (∏' i, f i ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultipliableUniformly.hasProdUniformly`：MultipliableUniformly.hasProdUni
formly (h : MultipliableUniformly f) : HasProdUniformly f (∏' i, f i ·)
· 使用定理 `HasProdUniformly.multipliableUniformly`：HasProdUniformly.multipliableUni
formly (h : HasProdUniformly f g) : MultipliableUniformly f
-/
theorem multipliableUniformly_iff_hasProdUniformly :
    MultipliableUniformly f ↔ HasProdUniformly f (∏' i, f i ·) :=
  ⟨MultipliableUniformly.hasProdUniformly, HasProdUniformly.multipliableUniformly⟩

end Uniformly

section LocallyUniformly
/-!
## Locally uniform convergence of sums and products
-/

variable [TopologicalSpace β]

variable (f g) in
/-- `HasProdLocallyUniformly f g` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges locally uniformly to `g b` (in the sense of
`TendstoLocallyUniformly`). -/
@[to_additive /-- `HasSumLocallyUniformly f g` means that the (potentially infinite) sum
`∑' i, f i b` for `b : β` converges locally uniformly to `g b` (in the sense of
`TendstoLocallyUniformly`). -/]
/-
**HasProdLocallyUniformly** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasProdLocallyUniformly : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def HasProdLocallyUniformly : Prop := TendstoLocallyUniformly (∏ i ∈ ·, f i ·) g atTop

variable (f g) in
/-- `MultipliableLocallyUniformly f` means that the product `∏' i, f i b` converges locally
uniformly to something. -/
@[to_additive /-- `SummableLocallyUniformly f` means that `∑' i, f i b` converges locally
uniformly to something. -/]
/-
**MultipliableLocallyUniformly** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MultipliableLocallyUniformly : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MultipliableLocallyUniformly : Prop := ∃ g, HasProdLocallyUniformly f g

@[to_additive]
/-
**MultipliableLocallyUniformly.exists** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MultipliableLocallyUniformly.exists (h : MultipliableLocallyUniformly f) :
 exists g, HasProdLocallyUniformly f g
参数：h : MultipliableLocallyUniformly f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MultipliableLocallyUniformly.exists (h : MultipliableLocallyUniformly f) :
    ∃ g, HasProdLocallyUniformly f g := h

@[to_additive]
/-
**HasProdLocallyUniformly.multipliableLocallyUniformly** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：HasProdLocallyUniformly.multipliableLocallyUniformly (h : HasProdLocallyUn
iformly f g) : MultipliableLocallyUniformly f
参数：h : HasProdLocallyUniformly f g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasProdLocallyUniformly.multipliableLocallyUniformly
    (h : HasProdLocallyUniformly f g) : MultipliableLocallyUniformly f :=
  ⟨g, h⟩

@[to_additive]
/-
**hasProdLocallyUniformly_iff_tendstoLocallyUniformly** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：hasProdLocallyUniformly_iff_tendstoLocallyUniformly : HasProdLocallyUnifor
mly f g ↔ TendstoLocallyUniformly (∏ i in ·, f i ·) g atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasProdLocallyUniformly_iff_tendstoLocallyUniformly :
    HasProdLocallyUniformly f g ↔ TendstoLocallyUniformly (∏ i ∈ ·, f i ·) g atTop :=
  .rfl

@[to_additive]
/-
**HasProdLocallyUniformly.hasProdLocallyUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：HasProdLocallyUniformly.hasProdLocallyUniformlyOn (h : HasProdLocallyUnifo
rmly f g) : HasProdLocallyUniformlyOn f g s
参数：h : HasProdLocallyUniformly f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformly.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β :
 Type u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] 
{F : ι → α → β}   {f : α → β} {s : Set …
-/
theorem HasProdLocallyUniformly.hasProdLocallyUniformlyOn (h : HasProdLocallyUniformly f g) :
    HasProdLocallyUniformlyOn f g s :=
  h.tendstoLocallyUniformlyOn

@[to_additive]
/-
**MultipliableLocallyUniformly.multipliableLocallyUniformlyOn** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：MultipliableLocallyUniformly.multipliableLocallyUniformlyOn (h : Multiplia
bleLocallyUniformly f) : MultipliableLocallyUniformlyOn f s
参数：h : MultipliableLocallyUniformly f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn`：HasProdLocally
UniformlyOn.multipliableLocallyUniformlyOn (h : HasProdLocallyUniformlyOn f g s)
 : MultipliableLocallyUniformlyOn f s
· 使用引理 `MultipliableLocallyUniformly.exists`：MultipliableLocallyUniformly.exists
 (h : MultipliableLocallyUniformly f) : exists g, HasProdLocallyUniformly f g
· 使用定理 `HasProdLocallyUniformly.hasProdLocallyUniformlyOn`：HasProdLocallyUniform
ly.hasProdLocallyUniformlyOn (h : HasProdLocallyUniformly f g) : HasProdLocallyU
niformlyOn f g s
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem MultipliableLocallyUniformly.multipliableLocallyUniformlyOn
    (h : MultipliableLocallyUniformly f) :
    MultipliableLocallyUniformlyOn f s :=
  h.exists.choose_spec.hasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn

/-- If every `x` has a neighbourhood on which `b ↦ ∏' i, f i b` converges uniformly
to `g`, then the product converges locally uniformly to `g`. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/
@[to_additive /-- If every `x` has a neighbourhood on which `b ↦ ∑' i, f i b`
converges uniformly to `g`, then the sum converges locally uniformly. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/]
/-
**hasProdLocallyUniformly_of_of_forall_exists_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProdLocallyUniformly_of_of_forall_exists_nhds (h : forall x, exists t i
n 𝓝 x, HasProdUniformlyOn f g t) : HasProdLocallyUniformly f g
参数：h : forall x, exists t in 𝓝 x, HasProdUniformlyOn f g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tendstoLocallyUniformly_of_forall_exists_nhds`：tendstoLocallyUniformly_o
f_forall_exists_nhds (h : forall x, exists t in 𝓝 x, TendstoUniformlyOn F f p t)
 : TendstoLocallyUniformly F f p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hasProdLocallyUniformly_of_of_forall_exists_nhds
    (h : ∀ x, ∃ t ∈ 𝓝 x, HasProdUniformlyOn f g t) : HasProdLocallyUniformly f g :=
  tendstoLocallyUniformly_of_forall_exists_nhds <| by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
/-
**HasProdUniformly.hasProdLocallyUniformly** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProdUniformly.hasProdLocallyUniformly (h : HasProdUniformly f g) : HasP
rodLocallyUniformly f g
参数：h : HasProdUniformly f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformly.tendstoLocallyUniformly`：∀ {α : Type u_1} {β : Type u_2
} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : ι → 
α → β}   {f : α → β} {p : Filt…
-/
lemma HasProdUniformly.hasProdLocallyUniformly (h : HasProdUniformly f g) :
    HasProdLocallyUniformly f g := by
  simp only [hasProdUniformly_iff_tendstoUniformly, HasProdLocallyUniformly] at *
  exact TendstoUniformly.tendstoLocallyUniformly h

@[to_additive]
/-
**hasProdLocallyUniformly_of_forall_compact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProdLocallyUniformly_of_forall_compact [LocallyCompactSpace β] (h : for
all K, IsCompact K -> HasProdUniformlyOn f g K) : HasProdLocallyUniformly f g
参数：h : forall K, IsCompact K -> HasProdUniformlyOn f g K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasProdLocallyUniformly.eq_1`：∀ {α : Type u_1} {β : Type u_2} {ι : Type 
u_3} [inst : CommMonoid α] (f : ι → β → α) (g : β → α)   [inst_1 : UniformSpace 
α] [inst_2 : Topol…
· 使用引理 `tendstoLocallyUniformly_iff_forall_isCompact`：tendstoLocallyUniformly_if
f_forall_isCompact [LocallyCompactSpace α] : TendstoLocallyUniformly F f p ↔ for
all K : Set α, IsCompact K -> Tend…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma hasProdLocallyUniformly_of_forall_compact [LocallyCompactSpace β]
    (h : ∀ K, IsCompact K → HasProdUniformlyOn f g K) : HasProdLocallyUniformly f g := by
  rw [HasProdLocallyUniformly, tendstoLocallyUniformly_iff_forall_isCompact]
  simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
/-
**multipliableLocallyUniformly_of_of_forall_exists_nhds** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：multipliableLocallyUniformly_of_of_forall_exists_nhds (h : forall x, exist
s t in 𝓝 x, MultipliableUniformlyOn f t) : MultipliableLocallyUniformly f
参数：h : forall x, exists t in 𝓝 x, MultipliableUniformlyOn f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProdLocallyUniformly.multipliableLocallyUniformly`：HasProdLocallyUnif
ormly.multipliableLocallyUniformly (h : HasProdLocallyUniformly f g) : Multiplia
bleLocallyUniformly f
· 使用引理 `hasProdLocallyUniformly_of_of_forall_exists_nhds`：hasProdLocallyUniforml
y_of_of_forall_exists_nhds (h : forall x, exists t in 𝓝 x, HasProdUniformlyOn f 
g t) : HasProdLocallyUniformly f g
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MultipliableUniformlyOn.hasProdUniformlyOn`：MultipliableUniformlyOn.hasP
rodUniformlyOn (h : MultipliableUniformlyOn f s) : HasProdUniformlyOn f (∏' i, f
 i ·) s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma multipliableLocallyUniformly_of_of_forall_exists_nhds
    (h : ∀ x, ∃ t ∈ 𝓝 x, MultipliableUniformlyOn f t) :
    MultipliableLocallyUniformly f :=
  hasProdLocallyUniformly_of_of_forall_exists_nhds
    (fun x => (h x).imp fun _ ht => ⟨ht.1, ht.2.hasProdUniformlyOn⟩)
    |>.multipliableLocallyUniformly

@[to_additive]
/-
**HasProdLocallyUniformly.hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasProdLocallyUniformly.hasProd (h : HasProdLocallyUniformly f g) : HasPro
d (f · x) (g x)
参数：h : HasProdLocallyUniformly f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.tendsto_at`：TendstoLocallyUniformlyOn.tendsto_
at (hf : TendstoLocallyUniformlyOn F f p s) {a : α} (ha : a in s) : Tendsto (fun
 i => F i a) p (𝓝 (f a))
· 使用定理 `TendstoLocallyUniformly.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β :
 Type u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] 
{F : ι → α → β}   {f : α → β} {s : Set …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem HasProdLocallyUniformly.hasProd (h : HasProdLocallyUniformly f g) : HasProd (f · x) (g x) :=
  h.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)

@[to_additive]
/-
**MultipliableLocallyUniformly.multipliable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultipliableLocallyUniformly.multipliable (h : MultipliableLocallyUniforml
y f) : Multipliable (f · x)
参数：h : MultipliableLocallyUniformly f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProdLocallyUniformly.hasProd`：HasProdLocallyUniformly.hasProd (h : Ha
sProdLocallyUniformly f g) : HasProd (f · x) (g x)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem MultipliableLocallyUniformly.multipliable
    (h : MultipliableLocallyUniformly f) : Multipliable (f · x) :=
  h.choose_spec.hasProd.multipliable

@[to_additive]
/-
**MultipliableLocallyUniformly.hasProdLocallyUniformly** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：MultipliableLocallyUniformly.hasProdLocallyUniformly (h : MultipliableLoca
llyUniformly f) : HasProdLocallyUniformly f (∏' i, f i ·)
参数：h : MultipliableLocallyUniformly f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `TendstoLocallyUniformly.congr_inseparable_right`：TendstoLocallyUniformly
.congr_inseparable_right {g : α -> β} (hf : TendstoLocallyUniformly F f p) (hg :
 forall x, Inseparable (f x) (g x)) :…
· 使用定理 `tendsto_nhds_unique_inseparable`：tendsto_nhds_unique_inseparable {f : Y 
-> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto 
f l (𝓝 b)) : Insepara…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasProdLocallyUniformly.hasProd`：HasProdLocallyUniformly.hasProd (h : Ha
sProdLocallyUniformly f g) : HasProd (f · x) (g x)
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
-/
theorem MultipliableLocallyUniformly.hasProdLocallyUniformly
    (h : MultipliableLocallyUniformly f) :
    HasProdLocallyUniformly f (∏' i, f i ·) :=
  h.elim fun _ hg => hg.congr_inseparable_right fun _ =>
    tendsto_nhds_unique_inseparable hg.hasProd hg.hasProd.multipliable.hasProd

@[to_additive]
/-
**multipliableLocallyUniformly_iff_hasProdLocallyUniformly** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：multipliableLocallyUniformly_iff_hasProdLocallyUniformly : MultipliableLoc
allyUniformly f ↔ HasProdLocallyUniformly f (∏' i, f i ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultipliableLocallyUniformly.hasProdLocallyUniformly`：MultipliableLocall
yUniformly.hasProdLocallyUniformly (h : MultipliableLocallyUniformly f) : HasPro
dLocallyUniformly f (∏' i, f i ·)
· 使用定理 `HasProdLocallyUniformly.multipliableLocallyUniformly`：HasProdLocallyUnif
ormly.multipliableLocallyUniformly (h : HasProdLocallyUniformly f g) : Multiplia
bleLocallyUniformly f
-/
theorem multipliableLocallyUniformly_iff_hasProdLocallyUniformly :
    MultipliableLocallyUniformly f ↔ HasProdLocallyUniformly f (∏' i, f i ·) :=
  ⟨MultipliableLocallyUniformly.hasProdLocallyUniformly,
    HasProdLocallyUniformly.multipliableLocallyUniformly⟩

@[to_additive]
/-
**HasProdLocallyUniformly.tendstoLocallyUniformly_finsetRange** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：HasProdLocallyUniformly.tendstoLocallyUniformly_finsetRange {f : Nat -> β 
-> α} (h : HasProdLocallyUniformly f g) : TendstoLocallyUniformly (∏ i in Finset
.range ·, f i ·) g atTop
参数：h : HasProdLocallyUniformly f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange`：HasProd
LocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange {f : Nat -> β -> α} (h 
: HasProdLocallyUniformlyOn f g s) : TendstoLocallyUn…
· 使用定理 `HasProdLocallyUniformly.hasProdLocallyUniformlyOn`：HasProdLocallyUniform
ly.hasProdLocallyUniformlyOn (h : HasProdLocallyUniformly f g) : HasProdLocallyU
niformlyOn f g s
-/
lemma HasProdLocallyUniformly.tendstoLocallyUniformly_finsetRange
    {f : ℕ → β → α} (h : HasProdLocallyUniformly f g) :
    TendstoLocallyUniformly (∏ i ∈ Finset.range ·, f i ·) g atTop := by
  simpa only [tendstoLocallyUniformlyOn_univ] using
    (h.hasProdLocallyUniformlyOn (s := .univ)).tendstoLocallyUniformlyOn_finsetRange

end LocallyUniformly

