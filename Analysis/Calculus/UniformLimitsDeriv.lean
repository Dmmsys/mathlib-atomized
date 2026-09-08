/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Order.Filter.Curry

/-!
# Swapping limits and derivatives via uniform convergence

The purpose of this file is to prove that the derivative of the pointwise limit of a sequence of
functions is the pointwise limit of the functions' derivatives when the derivatives converge
_uniformly_. The formal statement appears as `hasFDerivAt_of_tendstoLocallyUniformlyOn`.

## Main statements

* `uniformCauchySeqOnFilter_of_fderiv`: If
    1. `f : ℕ → E → G` is a sequence of functions which have derivatives
       `f' : ℕ → E → (E →L[𝕜] G)` on a neighborhood of `x`,
    2. the functions `f` converge at `x`, and
    3. the derivatives `f'` form a Cauchy sequence uniformly on a neighborhood of `x`,
  then the `f` form a Cauchy sequence _uniformly_ on a neighborhood of `x`
* `hasFDerivAt_of_tendstoUniformlyOnFilter` : Suppose (1), (2), and (3) above are true. Let
  `g` (resp. `g'`) be the limiting function of the `f` (resp. `g'`). Then `f'` is the derivative of
  `g` on a neighborhood of `x`
* `hasFDerivAt_of_tendstoUniformlyOn`: An often-easier-to-use version of the above theorem when
  *all* the derivatives exist and functions converge on a common open set and the derivatives
  converge uniformly there.

Each of the above statements also has variations that support `deriv` instead of `fderiv`.

## Implementation notes

Our technique for proving the main result is the famous "`ε / 3` proof." In words, you can find it
explained, for instance, at [this StackExchange post](https://math.stackexchange.com/questions/214218/uniform-convergence-of-derivatives-tao-14-2-7).
The subtlety is that we want to prove that the difference quotients of the `g` converge to the `g'`.
That is, we want to prove something like:

```
∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x), |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

To do so, we will need to introduce a pair of quantifiers

```lean
∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ δ > 0, ∀ y ∈ B_δ(x), |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

So how do we write this in terms of filters? Well, the initial definition of the derivative is

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (𝓝 x) (𝓝 0)
```

There are two ways we might introduce `n`. We could do:

```lean
∀ᶠ (n : ℕ) in atTop, Tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (𝓝 x) (𝓝 0)
```

but this is equivalent to the quantifier order `∃ N, ∀ n ≥ N, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x)`,
which _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is _not_ equivalent to it. On the other hand, we might
try

```lean
Tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (atTop ×ˢ 𝓝 x) (𝓝 0)
```

but this is equivalent to the quantifier order `∀ ε > 0, ∃ N, ∃ δ > 0, ∀ n ≥ N, ∀ y ∈ B_δ(x)`, which
again _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is not equivalent to it.

So to get the quantifier order we want, we need to introduce a new filter construction, which we
call a "curried filter"

```lean
Tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (atTop.curry (𝓝 x)) (𝓝 0)
```

Then the above implications are `Filter.Tendsto.curry` and
`Filter.Tendsto.mono_left Filter.curry_le_prod`. We will use both of these deductions as part of
our proof.

We note that if you loosen the assumptions of the main theorem then the proof becomes quite a bit
easier. In particular, if you assume there is a common neighborhood `s` where all of the three
assumptions of `hasFDerivAt_of_tendstoUniformlyOnFilter` hold and that the `f'` are
continuous, then you can avoid the mean value theorem and much of the work around curried filters.

## Tags

uniform convergence, limits of derivatives
-/

public section


open Filter

open scoped uniformity Filter Topology

section LimitsOfDerivatives

variable {ι : Type*} {l : Filter ι} {E : Type*} [NormedAddCommGroup E] {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedSpace 𝕜 E] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : ι → E → G}
  {g : E → G} {f' : ι → E → E →L[𝕜] G} {g' : E → E →L[𝕜] G} {x : E}

/-- If a sequence of functions real or complex functions are eventually differentiable on a
neighborhood of `x`, they are Cauchy _at_ `x`, and their derivatives
are a uniform Cauchy sequence in a neighborhood of `x`, then the functions form a uniform Cauchy
sequence in a neighborhood of `x`. -/
/-
**uniformCauchySeqOnFilter_of_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformCauchySeqOnFilter_of_fderiv (hf' : UniformCauchySeqOnFilter f' l (𝓝
 x)) (hf : forallᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2) 
(hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOnFilter f l (𝓝 x)
参数：hf' : UniformCauchySeqOnFilter f' l (𝓝 x)；hf : forallᶠ n : ι × E in l ×ˢ 𝓝 x,
 HasFDerivAt (f n.1) (f' n.1 n.2) n.2；hfg : Cauchy (map (fun n => f n x) l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter
_zero`：∀ {ι : Type u_2} {κ : Type u_3} {G : Type u_6} [inst : SeminormedAddGroup
 G] {f : ι → κ → G} {l : Filter ι}   {l' : Filter κ},   UniformCauc…
· 使用定理 `Metric.tendstoUniformlyOnFilter_iff`：tendstoUniformlyOnFilter_iff {F : ι
 -> β -> α} {f : β -> α} {p : Filter ι} {p' : Filter β} : TendstoUniformlyOnFilt
er F f p p' ↔ forall ε > …
· 使用定理 `Filter.Eventually.diag_of_prod_right`：∀ {α : Type u_1} {γ : Type u_3} {f
 : Filter α} {g : Filter γ} {p : α × γ × γ → Prop},   (∀ᶠ (x : α × γ × γ) in f ×
ˢ g ×ˢ g, p x) → ∀ᶠ (x : α…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_swap4_prod`：tendsto_swap4_prod {h : Filter γ} {k : Filter
 δ} : Tendsto (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f 
×ˢ g) ×ˢ (h ×ˢ …
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_prod_iff`：eventually_prod_iff {p : α × β -> Prop} : (f
orallᶠ x in f ×ˢ g, p x) ↔ exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exist
s pb : β -> Prop…
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_lt_iff_lt_one_right`：mul_lt_iff_lt_one_right [PosMulStrictMono α] [P
osMulReflectLT α] (a0 : 0 < a) : a * b < a ↔ b < 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
If a sequence of functions real or complex functions are eventually differentiab
le on a
neighborhood of `x`, they are Cauchy _at_ `x`, and their derivatives
are a uniform Cauchy sequence in a neighborhood of `x`, then the functions form 
a uniform Cauchy
sequence in a neighborhood of `x`.
-/
theorem uniformCauchySeqOnFilter_of_fderiv (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
    (hf : ∀ᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOnFilter f l (𝓝 x) := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero] at hf' ⊢
  suffices
    TendstoUniformlyOnFilter (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0
        (l ×ˢ l) (𝓝 x) ∧
      TendstoUniformlyOnFilter (fun (n : ι × ι) (_ : E) => f n.1 x - f n.2 x) 0 (l ×ˢ l) (𝓝 x) by
    have := this.1.neg.add this.2.neg
    rw [neg_zero, add_zero] at this
    apply this.congr (.of_forall (fun x ↦ by simp; abel))
  constructor
  · -- This inequality follows from the mean value theorem. To apply it, we will need to shrink our
    -- neighborhood to small enough ball
    rw [Metric.tendstoUniformlyOnFilter_iff] at hf' ⊢
    intro ε hε
    have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
    obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 ((hf' ε hε).and this)
    obtain ⟨R, hR, hR'⟩ := Metric.nhds_basis_ball.eventually_iff.mp d
    let r := min 1 R
    have hr : 0 < r := by simp [r, hR]
    have hr' : ∀ ⦃y : E⦄, y ∈ Metric.ball x r → c y := fun y hy =>
      hR' (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _))
    have hxy : ∀ y : E, y ∈ Metric.ball x r → ‖y - x‖ < 1 := by
      intro y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact lt_of_lt_of_le hy (min_le_left _ _)
    have hxyε : ∀ y : E, y ∈ Metric.ball x r → ε * ‖y - x‖ < ε := by
      intro y hy
      exact (mul_lt_iff_lt_one_right hε.lt).mpr (hxy y hy)
    -- With a small ball in hand, apply the mean value theorem
    refine
      eventually_prod_iff.mpr
        ⟨_, b, (· ∈ Metric.ball x r),
          eventually_mem_set.mpr (Metric.nhds_basis_ball.mem_of_mem hr), fun {n} hn {y} hy => ?_⟩
    simp only [Pi.zero_apply, dist_zero_left, norm_neg_add] at e ⊢
    refine lt_of_le_of_lt ?_ (hxyε y hy)
    exact
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).hasFDerivWithinAt)
        (fun y hy => (e hn (hr' hy)).1.le) (convex_ball x r) (Metric.mem_ball_self hr) hy
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine Metric.tendstoUniformlyOnFilter_iff.mpr fun ε hε => ?_
    obtain ⟨t, ht, ht'⟩ := (Metric.cauchy_iff.mp hfg).2 ε hε
    exact
      eventually_prod_iff.mpr
        ⟨fun n : ι × ι => f n.1 x ∈ t ∧ f n.2 x ∈ t,
          eventually_prod_iff.mpr ⟨_, ht, _, ht, fun {n} hn {n'} hn' => ⟨hn, hn'⟩⟩,
          fun _ => True,
          by simp,
          fun {n} hn {y} _ => by simpa [norm_sub_rev, dist_eq_norm] using ht' _ hn.1 _ hn.2⟩

/-- A variant of the second fundamental theorem of calculus (FTC-2): If a sequence of functions
between real or complex normed spaces are differentiable on a ball centered at `x`, they
form a Cauchy sequence _at_ `x`, and their derivatives are Cauchy uniformly on the ball, then the
functions form a uniform Cauchy sequence on the ball.

NOTE: The fact that we work on a ball is typically all that is necessary to work with power series
and Dirichlet series (our primary use case). However, this can be generalized by replacing the ball
with any connected, bounded, open set and replacing uniform convergence with local uniform
convergence. See `cauchy_map_of_uniformCauchySeqOn_fderiv`.
-/
/-
**uniformCauchySeqOn_ball_of_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformCauchySeqOn_ball_of_fderiv {r : Real} (hf' : UniformCauchySeqOn f' 
l (Metric.ball x r)) (hf : forall n : ι, forall y : E, y in Metric.ball x r -> H
asFDerivAt (f n) (f' n y) y) (hfg : Cauchy (map (fun n => f n x) l)) : UniformCa
uchySeqOn f l (Metric.ball x r)
参数：hf' : UniformCauchySeqOn f' l (Metric.ball x r)；hf : forall n : ι, forall y :
 E, y in Metric.ball x r -> HasFDerivAt (f n) (f' n y) y；hfg : Cauchy (map (fun 
n => f n x) l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchy_map_iff`：cauchy_map_iff {l : Filter β} {f : β -> α} : Cauchy (l.m
ap f) ↔ NeBot l ∧ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ball_eq_empty`：ball_eq_empty : ball x ε = ∅ ↔ ε <= 0
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Filter.prod.instNeBot`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g
 : Filter β} [hf : f.NeBot] [hg : g.NeBot], (f ×ˢ g).NeBot
· 使用定理 `SeminormedAddGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_zero`：∀ {ι 
: Type u_2} {κ : Type u_3} {G : Type u_6} [inst : SeminormedAddGroup G] {f : ι →
 κ → G} {s : Set κ} {l : Filter ι},   UniformCauchySeqO…
· 使用定理 `Metric.tendstoUniformlyOn_iff`：tendstoUniformlyOn_iff {F : ι -> β -> α} 
{f : β -> α} {p : Filter ι} {s : Set β} : TendstoUniformlyOn F f p s ↔ forall ε 
> 0, forallᶠ n in p…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `exists_pos_mul_lt`：exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : exist
s c : α, 0 < c ∧ b * c < a
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LT.lt.gt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a < b → b > a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`：norm_image_sub_le_o
f_norm_hasFDerivWithin_le (hf : forall x in s, HasFDerivWithinAt f (f' x) s x) (
bound : forall x in s, ‖f' x‖ <= C) (hs :…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `HasFDerivAt.sub`：HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDer
ivAt g g' x) : HasFDerivAt (f - g) (f' - g') x
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
A variant of the second fundamental theorem of calculus (FTC-2): If a sequence o
f functions
between real or complex normed spaces are differentiable on a ball centered at `
x`, they
form a Cauchy sequence _at_ `x`, and their derivatives are Cauchy uniformly on t
he ball, then the
functions form a uniform Cauchy sequence on the ball.

NOTE: The fact that we work on a ball is typically all that is necessary to work
 with power series
and Dirichlet series (our primary use case). However, this can be generalized by
 replacing the ball
with any connected, bounded, open set and replacing uniform convergence with loc
al uniform
convergence. See `cauchy_map_of_uniformCauchySeqOn_fderiv`.
-/
theorem uniformCauchySeqOn_ball_of_fderiv {r : ℝ} (hf' : UniformCauchySeqOn f' l (Metric.ball x r))
    (hf : ∀ n : ι, ∀ y : E, y ∈ Metric.ball x r → HasFDerivAt (f n) (f' n y) y)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOn f l (Metric.ball x r) := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  have : NeBot l := (cauchy_map_iff.1 hfg).1
  rcases le_or_gt r 0 with (hr | hr)
  · simp only [Metric.ball_eq_empty.2 hr, UniformCauchySeqOn, Set.mem_empty_iff_false,
      IsEmpty.forall_iff, eventually_const, imp_true_iff]
  rw [SeminormedAddGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_zero] at hf' ⊢
  suffices
    TendstoUniformlyOn (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0
        (l ×ˢ l) (Metric.ball x r) ∧
      TendstoUniformlyOn (fun (n : ι × ι) (_ : E) => f n.1 x - f n.2 x) 0
        (l ×ˢ l) (Metric.ball x r) by
    have := this.1.neg.add this.2.neg
    rw [neg_zero, add_zero] at this
    refine this.congr ?_
    filter_upwards with n z _ using (by simp; abel)
  constructor
  · -- This inequality follows from the mean value theorem
    rw [Metric.tendstoUniformlyOn_iff] at hf' ⊢
    intro ε hε
    obtain ⟨q, hqpos, hq⟩ : ∃ q : ℝ, 0 < q ∧ q * r < ε := by
      simp_rw [mul_comm]
      exact exists_pos_mul_lt hε.lt r
    apply (hf' q hqpos.gt).mono
    intro n hn y hy
    simp_rw [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg, norm_neg_add] at hn ⊢
    have mvt :=
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => ((hf n.1 z hz).sub (hf n.2 z hz)).hasFDerivWithinAt) (fun z hz => (hn z hz).le)
        (convex_ball x r) (Metric.mem_ball_self hr) hy
    refine lt_of_le_of_lt mvt ?_
    have : q * ‖y - x‖ < q * r :=
      mul_lt_mul' rfl.le (by simpa only [dist_eq_norm] using Metric.mem_ball.mp hy) (norm_nonneg _)
        hqpos
    exact this.trans hq
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨t, ht, ht'⟩ := (Metric.cauchy_iff.mp hfg).2 ε hε
    rw [eventually_prod_iff]
    refine ⟨fun n => f n x ∈ t, ht, fun n => f n x ∈ t, ht, ?_⟩
    intro n hn n' hn' z _
    rw [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg, ← dist_eq_norm]
    exact ht' _ hn _ hn'

/-- If a sequence of functions between real or complex normed spaces are differentiable on a
preconnected open set, they form a Cauchy sequence _at_ `x`, and their derivatives are Cauchy
uniformly on the set, then the functions form a Cauchy sequence at any point in the set. -/
/-
**cauchy_map_of_uniformCauchySeqOn_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchy_map_of_uniformCauchySeqOn_fderiv {s : Set E} (hs : IsOpen s) (h's :
 IsPreconnected s) (hf' : UniformCauchySeqOn f' l s) (hf : forall n : ι, forall 
y : E, y in s -> HasFDerivAt (f n) (f' n y) y) {x₀ x : E} (hx₀ : x₀ in s) (hx : 
x in s) (hfg : Cauchy (map (fun n => f n x₀) l)) : Cauchy (map (fun n => f n x) 
l)
参数：hs : IsOpen s；h's : IsPreconnected s；hf' : UniformCauchySeqOn f' l s；hf : for
all n : ι, forall y : E, y in s -> HasFDerivAt (f n) (f' n y) y；hx₀ : x₀ in s；hx
 : x in s；hfg : Cauchy (map (fun n => f n x₀) l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchy_map_iff`：cauchy_map_iff {l : Filter β} {f : β -> α} : Cauchy (l.m
ap f) ↔ NeBot l ∧ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α)
· 使用定理 `UniformCauchySeqOn.cauchy_map`：UniformCauchySeqOn.cauchy_map [hp : NeBot
 p] (hf : UniformCauchySeqOn F p s) (hx : x in s) : Cauchy (map (fun i => F i x)
 p)
· 使用定理 `uniformCauchySeqOn_ball_of_fderiv`：uniformCauchySeqOn_ball_of_fderiv {r 
: Real} (hf' : UniformCauchySeqOn f' l (Metric.ball x r)) (hf : forall n : ι, fo
rall y : E, y in Metric…
· 使用定理 `UniformCauchySeqOn.mono`：UniformCauchySeqOn.mono (hf : UniformCauchySeqO
n F p s) (hss' : s' subseteq s) : UniformCauchySeqOn F p s'
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Metric.ball_subset_ball'`：ball_subset_ball' (h : ε₁ + dist x y <= ε₂) : 
ball x ε₁ subseteq ball y ε₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
If a sequence of functions between real or complex normed spaces are differentia
ble on a
preconnected open set, they form a Cauchy sequence _at_ `x`, and their derivativ
es are Cauchy
uniformly on the set, then the functions form a Cauchy sequence at any point in 
the set.
-/
theorem cauchy_map_of_uniformCauchySeqOn_fderiv {s : Set E} (hs : IsOpen s) (h's : IsPreconnected s)
    (hf' : UniformCauchySeqOn f' l s) (hf : ∀ n : ι, ∀ y : E, y ∈ s → HasFDerivAt (f n) (f' n y) y)
    {x₀ x : E} (hx₀ : x₀ ∈ s) (hx : x ∈ s) (hfg : Cauchy (map (fun n => f n x₀) l)) :
    Cauchy (map (fun n => f n x) l) := by
  have : NeBot l := (cauchy_map_iff.1 hfg).1
  let t := { y | y ∈ s ∧ Cauchy (map (fun n => f n y) l) }
  suffices H : s ⊆ t from (H hx).2
  have A : ∀ x ε, x ∈ t → Metric.ball x ε ⊆ s → Metric.ball x ε ⊆ t := fun x ε xt hx y hy =>
    ⟨hx hy,
      (uniformCauchySeqOn_ball_of_fderiv (hf'.mono hx) (fun n y hy => hf n y (hx hy))
            xt.2).cauchy_map
        hy⟩
  have open_t : IsOpen t := by
    rw [Metric.isOpen_iff]
    intro x hx
    rcases Metric.isOpen_iff.1 hs x hx.1 with ⟨ε, εpos, hε⟩
    exact ⟨ε, εpos, A x ε hx hε⟩
  have st_nonempty : (s ∩ t).Nonempty := ⟨x₀, hx₀, ⟨hx₀, hfg⟩⟩
  suffices H : closure t ∩ s ⊆ t from h's.subset_of_closure_inter_subset open_t st_nonempty H
  rintro x ⟨xt, xs⟩
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ), ε > 0 ∧ Metric.ball x ε ⊆ s := Metric.isOpen_iff.1 hs x xs
  obtain ⟨y, yt, hxy⟩ : ∃ (y : E), y ∈ t ∧ dist x y < ε / 2 :=
    Metric.mem_closure_iff.1 xt _ (half_pos εpos)
  have B : Metric.ball y (ε / 2) ⊆ Metric.ball x ε := by
    apply Metric.ball_subset_ball'; rw [dist_comm]; linarith
  exact A y (ε / 2) yt (B.trans hε) (Metric.mem_ball.2 hxy)

/-- If `f_n → g` pointwise and the derivatives `(f_n)' → h` _uniformly_ converge, then
in fact for a fixed `y`, the difference quotients `‖z - y‖⁻¹ • (f_n z - f_n y)` converge
_uniformly_ to `‖z - y‖⁻¹ • (g z - g y)` -/
/-
**difference_quotients_converge_uniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：difference_quotients_converge_uniformly {E : Type*} [NormedAddCommGroup E]
 {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] {G : Type*} [NormedAddCommGroup G] [No
rmedSpace 𝕜 G] {f : ι -> E -> G} {g : E -> G} {f' : ι -> E -> E ->L[𝕜] G} {g' : 
E -> E ->L[𝕜] G} {x : E} (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x)) (hf : fo
rallᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2) (hfg : forall
ᶠ y : E in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) : TendstoUniformlyOnFilter
 (fun n : ι => fun y : E =
参数：hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x)；hf : forallᶠ n : ι × E in l ×ˢ 𝓝
 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2；hfg : forallᶠ y : E in 𝓝 x, Tendsto (fu
n n => f n y) l (𝓝 (g y))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto`：UniformCau
chySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto (hF : UniformCauchySeqOnFilte
r F p p') (hF' : forallᶠ x : α in p', Tendsto (fun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter
_zero`：∀ {ι : Type u_2} {κ : Type u_3} {G : Type u_6} [inst : SeminormedAddGroup
 G] {f : ι → κ → G} {l : Filter ι}   {l' : Filter κ},   UniformCauc…
· 使用定理 `Metric.tendstoUniformlyOnFilter_iff`：tendstoUniformlyOnFilter_iff {F : ι
 -> β -> α} {f : β -> α} {p : Filter ι} {p' : Filter β} : TendstoUniformlyOnFilt
er F f p p' ↔ forall ε > …
· 使用定理 `TendstoUniformlyOnFilter.uniformCauchySeqOnFilter`：TendstoUniformlyOnFil
ter.uniformCauchySeqOnFilter (hF : TendstoUniformlyOnFilter F f p p') : UniformC
auchySeqOnFilter F p p'
· 使用定理 `exists_pos_rat_lt`：exists_pos_rat_lt {x : K} (x0 : 0 < x) : exists q : R
at, 0 < q ∧ (q : K) < x
· 使用定理 `Filter.Eventually.diag_of_prod_right`：∀ {α : Type u_1} {γ : Type u_3} {f
 : Filter α} {g : Filter γ} {p : α × γ × γ → Prop},   (∀ᶠ (x : α × γ × γ) in f ×
ˢ g ×ˢ g, p x) → ∀ᶠ (x : α…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_swap4_prod`：tendsto_swap4_prod {h : Filter γ} {k : Filter
 δ} : Tendsto (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f 
×ˢ g) ×ˢ (h ×ˢ …
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_prod_iff`：eventually_prod_iff {p : α × β -> Prop} : (f
orallᶠ x in f ×ˢ g, p x) ↔ exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exist
s pb : β -> Prop…
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_mem_set`：eventually_mem_set {s : Set α} {l : Filter α}
 : (forallᶠ x in l, x in s) ↔ s in l
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_left`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 
dist 0 a = ‖a‖
· 使用定理 `norm_neg_add`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), ‖-a + b‖ = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
If `f_n → g` pointwise and the derivatives `(f_n)' → h` _uniformly_ converge, th
en
in fact for a fixed `y`, the difference quotients `‖z - y‖⁻¹ • (f_n z - f_n y)` 
converge
_uniformly_ to `‖z - y‖⁻¹ • (g z - g y)`
-/
theorem difference_quotients_converge_uniformly
    {E : Type*} [NormedAddCommGroup E] {𝕜 : Type*} [RCLike 𝕜]
    [NormedSpace 𝕜 E] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : ι → E → G}
    {g : E → G} {f' : ι → E → E →L[𝕜] G} {g' : E → E →L[𝕜] G} {x : E}
    (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : ∀ᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : ∀ᶠ y : E in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) :
    TendstoUniformlyOnFilter (fun n : ι => fun y : E => (‖y - x‖⁻¹ : 𝕜) • (f n y - f n x))
      (fun y : E => (‖y - x‖⁻¹ : 𝕜) • (g y - g x)) l (𝓝 x) := by
  let A : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  refine
    UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto ?_
      ((hfg.and (eventually_const.mpr hfg.self_of_nhds)).mono fun y hy =>
        (hy.1.sub hy.2).const_smul _)
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero]
  rw [Metric.tendstoUniformlyOnFilter_iff]
  have hfg' := hf'.uniformCauchySeqOnFilter
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero] at hfg'
  rw [Metric.tendstoUniformlyOnFilter_iff] at hfg'
  intro ε hε
  obtain ⟨q, hqpos, hqε⟩ := exists_pos_rat_lt hε
  specialize hfg' (q : ℝ) (by simp [hqpos])
  have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
  obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 (hfg'.and this)
  obtain ⟨r, hr, hr'⟩ := Metric.nhds_basis_ball.eventually_iff.mp d
  rw [eventually_prod_iff]
  refine
    ⟨_, b, (· ∈ Metric.ball x r),
      eventually_mem_set.mpr (Metric.nhds_basis_ball.mem_of_mem hr), fun {n} hn {y} hy => ?_⟩
  simp only [Pi.zero_apply, dist_zero_left]
  rw [norm_neg_add, ← smul_sub, norm_smul, norm_inv, RCLike.norm_coe_norm]
  refine lt_of_le_of_lt ?_ hqε
  by_cases hyz' : x = y; · simp [hyz', hqpos.le]
  have hyz : 0 < ‖y - x‖ := by rw [norm_pos_iff]; intro hy'; exact hyz' (eq_of_sub_eq_zero hy').symm
  rw [inv_mul_le_iff₀ hyz, mul_comm, sub_sub_sub_comm]
  simp only [Pi.zero_apply, dist_zero_left, norm_neg_add] at e
  refine
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).hasFDerivWithinAt)
      (fun y hy => (e hn (hr' hy)).1.le) (convex_ball x r) (Metric.mem_ball_self hr) hy

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit at `x`.

In words the assumptions mean the following:
  * `hf'`: The `f'` converge "uniformly at" `x` to `g'`. This does not mean that the `f' n` even
    converge away from `x`!
  * `hf`: For all `(y, n)` with `y` sufficiently close to `x` and `n` sufficiently large, `f' n` is
    the derivative of `f n`
  * `hfg`: The `f n` converge pointwise to `g` on a neighborhood of `x` -/
/-
**hasFDerivAt_of_tendstoUniformlyOnFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_of_tendstoUniformlyOnFilter [NeBot l] (hf' : TendstoUniformlyO
nFilter f' g' l (𝓝 x)) (hf : forallᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) 
(f' n.1 n.2) n.2) (hfg : forallᶠ y in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y)))
 : HasFDerivAt g (g' x) x
参数：hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x)；hf : forallᶠ n : ι × E in l ×ˢ 𝓝
 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2；hfg : forallᶠ y in 𝓝 x, Tendsto (fun n 
=> f n y) l (𝓝 (g y))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasFDerivAt_iff_tendsto`：hasFDerivAt_iff_tendsto : HasFDerivAt f f' x ↔ 
Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝 x) (𝓝 0)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `RCLike.norm_ofReal`：norm_ofReal (r : Real) : ‖(r : K)‖ = |r|
· 使用定理 `RCLike.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : K) = (r : K)⁻
¹
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FunLike.coe_sub`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Sub F] [inst_2 : Sub β]   [IsSubApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `_private.Mathlib.Analysis.Calculus.UniformLimitsDeriv.0.hasFDerivAt_of_t
endstoUniformlyOnFilter._abel_1_3`：∀ {ι : Type u_2} {E : Type u_3} [inst : Norme
dAddCommGroup E] {𝕜 : Type u_4} [inst_1 : NontriviallyNormedField 𝕜]   [inst_2 :
 NormedSpace 𝕜 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
（共 121 条，此处仅展示前 30 条）

--- 原说明 ---
`(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit at `x`.

In words the assumptions mean the following:
  * `hf'`: The `f'` converge "uniformly at" `x` to `g'`. This does not mean that
 the `f' n` even
    converge away from `x`!
  * `hf`: For all `(y, n)` with `y` sufficiently close to `x` and `n` sufficient
ly large, `f' n` is
    the derivative of `f n`
  * `hfg`: The `f n` converge pointwise to `g` on a neighborhood of `x`
-/
theorem hasFDerivAt_of_tendstoUniformlyOnFilter [NeBot l]
    (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : ∀ᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : ∀ᶠ y in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) : HasFDerivAt g (g' x) x := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  -- The proof strategy follows several steps:
  --   1. The quantifiers in the definition of the derivative are
  --      `∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x)`. We will introduce a quantifier in the middle:
  --      `∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ δ > 0, ∀ y ∈ B_δ(x)` which will allow us to introduce the
  --      `f(') n`
  --   2. The order of the quantifiers `hfg` are opposite to what we need. We will be able to swap
  --      the quantifiers using the uniform convergence assumption
  rw [hasFDerivAt_iff_tendsto]
  -- Introduce extra quantifier via curried filters
  suffices
    Tendsto (fun y : ι × E => ‖y.2 - x‖⁻¹ * ‖g y.2 - g x - (g' x) (y.2 - x)‖)
      (l.curry (𝓝 x)) (𝓝 0) by
    rw [Metric.tendsto_nhds] at this ⊢
    intro ε hε
    specialize this ε hε
    rw [eventually_curry_iff] at this
    simp only at this
    exact (eventually_const.mp this).mono (by simp only [imp_self, forall_const])
  -- With the new quantifier in hand, we can perform the famous `ε/3` proof. Specifically,
  -- we will break up the limit (the difference functions minus the derivative go to 0) into 3:
  --   * The difference functions of the `f n` converge *uniformly* to the difference functions
  --     of the `g n`
  --   * The `f' n` are the derivatives of the `f n`
  --   * The `f' n` converge to `g'` at `x`
  conv =>
    congr
    ext
    rw [← abs_norm, ← abs_inv, ← @RCLike.norm_ofReal 𝕜 _ _, RCLike.ofReal_inv, ← norm_smul]
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  have :
    (fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (g' x) (a.2 - x))) =
      ((fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (f a.1 a.2 - f a.1 x))) +
          fun a : ι × E =>
          (‖a.2 - x‖⁻¹ : 𝕜) • (f a.1 a.2 - f a.1 x - ((f' a.1 x) a.2 - (f' a.1 x) x))) +
        fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (f' a.1 x - g' x) (a.2 - x) := by
    ext; simp only [Pi.add_apply]; rw [← smul_add, ← smul_add]; congr
    simp only [map_sub, sub_add_sub_cancel, FunLike.coe_sub, Pi.sub_apply]
    abel
  simp_rw [this]
  have : 𝓝 (0 : G) = 𝓝 (0 + 0 + 0) := by simp only [add_zero]
  rw [this]
  refine Tendsto.add (Tendsto.add ?_ ?_) ?_
  · have := difference_quotients_converge_uniformly hf' hf hfg
    rw [Metric.tendstoUniformlyOnFilter_iff] at this
    rw [Metric.tendsto_nhds]
    intro ε hε
    apply ((this ε hε).filter_mono curry_le_prod).mono
    intro n hn
    rw [dist_eq_norm] at hn ⊢
    convert! hn using 2
    module
  · -- (Almost) the definition of the derivatives
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [eventually_curry_iff]
    refine hf.curry.mono fun n hn => ?_
    have := hn.self_of_nhds
    rw [hasFDerivAt_iff_tendsto, Metric.tendsto_nhds] at this
    refine (this ε hε).mono fun y hy => ?_
    rw [dist_eq_norm] at hy ⊢
    simp only [sub_zero, map_sub, norm_mul, norm_inv, norm_norm] at hy ⊢
    rw [norm_smul, norm_inv, RCLike.norm_coe_norm]
    exact hy
  · -- hfg' after specializing to `x` and applying the definition of the operator norm
    refine Tendsto.mono_left ?_ curry_le_prod
    have h1 : Tendsto (fun n : ι × E => g' n.2 - f' n.1 n.2) (l ×ˢ 𝓝 x) (𝓝 0) := by
      rw [Metric.tendstoUniformlyOnFilter_iff] at hf'
      exact Metric.tendsto_nhds.mpr fun ε hε => by simpa [dist_eq_norm] using hf' ε hε
    have h2 : Tendsto (fun n : ι => g' x - f' n x) l (𝓝 0) := by
      rw [Metric.tendsto_nhds] at h1 ⊢
      exact fun ε hε => (h1 ε hε).curry.mono fun n hn => hn.self_of_nhds
    refine squeeze_zero_norm ?_
      (tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_fst.comp (h2.prodMap tendsto_id)))
    intro n
    simp_rw [norm_smul, norm_inv, RCLike.norm_coe_norm]
    by_cases hx : x = n.2; · simp [hx]
    have hnx : 0 < ‖n.2 - x‖ := by
      rw [norm_pos_iff]; intro hx'; exact hx (eq_of_sub_eq_zero hx').symm
    rw [inv_mul_le_iff₀ hnx, mul_comm]
    simp only [Function.comp_apply, Prod.map_apply']
    rw [norm_sub_rev]
    exact (f' n.1 x - g' x).le_opNorm (n.2 - x)
/-
**hasFDerivAt_of_tendstoLocallyUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_of_tendstoLocallyUniformlyOn [NeBot l] {s : Set E} (hs : IsOpe
n s) (hf' : TendstoLocallyUniformlyOn f' g' l s) (hf : forall n, forall x in s, 
HasFDerivAt (f n) (f' n x) x) (hfg : forall x in s, Tendsto (fun n => f n x) l (
𝓝 (g x))) (hx : x in s) : HasFDerivAt g (g' x) x
参数：hs : IsOpen s；hf' : TendstoLocallyUniformlyOn f' g' l s；hf : forall n, forall
 x in s, HasFDerivAt (f n) (f' n x) x；hfg : forall x in s, Tendsto (fun n => f n
 x) l (𝓝 (g x))；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `hasFDerivAt_of_tendstoUniformlyOnFilter`：hasFDerivAt_of_tendstoUniformly
OnFilter [NeBot l] (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x)) (hf : forallᶠ 
n : ι × E in l ×ˢ 𝓝 x, HasFDe…
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendstoLocallyUniformlyOn_iff_filter`：tendstoLocallyUniformlyOn_iff_filt
er : TendstoLocallyUniformlyOn F f p s ↔ forall x in s, TendstoUniformlyOnFilter
 F f p (𝓝[s] x)
-/
theorem hasFDerivAt_of_tendstoLocallyUniformlyOn [NeBot l] {s : Set E} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn f' g' l s) (hf : ∀ n, ∀ x ∈ s, HasFDerivAt (f n) (f' n x) x)
    (hfg : ∀ x ∈ s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) :
    HasFDerivAt g (g' x) x := by
  have h1 : s ∈ 𝓝 x := hs.mem_nhds hx
  have h3 : Set.univ ×ˢ s ∈ l ×ˢ 𝓝 x := by simp only [h1, prod_mem_prod_iff, univ_mem, and_self_iff]
  have h4 : ∀ᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_of_mem h3 fun ⟨n, z⟩ ⟨_, hz⟩ => hf n z hz
  refine hasFDerivAt_of_tendstoUniformlyOnFilter ?_ h4 (eventually_of_mem h1 hfg)
  simpa [IsOpen.nhdsWithin_eq hs hx] using tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

/-- A slight variant of `hasFDerivAt_of_tendstoLocallyUniformlyOn` with the assumption stated
in terms of `DifferentiableOn` rather than `HasFDerivAt`. This makes a few proofs nicer in
complex analysis where holomorphicity is assumed but the derivative is not known a priori. -/
/-
**hasFDerivAt_of_tendsto_locally_uniformly_on'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_of_tendsto_locally_uniformly_on' [NeBot l] {s : Set E} (hs : I
sOpen s) (hf' : TendstoLocallyUniformlyOn (fderiv 𝕜 ∘ f) g' l s) (hf : forall n,
 DifferentiableOn 𝕜 (f n) s) (hfg : forall x in s, Tendsto (fun n => f n x) l (𝓝
 (g x))) (hx : x in s) : HasFDerivAt g (g' x) x
参数：hs : IsOpen s；hf' : TendstoLocallyUniformlyOn (fderiv 𝕜 ∘ f) g' l s；hf : fora
ll n, DifferentiableOn 𝕜 (f n) s；hfg : forall x in s, Tendsto (fun n => f n x) l
 (𝓝 (g x))；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `hasFDerivAt_of_tendstoLocallyUniformlyOn`：hasFDerivAt_of_tendstoLocallyU
niformlyOn [NeBot l] {s : Set E} (hs : IsOpen s) (hf' : TendstoLocallyUniformlyO
n f' g' l s) (hf : forall n, f…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
A slight variant of `hasFDerivAt_of_tendstoLocallyUniformlyOn` with the assumpti
on stated
in terms of `DifferentiableOn` rather than `HasFDerivAt`. This makes a few proof
s nicer in
complex analysis where holomorphicity is assumed but the derivative is not known
 a priori.
-/
theorem hasFDerivAt_of_tendsto_locally_uniformly_on' [NeBot l] {s : Set E} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn (fderiv 𝕜 ∘ f) g' l s) (hf : ∀ n, DifferentiableOn 𝕜 (f n) s)
    (hfg : ∀ x ∈ s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) :
    HasFDerivAt g (g' x) x := by
  refine hasFDerivAt_of_tendstoLocallyUniformlyOn hs hf' (fun n z hz => ?_) hfg hx
  exact ((hf n z hz).differentiableAt (hs.mem_nhds hz)).hasFDerivAt

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit on an open set containing `x`. -/
/-
**hasFDerivAt_of_tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_of_tendstoUniformlyOn [NeBot l] {s : Set E} (hs : IsOpen s) (h
f' : TendstoUniformlyOn f' g' l s) (hf : forall n : ι, forall x : E, x in s -> H
asFDerivAt (f n) (f' n x) x) (hfg : forall x : E, x in s -> Tendsto (fun n => f 
n x) l (𝓝 (g x))) (hx : x in s) : HasFDerivAt g (g' x) x
参数：hs : IsOpen s；hf' : TendstoUniformlyOn f' g' l s；hf : forall n : ι, forall x 
: E, x in s -> HasFDerivAt (f n) (f' n x) x；hfg : forall x : E, x in s -> Tendst
o (fun n => f n x) l (𝓝 (g x))；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `hasFDerivAt_of_tendstoLocallyUniformlyOn`：hasFDerivAt_of_tendstoLocallyU
niformlyOn [NeBot l] {s : Set E} (hs : IsOpen s) (hf' : TendstoLocallyUniformlyO
n f' g' l s) (hf : forall n, f…
· 使用定理 `TendstoUniformlyOn.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β : Type
 u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : 
ι → α → β}   {f : α → β} {s : Set …

--- 原说明 ---
`(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit on an open set containing `x`.
-/
theorem hasFDerivAt_of_tendstoUniformlyOn [NeBot l] {s : Set E} (hs : IsOpen s)
    (hf' : TendstoUniformlyOn f' g' l s)
    (hf : ∀ n : ι, ∀ x : E, x ∈ s → HasFDerivAt (f n) (f' n x) x)
    (hfg : ∀ x : E, x ∈ s → Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) :
    HasFDerivAt g (g' x) x :=
  hasFDerivAt_of_tendstoLocallyUniformlyOn hs hf'.tendstoLocallyUniformlyOn hf hfg hx

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit. -/
/-
**hasFDerivAt_of_tendstoUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_of_tendstoUniformly [NeBot l] (hf' : TendstoUniformly f' g' l)
 (hf : forall n : ι, forall x : E, HasFDerivAt (f n) (f' n x) x) (hfg : forall x
 : E, Tendsto (fun n => f n x) l (𝓝 (g x))) (x : E) : HasFDerivAt g (g' x) x
参数：hf' : TendstoUniformly f' g' l；hf : forall n : ι, forall x : E, HasFDerivAt (
f n) (f' n x) x；hfg : forall x : E, Tendsto (fun n => f n x) l (𝓝 (g x))；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_univ`：tendstoUniformlyOn_univ : TendstoUniformlyOn F 
f p univ ↔ TendstoUniformly F f p
· 使用定理 `hasFDerivAt_of_tendstoUniformlyOn`：hasFDerivAt_of_tendstoUniformlyOn [Ne
Bot l] {s : Set E} (hs : IsOpen s) (hf' : TendstoUniformlyOn f' g' l s) (hf : fo
rall n : ι, forall x : …
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
`(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit.
-/
theorem hasFDerivAt_of_tendstoUniformly [NeBot l] (hf' : TendstoUniformly f' g' l)
    (hf : ∀ n : ι, ∀ x : E, HasFDerivAt (f n) (f' n x) x)
    (hfg : ∀ x : E, Tendsto (fun n => f n x) l (𝓝 (g x))) (x : E) : HasFDerivAt g (g' x) x := by
  have hf : ∀ n : ι, ∀ x : E, x ∈ Set.univ → HasFDerivAt (f n) (f' n x) x := by simp [hf]
  have hfg : ∀ x : E, x ∈ Set.univ → Tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.univ := by rwa [tendstoUniformlyOn_univ]
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_univ hf' hf hfg (Set.mem_univ x)

end LimitsOfDerivatives

section deriv

/-! ### `deriv` versions of above theorems

In this section, we provide `deriv` equivalents of the `fderiv` lemmas in the previous section.
-/


variable {ι : Type*} {l : Filter ι} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {G : Type*} [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {f : ι → 𝕜 → G} {g : 𝕜 → G} {f' : ι → 𝕜 → G} {g' : 𝕜 → G} {x : 𝕜}

/-- If our derivatives converge uniformly, then the Fréchet derivatives converge uniformly -/
/-
**UniformCauchySeqOnFilter.one_smulRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOnFilter.one_smulRight {l' : Filter 𝕜} (hf' : UniformCauch
ySeqOnFilter f' l l') : UniformCauchySeqOnFilter (fun n z => (1 : 𝕜 ->L[𝕜] 𝕜).sm
ulRight (f' n z)) l l'
参数：hf' : UniformCauchySeqOnFilter f' l l'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.smulRightL_apply_apply`：∀ (𝕜 : Type u_1) (E : Type u
_4) (Fₗ : Type u_7) [inst : SeminormedAddCommGroup E] [inst_1 : SeminormedAddCom
mGroup Fₗ]   [inst_2 : Nontrivia…
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…

--- 原说明 ---
If our derivatives converge uniformly, then the Fréchet derivatives converge uni
formly
-/
theorem UniformCauchySeqOnFilter.one_smulRight {l' : Filter 𝕜}
    (hf' : UniformCauchySeqOnFilter f' l l') :
    UniformCauchySeqOnFilter (fun n => fun z => (1 : 𝕜 →L[𝕜] 𝕜).smulRight (f' n z)) l l' := by
  intro u hu
  simpa using hf' _ ((ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous hu)

variable [IsRCLikeNormedField 𝕜]
/-
**uniformCauchySeqOnFilter_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformCauchySeqOnFilter_of_deriv (hf' : UniformCauchySeqOnFilter f' l (𝓝 
x)) (hf : forallᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2) (h
fg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOnFilter f l (𝓝 x)
参数：hf' : UniformCauchySeqOnFilter f' l (𝓝 x)；hf : forallᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x,
 HasDerivAt (f n.1) (f' n.1 n.2) n.2；hfg : Cauchy (map (fun n => f n x) l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `uniformCauchySeqOnFilter_of_fderiv`：uniformCauchySeqOnFilter_of_fderiv (
hf' : UniformCauchySeqOnFilter f' l (𝓝 x)) (hf : forallᶠ n : ι × E in l ×ˢ 𝓝 x, 
HasFDerivAt (f n.1) (f' …
· 使用定理 `UniformCauchySeqOnFilter.one_smulRight`：UniformCauchySeqOnFilter.one_smu
lRight {l' : Filter 𝕜} (hf' : UniformCauchySeqOnFilter f' l l') : UniformCauchyS
eqOnFilter (fun n z => (1 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem uniformCauchySeqOnFilter_of_deriv (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
    (hf : ∀ᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOnFilter f l (𝓝 x) := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf
  exact uniformCauchySeqOnFilter_of_fderiv hf'.one_smulRight hf hfg
/-
**uniformCauchySeqOn_ball_of_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformCauchySeqOn_ball_of_deriv {r : Real} (hf' : UniformCauchySeqOn f' l
 (Metric.ball x r)) (hf : forall n : ι, forall y : 𝕜, y in Metric.ball x r -> Ha
sDerivAt (f n) (f' n y) y) (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauc
hySeqOn f l (Metric.ball x r)
参数：hf' : UniformCauchySeqOn f' l (Metric.ball x r)；hf : forall n : ι, forall y :
 𝕜, y in Metric.ball x r -> HasDerivAt (f n) (f' n y) y；hfg : Cauchy (map (fun n
 => f n x) l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuous.comp_uniformCauchySeqOn`：UniformContinuous.comp_unifor
mCauchySeqOn [UniformSpace γ] {g : β -> γ} (hg : UniformContinuous g) (hf : Unif
ormCauchySeqOn F p s) : Uniform…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
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
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…
· 使用定理 `uniformCauchySeqOn_ball_of_fderiv`：uniformCauchySeqOn_ball_of_fderiv {r 
: Real} (hf' : UniformCauchySeqOn f' l (Metric.ball x r)) (hf : forall n : ι, fo
rall y : E, y in Metric…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem uniformCauchySeqOn_ball_of_deriv {r : ℝ} (hf' : UniformCauchySeqOn f' l (Metric.ball x r))
    (hf : ∀ n : ι, ∀ y : 𝕜, y ∈ Metric.ball x r → HasDerivAt (f n) (f' n y) y)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOn f l (Metric.ball x r) := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf
  have hf' :
    UniformCauchySeqOn (fun n => fun z => (1 : 𝕜 →L[𝕜] 𝕜).smulRight (f' n z)) l
      (Metric.ball x r) :=
    (ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous.comp_uniformCauchySeqOn hf'
  exact uniformCauchySeqOn_ball_of_fderiv hf' hf hfg
/-
**hasDerivAt_of_tendstoUniformlyOnFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_of_tendstoUniformlyOnFilter [NeBot l] (hf' : TendstoUniformlyOn
Filter f' g' l (𝓝 x)) (hf : forallᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f
' n.1 n.2) n.2) (hfg : forallᶠ y in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) :
 HasDerivAt g (g' x) x
参数：hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x)；hf : forallᶠ n : ι × 𝕜 in l ×ˢ 𝓝
 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2；hfg : forallᶠ y in 𝓝 x, Tendsto (fun n =
> f n y) l (𝓝 (g y))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuous.comp_tendstoUniformlyOnFilter`：UniformContinuous.comp_
tendstoUniformlyOnFilter [UniformSpace γ] {g : β -> γ} (hg : UniformContinuous g
) (h : TendstoUniformlyOnFilter F f p…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
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
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…
· 使用定理 `hasFDerivAt_of_tendstoUniformlyOnFilter`：hasFDerivAt_of_tendstoUniformly
OnFilter [NeBot l] (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x)) (hf : forallᶠ 
n : ι × E in l ×ˢ 𝓝 x, HasFDe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem hasDerivAt_of_tendstoUniformlyOnFilter [NeBot l]
    (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : ∀ᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : ∀ᶠ y in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) : HasDerivAt g (g' x) x := by
  -- The first part of the proof rewrites `hf` and the goal to be functions so that Lean
  -- can recognize them when we apply `hasFDerivAt_of_tendstoUniformlyOnFilter`
  let F' n z := (1 : 𝕜 →L[𝕜] 𝕜).smulRight (f' n z)
  let G' z := (1 : 𝕜 →L[𝕜] 𝕜).smulRight (g' z)
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf ⊢
  have hf' : TendstoUniformlyOnFilter F' G' l (𝓝 x) :=
    (ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous.comp_tendstoUniformlyOnFilter hf'
  exact hasFDerivAt_of_tendstoUniformlyOnFilter hf' hf hfg
/-
**hasDerivAt_of_tendstoLocallyUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_of_tendstoLocallyUniformlyOn [NeBot l] {s : Set 𝕜} (hs : IsOpen
 s) (hf' : TendstoLocallyUniformlyOn f' g' l s) (hf : forallᶠ n in l, forall x i
n s, HasDerivAt (f n) (f' n x) x) (hfg : forall x in s, Tendsto (fun n => f n x)
 l (𝓝 (g x))) (hx : x in s) : HasDerivAt g (g' x) x
参数：hs : IsOpen s；hf' : TendstoLocallyUniformlyOn f' g' l s；hf : forallᶠ n in l, 
forall x in s, HasDerivAt (f n) (f' n x) x；hfg : forall x in s, Tendsto (fun n =
> f n x) l (𝓝 (g x))；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_prod_iff`：eventually_prod_iff {p : α × β -> Prop} : (f
orallᶠ x in f ×ˢ g, p x) ↔ exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exist
s pb : β -> Prop…
· 使用定理 `hasDerivAt_of_tendstoUniformlyOnFilter`：hasDerivAt_of_tendstoUniformlyOn
Filter [NeBot l] (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x)) (hf : forallᶠ n 
: ι × 𝕜 in l ×ˢ 𝓝 x, HasDeri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendstoLocallyUniformlyOn_iff_filter`：tendstoLocallyUniformlyOn_iff_filt
er : TendstoLocallyUniformlyOn F f p s ↔ forall x in s, TendstoUniformlyOnFilter
 F f p (𝓝[s] x)
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
-/
theorem hasDerivAt_of_tendstoLocallyUniformlyOn [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn f' g' l s)
    (hf : ∀ᶠ n in l, ∀ x ∈ s, HasDerivAt (f n) (f' n x) x)
    (hfg : ∀ x ∈ s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) : HasDerivAt g (g' x) x := by
  have h1 : s ∈ 𝓝 x := hs.mem_nhds hx
  have h2 : ∀ᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_prod_iff.2 ⟨_, hf, fun x => x ∈ s, h1, fun {n} => id⟩
  refine hasDerivAt_of_tendstoUniformlyOnFilter ?_ h2 (eventually_of_mem h1 hfg)
  simpa [IsOpen.nhdsWithin_eq hs hx] using tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

/-- A slight variant of `hasDerivAt_of_tendstoLocallyUniformlyOn` with the assumption stated in
terms of `DifferentiableOn` rather than `HasDerivAt`. This makes a few proofs nicer in complex
analysis where holomorphicity is assumed but the derivative is not known a priori. -/
/-
**hasDerivAt_of_tendsto_locally_uniformly_on'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_of_tendsto_locally_uniformly_on' [NeBot l] {s : Set 𝕜} (hs : Is
Open s) (hf' : TendstoLocallyUniformlyOn (deriv ∘ f) g' l s) (hf : forallᶠ n in 
l, DifferentiableOn 𝕜 (f n) s) (hfg : forall x in s, Tendsto (fun n => f n x) l 
(𝓝 (g x))) (hx : x in s) : HasDerivAt g (g' x) x
参数：hs : IsOpen s；hf' : TendstoLocallyUniformlyOn (deriv ∘ f) g' l s；hf : forallᶠ
 n in l, DifferentiableOn 𝕜 (f n) s；hfg : forall x in s, Tendsto (fun n => f n x
) l (𝓝 (g x))；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAt_of_tendstoLocallyUniformlyOn`：hasDerivAt_of_tendstoLocallyUni
formlyOn [NeBot l] {s : Set 𝕜} (hs : IsOpen s) (hf' : TendstoLocallyUniformlyOn 
f' g' l s) (hf : forallᶠ n in…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
A slight variant of `hasDerivAt_of_tendstoLocallyUniformlyOn` with the assumptio
n stated in
terms of `DifferentiableOn` rather than `HasDerivAt`. This makes a few proofs ni
cer in complex
analysis where holomorphicity is assumed but the derivative is not known a prior
i.
-/
theorem hasDerivAt_of_tendsto_locally_uniformly_on' [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn (deriv ∘ f) g' l s)
    (hf : ∀ᶠ n in l, DifferentiableOn 𝕜 (f n) s)
    (hfg : ∀ x ∈ s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) : HasDerivAt g (g' x) x := by
  refine hasDerivAt_of_tendstoLocallyUniformlyOn hs hf' ?_ hfg hx
  filter_upwards [hf] with n h z hz using ((h z hz).differentiableAt (hs.mem_nhds hz)).hasDerivAt
/-
**hasDerivAt_of_tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_of_tendstoUniformlyOn [NeBot l] {s : Set 𝕜} (hs : IsOpen s) (hf
' : TendstoUniformlyOn f' g' l s) (hf : forallᶠ n in l, forall x : 𝕜, x in s -> 
HasDerivAt (f n) (f' n x) x) (hfg : forall x : 𝕜, x in s -> Tendsto (fun n => f 
n x) l (𝓝 (g x))) (hx : x in s) : HasDerivAt g (g' x) x
参数：hs : IsOpen s；hf' : TendstoUniformlyOn f' g' l s；hf : forallᶠ n in l, forall 
x : 𝕜, x in s -> HasDerivAt (f n) (f' n x) x；hfg : forall x : 𝕜, x in s -> Tends
to (fun n => f n x) l (𝓝 (g x))；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivAt_of_tendstoLocallyUniformlyOn`：hasDerivAt_of_tendstoLocallyUni
formlyOn [NeBot l] {s : Set 𝕜} (hs : IsOpen s) (hf' : TendstoLocallyUniformlyOn 
f' g' l s) (hf : forallᶠ n in…
· 使用定理 `TendstoUniformlyOn.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β : Type
 u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : 
ι → α → β}   {f : α → β} {s : Set …
-/
theorem hasDerivAt_of_tendstoUniformlyOn [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
    (hf' : TendstoUniformlyOn f' g' l s)
    (hf : ∀ᶠ n in l, ∀ x : 𝕜, x ∈ s → HasDerivAt (f n) (f' n x) x)
    (hfg : ∀ x : 𝕜, x ∈ s → Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) :
    HasDerivAt g (g' x) x :=
  hasDerivAt_of_tendstoLocallyUniformlyOn hs hf'.tendstoLocallyUniformlyOn hf hfg hx
/-
**hasDerivAt_of_tendstoUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_of_tendstoUniformly [NeBot l] (hf' : TendstoUniformly f' g' l) 
(hf : forallᶠ n in l, forall x : 𝕜, HasDerivAt (f n) (f' n x) x) (hfg : forall x
 : 𝕜, Tendsto (fun n => f n x) l (𝓝 (g x))) (x : 𝕜) : HasDerivAt g (g' x) x
参数：hf' : TendstoUniformly f' g' l；hf : forallᶠ n in l, forall x : 𝕜, HasDerivAt 
(f n) (f' n x) x；hfg : forall x : 𝕜, Tendsto (fun n => f n x) l (𝓝 (g x))；x : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_univ`：tendstoUniformlyOn_univ : TendstoUniformlyOn F 
f p univ ↔ TendstoUniformly F f p
· 使用定理 `hasDerivAt_of_tendstoUniformlyOn`：hasDerivAt_of_tendstoUniformlyOn [NeBo
t l] {s : Set 𝕜} (hs : IsOpen s) (hf' : TendstoUniformlyOn f' g' l s) (hf : fora
llᶠ n in l, forall x :…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem hasDerivAt_of_tendstoUniformly [NeBot l] (hf' : TendstoUniformly f' g' l)
    (hf : ∀ᶠ n in l, ∀ x : 𝕜, HasDerivAt (f n) (f' n x) x)
    (hfg : ∀ x : 𝕜, Tendsto (fun n => f n x) l (𝓝 (g x))) (x : 𝕜) : HasDerivAt g (g' x) x := by
  have hf : ∀ᶠ n in l, ∀ x : 𝕜, x ∈ Set.univ → HasDerivAt (f n) (f' n x) x := by
    filter_upwards [hf] with n h x _ using h x
  have hfg : ∀ x : 𝕜, x ∈ Set.univ → Tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.univ := by rwa [tendstoUniformlyOn_univ]
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_univ hf' hf hfg (Set.mem_univ x)

end deriv

