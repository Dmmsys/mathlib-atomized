/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Tangent cone points as limits of sequences

This file contains a few ways to describe `tangentConeAt`
as the set of limits of certain sequences.

In many cases, one can generalize results about the tangent cone
by using `mem_tangentConeAt_of_seq` and `exists_fun_of_mem_tangentConeAt`
instead of these lemmas.
-/

public section

open Filter
open scoped Topology

/-- In a vector space with first countable topology, a vector `y` belongs to `tangentConeAt 𝕜 s x`
if and only if there exist sequences `c n` and `d n` such that

- `d n` tends to zero as `n → ∞`;
- `x + d n ∈ s` for sufficiently large `n`;
- `c n • d n` tends to `y` as `n → ∞`.

See `mem_tangentConeAt_of_seq` and `exists_fun_of_mem_tangentConeAt`
for versions of two implications of this theorem that don't assume first countable topology. -/
/-
**mem_tangentConeAt_iff_exists_seq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_tangentConeAt_iff_exists_seq {R E : Type*} [AddCommGroup E] [SMul R E]
 [TopologicalSpace E] [FirstCountableTopology E] {s : Set E} {x y : E} : y in ta
ngentConeAt R s x ↔ exists (c : Nat -> R) (d : Nat -> E), Tendsto d atTop (𝓝 0) 
∧ (forallᶠ n in atTop, x + d n in s) ∧ Tendsto (fun n => c n • d n) atTop (𝓝 y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `Filter.Inf.isCountablyGenerated`：∀ {α : Type u_1} (f g : Filter α) [f.Is
CountablyGenerated] [g.IsCountablyGenerated], (f ⊓ g).IsCountablyGenerated
· 使用定理 `Filter.comap.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (l : 
Filter β) [l.IsCountablyGenerated] (f : α → β),   (Filter.comap f l).IsCountably
Generated
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `Filter.prod.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (la : 
Filter α) (lb : Filter β) [la.IsCountablyGenerated] [lb.IsCountablyGenerated],  
 (la ×ˢ lb).IsCountabl…
· 使用定理 `Filter.isCountablyGenerated_top`：isCountablyGenerated_top : IsCountablyG
enerated (⊤ : Filter α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tangentConeAt_def`：∀ (R : Type u_1) {E : Type u_2} [inst : AddCommGroup 
E] [inst_1 : SMul R E] [inst_2 : TopologicalSpace E] (s : Set E)   (x : E), tang
entCone…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mem_tangentConeAt_of_seq`：mem_tangentConeAt_of_seq {α : Type*} (l : Filt
er α) [l.NeBot] (c : α -> R) (d : α -> E) (hd₀ : Tendsto d l (𝓝 0)) (hds : foral
lᶠ n in l, x +…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
In a vector space with first countable topology, a vector `y` belongs to `tangen
tConeAt 𝕜 s x`
if and only if there exist sequences `c n` and `d n` such that

- `d n` tends to zero as `n → ∞`;
- `x + d n ∈ s` for sufficiently large `n`;
- `c n • d n` tends to `y` as `n → ∞`.

See `mem_tangentConeAt_of_seq` and `exists_fun_of_mem_tangentConeAt`
for versions of two implications of this theorem that don't assume first countab
le topology.
-/
theorem mem_tangentConeAt_iff_exists_seq {R E : Type*} [AddCommGroup E] [SMul R E]
    [TopologicalSpace E] [FirstCountableTopology E] {s : Set E} {x y : E} :
    y ∈ tangentConeAt R s x ↔ ∃ (c : ℕ → R) (d : ℕ → E), Tendsto d atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, x + d n ∈ s) ∧ Tendsto (fun n ↦ c n • d n) atTop (𝓝 y) := by
  constructor
  · intro h
    simp only [tangentConeAt_def, Set.mem_ofPred, ← map₂_smul, ← map_prod_eq_map₂, ClusterPt,
      ← neBot_inf_comap_iff_map'] at h
    rcases @exists_seq_tendsto _ _ _ h with ⟨cd, hcd⟩
    simp only [tendsto_inf, tendsto_comap_iff, tendsto_prod_iff', tendsto_nhdsWithin_iff] at hcd
    exact ⟨Prod.fst ∘ cd, Prod.snd ∘ cd, hcd.2.2.1, hcd.2.2.2, hcd.1⟩
  · rintro ⟨c, d, hd₀, hds, hcd⟩
    exact mem_tangentConeAt_of_seq atTop c d hd₀ hds hcd

section
variable {𝕜 E : Type*} [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousSMul 𝕜 E] {s : Set E} {x y : E} {r : 𝕜}

/-- Auxiliary lemma ensuring that, under the assumptions from an old definition of the tangent cone,
the sequence `d` tends to 0 at infinity. -/
/-
**tangentConeAt.lim_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt.lim_zero {α : Type*} (l : Filter α) {c : α -> 𝕜} {d : α -> E
} {y : E} (hc : Tendsto (fun n => ‖c n‖) l atTop) (hd : Tendsto (fun n => c n • 
d n) l (𝓝 y)) : Tendsto d l (𝓝 0)
参数：l : Filter α；hc : Tendsto (fun n => ‖c n‖) l atTop；hd : Tendsto (fun n => c n
 • d n) l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_ne_of_tendsto_norm_atTop`：∀ {α : Type u_1} {E : Type u_4} [in
st : SeminormedAddGroup E] {l : Filter α} {f : α → E},   Filter.Tendsto (fun y =
> ‖f y‖) l Filter.atTop →…
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_inv₀_cobounded`：tendsto_inv₀_cobounded : Tendsto Inv.inv 
(cobounded α) (𝓝 0)
· 使用定理 `tendsto_norm_atTop_iff_cobounded`：∀ {α : Type u_1} {E : Type u_2} [inst 
: SeminormedAddGroup E] {f : α → E} {l : Filter α},   Filter.Tendsto (fun x => ‖
f x‖) l Filter.atTop ↔…

--- 原说明 ---
Auxiliary lemma ensuring that, under the assumptions from an old definition of t
he tangent cone,
the sequence `d` tends to 0 at infinity.
-/
theorem tangentConeAt.lim_zero {α : Type*} (l : Filter α) {c : α → 𝕜} {d : α → E} {y : E}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) (hd : Tendsto (fun n => c n • d n) l (𝓝 y)) :
    Tendsto d l (𝓝 0) := by
  have : ∀ᶠ n in l, (c n)⁻¹ • c n • d n = d n :=
    (eventually_ne_of_tendsto_norm_atTop hc 0).mono fun n hn ↦ inv_smul_smul₀ hn (d n)
  rw [tendsto_norm_atTop_iff_cobounded] at hc
  simpa using Tendsto.congr' this <| (tendsto_inv₀_cobounded.comp hc).smul hd
/-
**mem_tangentConeAt_of_pow_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_tangentConeAt_of_pow_smul (hr₀ : r != 0) (hr : ‖r‖ < 1) (hs : forallᶠ 
n : Nat in atTop, x + r ^ n • y in s) : y in tangentConeAt 𝕜 s x
参数：hr₀ : r != 0；hr : ‖r‖ < 1；hs : forallᶠ n : Nat in atTop, x + r ^ n • y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_tangentConeAt_of_add_smul_mem`：mem_tangentConeAt_of_add_smul_mem {α 
: Type*} {l : Filter α} [l.NeBot] {c : α -> 𝕜} (hc₀ : Tendsto c l (𝓝[!=] 0)) (hm
em : forallᶠ n in l, x …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`：tendsto_pow_atTop_nhds_zero_
of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R} (h : ‖x‖ < 1) : Tendsto (f
un n : Nat => x ^ n) atTop (𝓝 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mem_tangentConeAt_of_pow_smul (hr₀ : r ≠ 0) (hr : ‖r‖ < 1)
    (hs : ∀ᶠ n : ℕ in atTop, x + r ^ n • y ∈ s) :
    y ∈ tangentConeAt 𝕜 s x := by
  refine mem_tangentConeAt_of_add_smul_mem
    (tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr, ?_⟩) hs
  simp [hr₀]

end

/-- In a normed space over a nontrivially normed field,
a point `y` belongs to the tangent cone of a set `s` at `x`
iff there exists a sequence of scalars `c n` and a sequence of points `d n` such that

- `‖c n‖ → ∞` as `n → ∞`;
- `x + d n ∈ s` for sufficiently large `n`;
- `c n • d n` tends to `y`.

Before https://github.com/leanprover-community/mathlib4/pull/34127,
the right-hand side of this equivalence was the definition of the tangent cone.

In most cases, `exists_fun_of_mem_tangentConeAt` and/or `mem_tangentConeAt_of_seq`
can be used to generalize a proof using this lemma to topological vector spaces.
-/
/-
**mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop {𝕜 E : Type*} [Nontriv
iallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : Set E} {x y : 
E} : y in tangentConeAt 𝕜 s x ↔ exists (c : Nat -> 𝕜) (d : Nat -> E), Tendsto (‖
c ·‖) atTop atTop ∧ (forallᶠ n in atTop, x + d n in s) ∧ Tendsto (fun n => c n •
 d n) atTop (𝓝 y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_mem_tangentConeAt_iff`：zero_mem_tangentConeAt_iff : 0 in tangentCon
eAt 𝕜 s x ↔ x in closure s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `dist_eq_norm_sub'`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a
 b : E), dist a b = ‖b - a‖
（共 94 条，此处仅展示前 30 条）

--- 原说明 ---
In a normed space over a nontrivially normed field,
a point `y` belongs to the tangent cone of a set `s` at `x`
iff there exists a sequence of scalars `c n` and a sequence of points `d n` such
 that

- `‖c n‖ → ∞` as `n → ∞`;
- `x + d n ∈ s` for sufficiently large `n`;
- `c n • d n` tends to `y`.

Before https://github.com/leanprover-community/mathlib4/pull/34127,
the right-hand side of this equivalence was the definition of the tangent cone.

In most cases, `exists_fun_of_mem_tangentConeAt` and/or `mem_tangentConeAt_of_se
q`
can be used to generalize a proof using this lemma to topological vector spaces.
-/
theorem mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set E} {x y : E} :
    y ∈ tangentConeAt 𝕜 s x ↔
      ∃ (c : ℕ → 𝕜) (d : ℕ → E), Tendsto (‖c ·‖) atTop atTop ∧ (∀ᶠ n in atTop, x + d n ∈ s) ∧
        Tendsto (fun n ↦ c n • d n) atTop (𝓝 y) := by
  constructor
  · rcases eq_or_ne y 0 with rfl | hy₀
    · rw [zero_mem_tangentConeAt_iff]
      intro hx
      obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 1
      have (n : ℕ) : ∃ d : E, x + d ∈ s ∧ ‖d‖ < (1 / (2 * ‖c‖)) ^ n := by
        rw [Metric.mem_closure_iff] at hx
        rcases hx ((1 / (2 * ‖c‖)) ^ n) (by positivity) with ⟨v, hvs, hv⟩
        use v - x
        simp_all [dist_eq_norm_sub']
      choose d hds hd using this
      refine ⟨(c ^ ·), d, ?tendsto_c, .of_forall hds, ?tendsto_cd⟩
      case tendsto_c =>
        simp only [norm_pow]
        exact tendsto_pow_atTop_atTop_of_one_lt hc
      case tendsto_cd =>
        rw [atTop_basis.tendsto_iff (Metric.nhds_basis_ball_pow one_half_pos one_half_lt_one)]
        refine fun N _ ↦ ⟨N, trivial, fun n hn ↦ ?_⟩
        rw [Set.mem_Ici] at hn
        suffices ‖c‖ ^ n * ‖d n‖ < 1 / (2 ^ N) by simpa [norm_smul]
        rw [← lt_div_iff₀' (by positivity)]
        refine (hd n).trans_le ?_
        grw [hn]
        · simp [mul_pow, div_eq_inv_mul]
        · norm_num1
    · rw [mem_tangentConeAt_iff_exists_seq]
      rintro ⟨c, d, hd₀, hds, hcd⟩
      refine ⟨c, d, ?_, hds, hcd⟩
      replace hd₀ := hd₀.norm
      have hd₀' : ∀ᶠ n in .atTop, d n ≠ 0 :=
        hcd.eventually_ne hy₀ |>.mono fun _ ↦ right_ne_zero_of_smul
      replace hcd := hcd.norm
      simp only [norm_smul, norm_zero, ← div_inv_eq_mul] at hd₀ hcd
      refine .num ?_ (by simpa) hcd
      rw [← inv_nhdsGT_zero (𝕜 := ℝ), ← Filter.comap_inv, Filter.tendsto_comap_iff]
      simpa [Function.comp_def, tendsto_nhdsWithin_iff, hd₀] using hd₀'
  · rintro ⟨c, d, hc, hds, hcd⟩
    exact mem_tangentConeAt_of_seq atTop c d (tangentConeAt.lim_zero atTop hc hcd) hds hcd
