/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Tangent cone

In this file, we define two predicates `UniqueDiffWithinAt 𝕜 s x` and `UniqueDiffOn 𝕜 s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangentConeAt`,
and express `UniqueDiffWithinAt` and `UniqueDiffOn` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `UniqueDiffWithinAt` and `UniqueDiffOn` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. Hence, derivatives
are not defined yet. The property of uniqueness of the derivative is therefore proved in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`, but based on the properties of the tangent cone we
prove here.
-/

@[expose] public section

open Filter Set Metric
open scoped Topology Pointwise

universe u v
variable (R : Type u) {E : Type v}

section TangentConeAt

variable [AddCommGroup E] [SMul R E] [TopologicalSpace E] {s : Set E} {x y : E}

/-- The set of all tangent directions to the set `s` at the point `x`.

A point `y` belongs to the tangent cone of `s` at `x` iff
there exist a family of scalars `c n`, a family of vectors `d n`,
and a nontrivial filter in the index type such that

- `d n → 0` along the filter;
- `x + d n ∈ s` eventually along the filter;
- `c n • d n → y` along the filter,

The actual definition is given in terms of cluster points of a filter,
see `mem_tangentConeAt_of_seq` and `exists_fun_of_mem_tangentConeAt`
for the two implications unfolding this definition in more convenient way.

In a space with first countable topology,
one can assume that the index type is `ℕ` and the filter is `atTop`,
but the definition we use is more useful without that assumption.
-/
irreducible_def tangentConeAt (s : Set E) (x : E) : Set E :=
  {y : E | ClusterPt y ((⊤ : Filter R) • 𝓝[(x + ·) ⁻¹' s] 0)}

variable {R}

/-- Let `c n` be a family of scalars, `d n` be a family of vectors, and `l` be a filter such that

- `d n → 0` along `l`;
- `x + d n ∈ s` frequently along `l`;
- `c n • d n → y` along `l`.

Then `y` belongs to the tangent cone of `s` at `x`.
See also

- `mem_tangentConeAt_of_seq` for a version assuming that `x + d n ∈ s` eventually along `l`.
- `exists_fun_of_mem_tangentConeAt` for the other implication.
-/
/-
**mem_tangentConeAt_of_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_tangentConeAt_of_frequently {α : Type*} (l : Filter α) (c : α -> R) (d
 : α -> E) (hd₀ : Tendsto d l (𝓝 0)) (hds : existsᶠ n in l, x + d n in s) (hcd :
 Tendsto (fun n => c n • d n) l (𝓝 y)) : y in tangentConeAt R s x
参数：l : Filter α；c : α -> R；d : α -> E；hd₀ : Tendsto d l (𝓝 0)；hds : existsᶠ n in
 l, x + d n in s；hcd : Tendsto (fun n => c n • d n) l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map₂_smul`：map₂_smul : map₂ (· • ·) f g = f • g
· 使用定理 `Filter.map_prod_eq_map₂`：map_prod_eq_map₂ (m : α -> β -> γ) (f : Filter 
α) (g : Filter β) : Filter.map (fun p : α × β => m p.1 p.2) (f ×ˢ g) = map₂ m f 
g
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_top`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Fil
ter α}, Filter.Tendsto f l ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tangentConeAt_def`：∀ (R : Type u_1) {E : Type u_2} [inst : AddCommGroup 
E] [inst_1 : SMul R E] [inst_2 : TopologicalSpace E] (s : Set E)   (x : E), tang
entCone…
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `Filter.Tendsto.mapClusterPt`：Filter.Tendsto.mapClusterPt [NeBot F] (h : 
Tendsto u F (𝓝 x)) : MapClusterPt x F u
· 使用引理 `Filter.frequently_iff_neBot`：frequently_iff_neBot {l : Filter α} {p : α 
-> Prop} : (existsᶠ x in l, p x) ↔ NeBot (l ⊓ 𝓟 {x | p x})

--- 原说明 ---
Let `c n` be a family of scalars, `d n` be a family of vectors, and `l` be a fil
ter such that

- `d n → 0` along `l`;
- `x + d n ∈ s` frequently along `l`;
- `c n • d n → y` along `l`.

Then `y` belongs to the tangent cone of `s` at `x`.
See also

- `mem_tangentConeAt_of_seq` for a version assuming that `x + d n ∈ s` eventuall
y along `l`.
- `exists_fun_of_mem_tangentConeAt` for the other implication.
-/
theorem mem_tangentConeAt_of_frequently {α : Type*} (l : Filter α) (c : α → R) (d : α → E)
    (hd₀ : Tendsto d l (𝓝 0)) (hds : ∃ᶠ n in l, x + d n ∈ s)
    (hcd : Tendsto (fun n ↦ c n • d n) l (𝓝 y)) : y ∈ tangentConeAt R s x := by
  suffices Tendsto (fun n ↦ c n • d n) (l ⊓ 𝓟 {y | x + d y ∈ s}) (⊤ • 𝓝[(x + ·) ⁻¹' s] 0) by
    rw [frequently_iff_neBot] at hds
    rw [tangentConeAt_def]
    exact ClusterPt.mono (hcd.mono_left inf_le_left).mapClusterPt this
  rw [← map₂_smul, ← map_prod_eq_map₂]
  refine tendsto_map.comp (tendsto_top.prodMk (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩))
  · exact hd₀.mono_left inf_le_left
  · simp [eventually_inf_principal]

/-- A special case of `mem_tangentConeAt_of_frequently`, which avoids `Filter.Frequently`. -/
/-
**mem_tangentConeAt_of_seq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_tangentConeAt_of_seq {α : Type*} (l : Filter α) [l.NeBot] (c : α -> R)
 (d : α -> E) (hd₀ : Tendsto d l (𝓝 0)) (hds : forallᶠ n in l, x + d n in s) (hc
d : Tendsto (fun n => c n • d n) l (𝓝 y)) : y in tangentConeAt R s x
参数：l : Filter α；c : α -> R；d : α -> E；hd₀ : Tendsto d l (𝓝 0)；hds : forallᶠ n in
 l, x + d n in s；hcd : Tendsto (fun n => c n • d n) l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_tangentConeAt_of_frequently`：mem_tangentConeAt_of_frequently {α : Ty
pe*} (l : Filter α) (c : α -> R) (d : α -> E) (hd₀ : Tendsto d l (𝓝 0)) (hds : e
xistsᶠ n in l, x + d …
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x

--- 原说明 ---
A special case of `mem_tangentConeAt_of_frequently`, which avoids `Filter.Freque
ntly`.
-/
theorem mem_tangentConeAt_of_seq {α : Type*} (l : Filter α) [l.NeBot] (c : α → R) (d : α → E)
    (hd₀ : Tendsto d l (𝓝 0)) (hds : ∀ᶠ n in l, x + d n ∈ s)
    (hcd : Tendsto (fun n ↦ c n • d n) l (𝓝 y)) : y ∈ tangentConeAt R s x :=
  mem_tangentConeAt_of_frequently l c d hd₀ hds.frequently hcd

/-- If `y` belongs to the tangent cone of `s` at `x`, then there exist

- an index type `α` and a nontrivial filter `l` on `α`;
- a family of scalars `c n`, `n : α`, and a family of vectors `d n`, `n : α` such that
- `d n → 0` along `l`;
- `x + d n ∈ s` eventually along `l`;
- `c n • d n → y` along `l`.

In fact, one can take `α = R × E`, `c = Prod.fst`, and `d = Prod.snd`, but this is not important,
so the lemma statement hides these details.

This lemma provides a convenient way to unfold the definition of `tangentConeAt`. -/
/-
**exists_fun_of_mem_tangentConeAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_fun_of_mem_tangentConeAt (h : y in tangentConeAt R s x) : exists (α
 : Type (max u v)) (l : Filter α) (_hl : l.NeBot) (c : α -> R) (d : α -> E), Ten
dsto d l (𝓝 0) ∧ (forallᶠ n in l, x + d n in s) ∧ Tendsto (fun n => c n • d n) l
 (𝓝 y)
参数：h : y in tangentConeAt R s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.neBot_inf_comap_iff_map'`：neBot_inf_comap_iff_map' {f : α -> β} {
F : Filter α} {G : Filter β} : NeBot (comap f G ⊓ F) ↔ NeBot (G ⊓ map f F)
· 使用定理 `ClusterPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F 
: Filter X), ClusterPt x F = (nhds x ⊓ F).NeBot
· 使用定理 `Filter.map_prod_eq_map₂`：map_prod_eq_map₂ (m : α -> β -> γ) (f : Filter 
α) (g : Filter β) : Filter.map (fun p : α × β => m p.1 p.2) (f ×ˢ g) = map₂ m f 
g
· 使用定理 `Filter.map₂_smul`：map₂_smul : map₂ (· • ·) f g = f • g
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `tangentConeAt_def`：∀ (R : Type u_1) {E : Type u_2} [inst : AddCommGroup 
E] [inst_1 : SMul R E] [inst_2 : TopologicalSpace E] (s : Set E)   (x : E), tang
entCone…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.top_prod`：top_prod : (⊤ : Filter α) ×ˢ g = g.comap Prod.snd
· 使用定理 `Filter.eventually_comap`：eventually_comap : (forallᶠ a in comap f l, p a
) ↔ forallᶠ b in l, forall a, f a = b -> p a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
If `y` belongs to the tangent cone of `s` at `x`, then there exist

- an index type `α` and a nontrivial filter `l` on `α`;
- a family of scalars `c n`, `n : α`, and a family of vectors `d n`, `n : α` suc
h that
- `d n → 0` along `l`;
- `x + d n ∈ s` eventually along `l`;
- `c n • d n → y` along `l`.

In fact, one can take `α = R × E`, `c = Prod.fst`, and `d = Prod.snd`, but this 
is not important,
so the lemma statement hides these details.

This lemma provides a convenient way to unfold the definition of `tangentConeAt`
.
-/
theorem exists_fun_of_mem_tangentConeAt (h : y ∈ tangentConeAt R s x) :
    ∃ (α : Type (max u v)) (l : Filter α) (_hl : l.NeBot) (c : α → R) (d : α → E),
      Tendsto d l (𝓝 0) ∧ (∀ᶠ n in l, x + d n ∈ s) ∧ Tendsto (fun n ↦ c n • d n) l (𝓝 y) := by
  rw [tangentConeAt, mem_ofPred, ← map₂_smul, ← map_prod_eq_map₂, ClusterPt,
    ← neBot_inf_comap_iff_map'] at h
  refine ⟨R × E, _, h, Prod.fst, Prod.snd, ?_, ?_, ?_⟩
  · refine (tendsto_snd (f := ⊤)).mono_left <| inf_le_right.trans <| ?_
    gcongr
    apply nhdsWithin_le_nhds
  · refine .filter_mono inf_le_right ?_
    rw [top_prod, eventually_comap]
    filter_upwards [eventually_mem_nhdsWithin]
    simp +contextual
  · exact tendsto_comap.mono_left inf_le_left

end TangentConeAt

/-- "Positive" tangent cone to `s` at `x`. -/
/-
**posTangentConeAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：posTangentConeAt [AddCommGroup E] [Module Real E] [TopologicalSpace E] (s 
: Set E) (x : E) : Set E
参数：s : Set E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Positive" tangent cone to `s` at `x`.
-/
abbrev posTangentConeAt [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (s : Set E) (x : E) :
    Set E :=
  tangentConeAt NNReal s x

variable [Semiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `UniqueDiffWithinAt.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional). -/
@[mk_iff]
/-
**UniqueDiffWithinAt** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   {E : Type v} →     [inst : Semiring R] → [inst_1 : AddCom
mGroup E] → [_root_.Module R E] → [TopologicalSpace E] → Set E → E → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property ensuring that the tangent cone to `s` at `x` spans a dense subset of 
the whole space.
The main role of this property is to ensure that the differential within `s` at 
`x` is unique,
hence this name. The uniqueness it asserts is proved in `UniqueDiffWithinAt.eq` 
in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the clo
sure of `s` (which
is automatic when `E` is not `0`-dimensional).
-/
structure UniqueDiffWithinAt (s : Set E) (x : E) : Prop where
  dense_tangentConeAt : Dense (Submodule.span R (tangentConeAt R s x) : Set E)
  mem_closure : x ∈ closure s

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space. The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `UniqueDiffOn.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. -/
/-
**UniqueDiffOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniqueDiffOn (s : Set E) : Prop
参数：s : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property ensuring that the tangent cone to `s` at any of its points spans a de
nse subset of
the whole space. The main role of this property is to ensure that the differenti
al along `s` is
unique, hence this name. The uniqueness it asserts is proved in `UniqueDiffOn.eq
` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.
-/
def UniqueDiffOn (s : Set E) : Prop :=
  ∀ x ∈ s, UniqueDiffWithinAt R s x

variable {R} in
/-
**UniqueDiffOn.uniqueDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffOn.uniqueDiffWithinAt {s : Set E} {x} (hs : UniqueDiffOn R s) (h
 : x in s) : UniqueDiffWithinAt R s x
参数：hs : UniqueDiffOn R s；h : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UniqueDiffOn.uniqueDiffWithinAt {s : Set E} {x} (hs : UniqueDiffOn R s) (h : x ∈ s) :
    UniqueDiffWithinAt R s x :=
  hs x h
