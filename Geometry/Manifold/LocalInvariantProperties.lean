/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Local properties invariant under a groupoid

We study properties of a triple `(g, s, x)` where `g` is a function between two spaces `H` and `H'`,
`s` is a subset of `H` and `x` is a point of `H`. Our goal is to register how such a property
should behave to make sense in charted spaces modelled on `H` and `H'`.

The main examples we have in mind are the properties "`g` is differentiable at `x` within `s`", or
"`g` is smooth at `x` within `s`". We want to develop general results that, when applied in these
specific situations, say that the notion of smooth function in a manifold behaves well under
restriction, intersection, is local, and so on.

## Main definitions

* `LocalInvariantProp G G' P` says that a property `P` of a triple `(g, s, x)` is local, and
  invariant under composition by elements of the groupoids `G` and `G'` of `H` and `H'`
  respectively.
* `ChartedSpace.LiftPropWithinAt` (resp. `LiftPropAt`, `LiftPropOn` and `LiftProp`):
  given a property `P` of `(g, s, x)` where `g : H → H'`, define the corresponding property
  for functions `M → M'` where `M` and `M'` are charted spaces modelled respectively on `H` and
  `H'`. We define these properties within a set at a point, or at a point, or on a set, or in the
  whole space. This lifting process (obtained by restricting to suitable chart domains) can always
  be done, but it only behaves well under locality and invariance assumptions.

Given `hG : LocalInvariantProp G G' P`, we deduce many properties of the lifted property on the
charted spaces. For instance, `hG.liftPropWithinAt_inter` says that `P g s x` is equivalent to
`P g (s ∩ t) x` whenever `t` is a neighborhood of `x`.

## Implementation notes

We do not use dot notation for properties of the lifted property. For instance, we have
`hG.liftPropWithinAt_congr` saying that if `LiftPropWithinAt P g s x` holds, and `g` and `g'`
coincide on `s`, then `LiftPropWithinAt P g' s x` holds. We can't call it
`LiftPropWithinAt.congr` as it is in the namespace associated to `LocalInvariantProp`, not
in the one for `LiftPropWithinAt`.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold Topology

variable {H M H' M' X : Type*}
variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']
variable [TopologicalSpace X]

namespace StructureGroupoid

variable (G : StructureGroupoid H) (G' : StructureGroupoid H')

/-- Structure recording good behavior of a property of a triple `(f, s, x)` where `f` is a function,
`s` a set and `x` a point. Good behavior here means locality and invariance under given groupoids
(both in the source and in the target). Given such a good behavior, the lift of this property
to charted spaces admitting these groupoids will inherit the good behavior. -/
/-
**StructureGroupoid.LocalInvariantProp** 是 Mathlib 中的一个归纳类型，位于命名空间 `StructureGro
upoid`。
形式化陈述：{H : Type u_1} →   {H' : Type u_3} →     [inst : TopologicalSpace H] →    
   [inst_1 : TopologicalSpace H'] → StructureGroupoid H → StructureGroupoid H' →
 ((H → H') → Set H → H → Prop) → Prop
参数：(H → H') → Set H → H → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure recording good behavior of a property of a triple `(f, s, x)` where `f
` is a function,
`s` a set and `x` a point. Good behavior here means locality and invariance unde
r given groupoids
(both in the source and in the target). Given such a good behavior, the lift of 
this property
to charted spaces admitting these groupoids will inherit the good behavior.
-/
structure LocalInvariantProp (P : (H → H') → Set H → H → Prop) : Prop where
  is_local : ∀ {s x u} {f : H → H'}, IsOpen u → x ∈ u → (P f s x ↔ P f (s ∩ u) x)
  right_invariance' : ∀ {s x f} {e : OpenPartialHomeomorph H H},
    e ∈ G → x ∈ e.source → P f s x → P (f ∘ e.symm) (e.symm ⁻¹' s) (e x)
  congr_of_forall : ∀ {s x} {f g : H → H'}, (∀ y ∈ s, f y = g y) → f x = g x → P f s x → P g s x
  left_invariance' : ∀ {s x f} {e' : OpenPartialHomeomorph H' H'},
    e' ∈ G' → s ⊆ f ⁻¹' e'.source → f x ∈ e'.source → P f s x → P (e' ∘ f) s x

variable {G G'} {P : (H → H') → Set H → H → Prop}
variable (hG : G.LocalInvariantProp G' P)
include hG

namespace LocalInvariantProp

/-
**StructureGroupoid.LocalInvariantProp.congr_set** 是 Mathlib 中的一个定理，位于命名空间 `Stru
ctureGroupoid.LocalInvariantProp`。
形式化陈述：congr_set {s t : Set H} {x : H} {f : H -> H'} (hu : s =ᶠ[𝓝 x] t) : P f s x
 ↔ P f t x
参数：hu : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Filter.EventuallyEq.mem_iff`：∀ {α : Type u} {s t : Set α} {l : Filter α}
, s =ᶠ[l] t → ∀ᶠ (x : α) in l, x ∈ s ↔ x ∈ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.LocalInvariantProp.is_local`：∀ {H : Type u_1} {H' : Ty
pe u_3} [inst : TopologicalSpace H] [inst_1 : TopologicalSpace H'] {G : Structur
eGroupoid H}   {G' : StructureGroup…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem congr_set {s t : Set H} {x : H} {f : H → H'} (hu : s =ᶠ[𝓝 x] t) : P f s x ↔ P f t x := by
  obtain ⟨o, host, ho, hxo⟩ := mem_nhds_iff.mp hu.mem_iff
  simp_rw [subset_def, mem_ofPred, ← and_congr_left_iff, ← mem_inter_iff, ← Set.ext_iff] at host
  rw [hG.is_local ho hxo, host, ← hG.is_local ho hxo]
/-
**StructureGroupoid.LocalInvariantProp.is_local_nhds** 是 Mathlib 中的一个定理，位于命名空间 `
StructureGroupoid.LocalInvariantProp`。
形式化陈述：is_local_nhds {s u : Set H} {x : H} {f : H -> H'} (hu : u in 𝓝[s] x) : P f
 s x ↔ P f (s inter u) x
参数：hu : u in 𝓝[s] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_set`：congr_set {s t : Set H} 
{x : H} {f : H -> H'} (hu : s =ᶠ[𝓝 x] t) : P f s x ↔ P f t x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_eventuallyEq`：mem_nhdsWithin_iff_eventuallyEq {s t : 
Set α} {x : α} : t in 𝓝[s] x ↔ s =ᶠ[𝓝 x] (s inter t : Set α)
-/
theorem is_local_nhds {s u : Set H} {x : H} {f : H → H'} (hu : u ∈ 𝓝[s] x) :
    P f s x ↔ P f (s ∩ u) x :=
  hG.congr_set <| mem_nhdsWithin_iff_eventuallyEq.mp hu
/-
**StructureGroupoid.LocalInvariantProp.congr_iff_nhdsWithin** 是 Mathlib 中的一个定理，位
于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：congr_iff_nhdsWithin {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x
] g) (h2 : f x = g x) : P f s x ↔ P g s x
参数：h1 : f =ᶠ[𝓝[s] x] g；h2 : f x = g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.LocalInvariantProp.is_local_nhds`：is_local_nhds {s u :
 Set H} {x : H} {f : H -> H'} (hu : u in 𝓝[s] x) : P f s x ↔ P f (s inter u) x
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_of_forall`：∀ {H : Type u_1} {
H' : Type u_3} [inst : TopologicalSpace H] [inst_1 : TopologicalSpace H'] {G : S
tructureGroupoid H}   {G' : StructureGroup…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem congr_iff_nhdsWithin {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g)
    (h2 : f x = g x) : P f s x ↔ P g s x := by
  simp_rw [hG.is_local_nhds h1]
  exact ⟨hG.congr_of_forall (fun y hy ↦ hy.2) h2, hG.congr_of_forall (fun y hy ↦ hy.2.symm) h2.symm⟩
/-
**StructureGroupoid.LocalInvariantProp.congr_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空
间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：congr_nhdsWithin {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g)
 (h2 : f x = g x) (hP : P f s x) : P g s x
参数：h1 : f =ᶠ[𝓝[s] x] g；h2 : f x = g x；hP : P f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_iff_nhdsWithin`：congr_iff_nhd
sWithin {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g 
x) : P f s x ↔ P g s x
-/
theorem congr_nhdsWithin {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
    (hP : P f s x) : P g s x :=
  (hG.congr_iff_nhdsWithin h1 h2).mp hP
/-
**StructureGroupoid.LocalInvariantProp.congr_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名
空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：congr_nhdsWithin' {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g
) (h2 : f x = g x) (hP : P g s x) : P f s x
参数：h1 : f =ᶠ[𝓝[s] x] g；h2 : f x = g x；hP : P g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_iff_nhdsWithin`：congr_iff_nhd
sWithin {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g 
x) : P f s x ↔ P g s x
-/
theorem congr_nhdsWithin' {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
    (hP : P g s x) : P f s x :=
  (hG.congr_iff_nhdsWithin h1 h2).mpr hP
/-
**StructureGroupoid.LocalInvariantProp.congr_iff** 是 Mathlib 中的一个定理，位于命名空间 `Stru
ctureGroupoid.LocalInvariantProp`。
形式化陈述：congr_iff {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) : P f s x 
↔ P g s x
参数：h : f =ᶠ[𝓝 x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_iff_nhdsWithin`：congr_iff_nhd
sWithin {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g 
x) : P f s x ↔ P g s x
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem congr_iff {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) : P f s x ↔ P g s x :=
  hG.congr_iff_nhdsWithin (mem_nhdsWithin_of_mem_nhds h) (mem_of_mem_nhds h :)
/-
**StructureGroupoid.LocalInvariantProp.congr** 是 Mathlib 中的一个定理，位于命名空间 `Structur
eGroupoid.LocalInvariantProp`。
形式化陈述：congr {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x)
 : P g s x
参数：h : f =ᶠ[𝓝 x] g；hP : P f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_iff`：congr_iff {s : Set H} {x
 : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) : P f s x ↔ P g s x
-/
theorem congr {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x) : P g s x :=
  (hG.congr_iff h).mp hP
/-
**StructureGroupoid.LocalInvariantProp.congr'** 是 Mathlib 中的一个定理，位于命名空间 `Structu
reGroupoid.LocalInvariantProp`。
形式化陈述：congr' {s : Set H} {x : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x
) : P f s x
参数：h : f =ᶠ[𝓝 x] g；hP : P g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr`：congr {s : Set H} {x : H} {f
 g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x) : P g s x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem congr' {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x) : P f s x :=
  hG.congr h.symm hP
/-
**StructureGroupoid.LocalInvariantProp.congr_set_fun** 是 Mathlib 中的一个定理，位于命名空间 `
StructureGroupoid.LocalInvariantProp`。
形式化陈述：congr_set_fun {s t : Set H} {x : H} {f g : H -> H'} (hu : s =ᶠ[𝓝 x] t) (h 
: f =ᶠ[𝓝 x] g) : P f s x ↔ P g t x
参数：hu : s =ᶠ[𝓝 x] t；h : f =ᶠ[𝓝 x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_iff`：congr_iff {s : Set H} {x
 : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) : P f s x ↔ P g s x
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_set`：congr_set {s t : Set H} 
{x : H} {f : H -> H'} (hu : s =ᶠ[𝓝 x] t) : P f s x ↔ P f t x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem congr_set_fun {s t : Set H} {x : H} {f g : H → H'} (hu : s =ᶠ[𝓝 x] t) (h : f =ᶠ[𝓝 x] g) :
    P f s x ↔ P g t x := by
  rw [hG.congr_iff h, hG.congr_set hu]
/-
**StructureGroupoid.LocalInvariantProp.left_invariance** 是 Mathlib 中的一个定理，位于命名空间
 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：left_invariance {s : Set H} {x : H} {f : H -> H'} {e' : OpenPartialHomeomo
rph H' H'} (he' : e' in G') (hfs : ContinuousWithinAt f s x) (hxe' : f x in e'.s
ource) : P (e' ∘ f) s x ↔ P f s x
参数：he' : e' in G'；hfs : ContinuousWithinAt f s x；hxe' : f x in e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin`：ContinuousWithinAt.preimage_
mem_nhdsWithin {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝 (f x)) : 
f ⁻¹' t in 𝓝[s] x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
· 使用定理 `StructureGroupoid.LocalInvariantProp.left_invariance'`：∀ {H : Type u_1} 
{H' : Type u_3} [inst : TopologicalSpace H] [inst_1 : TopologicalSpace H'] {G : 
StructureGroupoid H}   {G' : StructureGroup…
· 使用定理 `StructureGroupoid.symm`：StructureGroupoid.symm (G : StructureGroupoid H)
 {e : OpenPartialHomeomorph H H} (he : e in G) : e.symm in G
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.LocalInvariantProp.is_local_nhds`：is_local_nhds {s u :
 Set H} {x : H} {f : H -> H'} (hu : u in 𝓝[s] x) : P f s x ↔ P f (s inter u) x
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_nhdsWithin`：congr_nhdsWithin 
{s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x) (hP :
 P f s x) : P g s x
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem left_invariance {s : Set H} {x : H} {f : H → H'} {e' : OpenPartialHomeomorph H' H'}
    (he' : e' ∈ G') (hfs : ContinuousWithinAt f s x) (hxe' : f x ∈ e'.source) :
    P (e' ∘ f) s x ↔ P f s x := by
  have h2f := hfs.preimage_mem_nhdsWithin (e'.open_source.mem_nhds hxe')
  have h3f :=
    ((e'.continuousAt hxe').comp_continuousWithinAt hfs).preimage_mem_nhdsWithin <|
      e'.symm.open_source.mem_nhds <| e'.mapsTo hxe'
  constructor
  · intro h
    rw [hG.is_local_nhds h3f] at h
    have h2 := hG.left_invariance' (G'.symm he') inter_subset_right (e'.mapsTo hxe') h
    rw [← hG.is_local_nhds h3f] at h2
    refine hG.congr_nhdsWithin ?_ (e'.left_inv hxe') h2
    exact eventually_of_mem h2f fun x' ↦ e'.left_inv
  · simp_rw [hG.is_local_nhds h2f]
    exact hG.left_invariance' he' inter_subset_right hxe'
/-
**StructureGroupoid.LocalInvariantProp.right_invariance** 是 Mathlib 中的一个定理，位于命名空
间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：right_invariance {s : Set H} {x : H} {f : H -> H'} {e : OpenPartialHomeomo
rph H H} (he : e in G) (hxe : x in e.source) : P (f ∘ e.symm) (e.symm ⁻¹' s) (e 
x) ↔ P f s x
参数：he : e in G；hxe : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.right_invariance'`：∀ {H : Type u_1}
 {H' : Type u_3} [inst : TopologicalSpace H] [inst_1 : TopologicalSpace H'] {G :
 StructureGroupoid H}   {G' : StructureGroup…
· 使用定理 `StructureGroupoid.symm`：StructureGroupoid.symm (G : StructureGroupoid H)
 {e : OpenPartialHomeomorph H H} (he : e in G) : e.symm in G
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr`：congr {s : Set H} {x : H} {f
 g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x) : P g s x
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_set`：congr_set {s t : Set H} 
{x : H} {f : H -> H'} (hu : s =ᶠ[𝓝 x] t) : P f s x ↔ P f t x
· 使用定理 `Filter.eventuallyEq_set`：eventuallyEq_set {s t : Set α} {l : Filter α} :
 s =ᶠ[l] t ↔ forallᶠ x in l, x in s ↔ x in t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `OpenPartialHomeomorph.symm_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph 
X Y), e.symm.symm = e
-/
theorem right_invariance {s : Set H} {x : H} {f : H → H'} {e : OpenPartialHomeomorph H H}
    (he : e ∈ G) (hxe : x ∈ e.source) : P (f ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P f s x := by
  refine ⟨fun h ↦ ?_, hG.right_invariance' he hxe⟩
  have := hG.right_invariance' (G.symm he) (e.mapsTo hxe) h
  rw [e.symm_symm, e.left_inv hxe] at this
  refine hG.congr ?_ ((hG.congr_set ?_).mp this)
  · refine eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' ↦ ?_
    simp_rw [Function.comp_apply, e.left_inv hx']
  · rw [eventuallyEq_set]
    refine eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' ↦ ?_
    simp_rw [mem_preimage, e.left_inv hx']

end LocalInvariantProp

end StructureGroupoid

namespace ChartedSpace

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property in a charted space, by requiring that it holds at the preferred chart at
this point. (When the property is local and invariant, it will in fact hold using any chart, see
`liftPropWithinAt_indep_chart`). We require continuity in the lifted property, as otherwise one
single chart might fail to capture the behavior of the function.
-/
@[mk_iff liftPropWithinAt_iff']
/-
**ChartedSpace.LiftPropWithinAt** 是 Mathlib 中的一个归纳类型，位于命名空间 `ChartedSpace`。
形式化陈述：{H : Type u_1} →   {M : Type u_2} →     {H' : Type u_3} →       {M' : Type
 u_4} →         [inst : TopologicalSpace H] →           [inst_1 : TopologicalSpa
ce M] →             [ChartedSpace H M] →               [inst : TopologicalSpace 
H'] →                 [inst_2 : TopologicalSpace M'] →                   [Charte
dSpace H' M'] → ((H → H') → Set H → H → Prop) → (M → M') → Set M → M → Prop
参数：(H → H') → Set H → H → Prop；M → M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a property of germs of functions and sets in the model space, then one def
ines
a corresponding property in a charted space, by requiring that it holds at the p
referred chart at
this point. (When the property is local and invariant, it will in fact hold usin
g any chart, see
`liftPropWithinAt_indep_chart`). We require continuity in the lifted property, a
s otherwise one
single chart might fail to capture the behavior of the function.
-/
structure LiftPropWithinAt (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) (x : M) :
    Prop where
  continuousWithinAt : ContinuousWithinAt f s x
  prop : P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x)

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of functions on sets in a charted space, by requiring that it holds
around each point of the set, in the preferred charts. -/
/-
**ChartedSpace.LiftPropOn** 是 Mathlib 中的一个定义，位于命名空间 `ChartedSpace`。
形式化陈述：LiftPropOn (P : (H -> H') -> Set H -> H -> Prop) (f : M -> M') (s : Set M)
参数：P : (H -> H') -> Set H -> H -> Prop；f : M -> M'；s : Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a property of germs of functions and sets in the model space, then one def
ines
a corresponding property of functions on sets in a charted space, by requiring t
hat it holds
around each point of the set, in the preferred charts.
-/
def LiftPropOn (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) :=
  ∀ x ∈ s, LiftPropWithinAt P f s x

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function at a point in a charted space, by requiring that it holds
in the preferred chart. -/
/-
**ChartedSpace.LiftPropAt** 是 Mathlib 中的一个定义，位于命名空间 `ChartedSpace`。
形式化陈述：LiftPropAt (P : (H -> H') -> Set H -> H -> Prop) (f : M -> M') (x : M)
参数：P : (H -> H') -> Set H -> H -> Prop；f : M -> M'；x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a property of germs of functions and sets in the model space, then one def
ines
a corresponding property of a function at a point in a charted space, by requiri
ng that it holds
in the preferred chart.
-/
def LiftPropAt (P : (H → H') → Set H → H → Prop) (f : M → M') (x : M) :=
  LiftPropWithinAt P f univ x
/-
**ChartedSpace.liftPropAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `ChartedSpace`。
形式化陈述：liftPropAt_iff {P : (H -> H') -> Set H -> H -> Prop} {f : M -> M'} {x : M}
 : LiftPropAt P f x ↔ ContinuousAt f x ∧ P (chartAt H' (f x) ∘ f ∘ (chartAt H x)
.symm) univ (chartAt H x x)
参数：H -> H'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ChartedSpace.LiftPropAt.eq_1`：∀ {H : Type u_1} {M : Type u_2} {H' : Type
 u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalSpace M
] [inst_2 : Charte…
· 使用定理 `ChartedSpace.liftPropWithinAt_iff'`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftPropAt_iff {P : (H → H') → Set H → H → Prop} {f : M → M'} {x : M} :
    LiftPropAt P f x ↔
      ContinuousAt f x ∧ P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) univ (chartAt H x x) := by
  rw [LiftPropAt, liftPropWithinAt_iff', continuousWithinAt_univ, preimage_univ]

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function in a charted space, by requiring that it holds
in the preferred chart around every point. -/
/-
**ChartedSpace.LiftProp** 是 Mathlib 中的一个定义，位于命名空间 `ChartedSpace`。
形式化陈述：LiftProp (P : (H -> H') -> Set H -> H -> Prop) (f : M -> M')
参数：P : (H -> H') -> Set H -> H -> Prop；f : M -> M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a property of germs of functions and sets in the model space, then one def
ines
a corresponding property of a function in a charted space, by requiring that it 
holds
in the preferred chart around every point.
-/
def LiftProp (P : (H → H') → Set H → H → Prop) (f : M → M') :=
  ∀ x, LiftPropAt P f x
/-
**ChartedSpace.liftProp_iff** 是 Mathlib 中的一个定理，位于命名空间 `ChartedSpace`。
形式化陈述：liftProp_iff {P : (H -> H') -> Set H -> H -> Prop} {f : M -> M'} : LiftPro
p P f ↔ Continuous f ∧ forall x, P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) u
niv (chartAt H x x)
参数：H -> H'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem liftProp_iff {P : (H → H') → Set H → H → Prop} {f : M → M'} :
    LiftProp P f ↔
      Continuous f ∧ ∀ x, P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) univ (chartAt H x x) := by
  simp_rw [LiftProp, liftPropAt_iff, forall_and, continuous_iff_continuousAt]

@[simp]
/-
**ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
hartedSpace`。
形式化陈述：liftPropWithinAt_subtypeVal_comp_iff {P : (H -> H') -> Set H -> H -> Prop}
 {U : Opens M'} (f : M -> U) (s : Set M) (x : M) : LiftPropWithinAt P (Subtype.v
al ∘ f) s x ↔ LiftPropWithinAt P f s x
参数：H -> H'；f : M -> U；s : Set M；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Topology.IsInducing.continuousWithinAt_iff`：Topology.IsInducing.continuo
usWithinAt_iff {f : α -> β} {g : β -> γ} (hg : IsInducing g) {s : Set α} {x : α}
 : ContinuousWithinAt f s x ↔ Co…
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma liftPropWithinAt_subtypeVal_comp_iff {P : (H → H') → Set H → H → Prop}
    {U : Opens M'} (f : M → U) (s : Set M) (x : M) :
    LiftPropWithinAt P (Subtype.val ∘ f) s x ↔ LiftPropWithinAt P f s x := by
  simp only [ChartedSpace.liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · exact Topology.IsEmbedding.subtypeVal.isInducing.continuousWithinAt_iff.symm
  · rfl

end ChartedSpace

open ChartedSpace

namespace StructureGroupoid

variable {G : StructureGroupoid H} {G' : StructureGroupoid H'} {e e' : OpenPartialHomeomorph M H}
  {f f' : OpenPartialHomeomorph M' H'} {P : (H → H') → Set H → H → Prop} {g g' : M → M'}
  {s t : Set M} {x : M} {Q : (H → H) → Set H → H → Prop}

/-
**StructureGroupoid.liftPropWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 `StructureGr
oupoid`。
形式化陈述：liftPropWithinAt_univ : LiftPropWithinAt P g univ x ↔ LiftPropAt P g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftPropWithinAt_univ : LiftPropWithinAt P g univ x ↔ LiftPropAt P g x := Iff.rfl
/-
**StructureGroupoid.liftPropOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid
`。
形式化陈述：liftPropOn_univ : LiftPropOn P g univ ↔ LiftProp P g
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem liftPropOn_univ : LiftPropOn P g univ ↔ LiftProp P g := by
  simp [LiftPropOn, LiftProp, LiftPropAt]
/-
**StructureGroupoid.liftPropWithinAt_self** 是 Mathlib 中的一个定理，位于命名空间 `StructureGr
oupoid`。
形式化陈述：liftPropWithinAt_self {f : H -> H'} {s : Set H} {x : H} : LiftPropWithinAt
 P f s x ↔ ContinuousWithinAt f s x ∧ P f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.liftPropWithinAt_iff'`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
-/
theorem liftPropWithinAt_self {f : H → H'} {s : Set H} {x : H} :
    LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P f s x :=
  liftPropWithinAt_iff' ..
/-
**StructureGroupoid.liftPropWithinAt_self_source** 是 Mathlib 中的一个定理，位于命名空间 `Stru
ctureGroupoid`。
形式化陈述：liftPropWithinAt_self_source {f : H -> M'} {s : Set H} {x : H} : LiftPropW
ithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P (chartAt H' (f x) ∘ f) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.liftPropWithinAt_iff'`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
-/
theorem liftPropWithinAt_self_source {f : H → M'} {s : Set H} {x : H} :
    LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P (chartAt H' (f x) ∘ f) s x :=
  liftPropWithinAt_iff' ..
/-
**StructureGroupoid.liftPropWithinAt_self_target** 是 Mathlib 中的一个定理，位于命名空间 `Stru
ctureGroupoid`。
形式化陈述：liftPropWithinAt_self_target {f : M -> H'} : LiftPropWithinAt P f s x ↔ Co
ntinuousWithinAt f s x ∧ P (f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (
chartAt H x x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.liftPropWithinAt_iff'`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
-/
theorem liftPropWithinAt_self_target {f : M → H'} :
    LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧
      P (f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x) :=
  liftPropWithinAt_iff' ..

namespace LocalInvariantProp

section
variable (hG : G.LocalInvariantProp G' P)
include hG

/-- `LiftPropWithinAt P f s x` is equivalent to a definition where we restrict the set we are
  considering to the domain of the charts at `x` and `f x`. -/
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_iff** 是 Mathlib 中的一个定理，位
于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_iff {f : M -> M'} : LiftPropWithinAt P f s x ↔ Continuous
WithinAt f s x ∧ P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) ((chartAt H x).ta
rget inter (chartAt H x).symm ⁻¹' (s inter f ⁻¹' (chartAt H' (f x)).source)) (ch
artAt H x x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ChartedSpace.liftPropWithinAt_iff'`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_set`：congr_set {s t : Set H} 
{x : H} {f : H -> H'} (hu : s =ᶠ[𝓝 x] t) : P f s x ↔ P f t x
· 使用定理 `OpenPartialHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter`
：preimage_eventuallyEq_target_inter_preimage_inter {e : OpenPartialHomeomorph X 
Y} {s : Set X} {t : Set Z} {x : X} {f : X -> Z} (hf : Continu…
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `chart_source_mem_nhds`：chart_source_mem_nhds (x : M) : (chartAt H x).sou
rce in 𝓝 x

--- 原说明 ---
`LiftPropWithinAt P f s x` is equivalent to a definition where we restrict the s
et we are
  considering to the domain of the charts at `x` and `f x`.
-/
theorem liftPropWithinAt_iff {f : M → M'} :
    LiftPropWithinAt P f s x ↔
      ContinuousWithinAt f s x ∧
        P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm)
          ((chartAt H x).target ∩ (chartAt H x).symm ⁻¹' (s ∩ f ⁻¹' (chartAt H' (f x)).source))
          (chartAt H x x) := by
  rw [liftPropWithinAt_iff']
  refine and_congr_right fun hf ↦ hG.congr_set ?_
  exact OpenPartialHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter hf
    (mem_chart_source H x) (chart_source_mem_nhds H' (f x))
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_source_aux**
 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_indep_chart_source_aux (g : M -> H') (he : e in G.maximal
Atlas M) (xe : x in e.source) : P (g ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻
¹' s) (chartAt H x x) ↔ P (g ∘ e.symm) (e.symm ⁻¹' s) (e x)
参数：g : M -> H'；he : e in G.maximalAtlas M；xe : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StructureGroupoid.LocalInvariantProp.right_invariance`：right_invariance 
{s : Set H} {x : H} {f : H -> H'} {e : OpenPartialHomeomorph H H} (he : e in G) 
(hxe : x in e.source) : P (f ∘ e.symm) (e.s…
· 使用定理 `StructureGroupoid.compatible_of_mem_maximalAtlas_right`：StructureGroupoi
d.compatible_of_mem_maximalAtlas_right {e' : OpenPartialHomeomorph M H} {x : M} 
(he' : e' in G.maximalAtlas M) : (chartAt H …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_set_fun`：congr_set_fun {s t :
 Set H} {x : H} {f g : H -> H'} (hu : s =ᶠ[𝓝 x] t) (h : f =ᶠ[𝓝 x] g) : P f s x ↔
 P g t x
· 使用定理 `Filter.Eventually.set_eq`：∀ {α : Type u} {s t : Set α} {l : Filter α}, (
∀ᶠ (x : α) in l, x ∈ s ↔ x ∈ t) → s =ᶠ[l] t
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OpenPartialHomeomorph.eventually_nhds'`：eventually_nhds' {x : X} (p : X 
-> Prop) (hx : x in e.source) : (forallᶠ y in 𝓝 (e x), p (e.symm y)) ↔ forallᶠ x
 in 𝓝 x, p x
· 使用定理 `OpenPartialHomeomorph.eventually_left_inverse`：eventually_left_inverse {
x} (hx : x in e.source) : forallᶠ y in 𝓝 x, e.symm (e y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftPropWithinAt_indep_chart_source_aux (g : M → H')
    (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source) :
    P (g ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x) ↔
      P (g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [← hG.right_invariance (compatible_of_mem_maximalAtlas_right (x := x) he)]; swap
  · simp [xe]
  simp only [OpenPartialHomeomorph.trans_apply, mem_chart_source, OpenPartialHomeomorph.left_inv]
  apply hG.congr_set_fun
  · refine (eventually_of_mem ?_ fun y (hy : y ∈ e.symm ⁻¹' (chartAt H x).source) ↦ ?_).set_eq
    · refine (e.symm.continuousAt <| e.mapsTo xe).preimage_mem_nhds
        ((chartAt H x).open_source.mem_nhds ?_)
      simp_rw [e.left_inv xe, mem_chart_source H x]
    simp_rw [mem_preimage, OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
      Function.comp_apply, (chartAt H x).left_inv hy]
  · refine ((e.eventually_nhds' _ xe).mpr <| (chartAt H x).eventually_left_inverse
      (mem_chart_source H x)).mono fun y hy ↦ ?_
    simp [hy]
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_target_aux2*
* 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_indep_chart_target_aux2 (g : H -> M') {x : H} {s : Set H}
 (hf : f in G'.maximalAtlas M') (xf : g x in f.source) (hgs : ContinuousWithinAt
 g s x) : P ((chartAt H' (g x)) ∘ g) s x ↔ P (f ∘ g) s x
参数：g : H -> M'；hf : f in G'.maximalAtlas M'；xf : g x in f.source；hgs : Continuou
sWithinAt g s x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StructureGroupoid.LocalInvariantProp.left_invariance`：left_invariance {s
 : Set H} {x : H} {f : H -> H'} {e' : OpenPartialHomeomorph H' H'} (he' : e' in 
G') (hfs : ContinuousWithinAt f s x) (hxe'…
· 使用定理 `StructureGroupoid.compatible_of_mem_maximalAtlas_right`：StructureGroupoi
d.compatible_of_mem_maximalAtlas_right {e' : OpenPartialHomeomorph M H} {x : M} 
(he' : e' in G.maximalAtlas M) : (chartAt H …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_iff_nhdsWithin`：congr_iff_nhd
sWithin {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g 
x) : P f s x ↔ P g s x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `OpenPartialHomeomorph.eventually_left_inverse`：eventually_left_inverse {
x} (hx : x in e.source) : forallᶠ y in 𝓝 x, e.symm (e y) = y
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftPropWithinAt_indep_chart_target_aux2 (g : H → M') {x : H} {s : Set H}
    (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) (hgs : ContinuousWithinAt g s x) :
    P ((chartAt H' (g x)) ∘ g) s x ↔ P (f ∘ g) s x := by
  have hcont : ContinuousWithinAt ((chartAt H' (g x)) ∘ g) s x :=
    ((chartAt H' (g x)).continuousAt (by simp)).comp_continuousWithinAt hgs
  rw [← hG.left_invariance (compatible_of_mem_maximalAtlas_right (x := g x) hf) hcont
      (by simp [xf, mfld_simps])]
  refine hG.congr_iff_nhdsWithin ?_ (by simp)
  exact (hgs.eventually <| (chartAt H' (g x)).eventually_left_inverse
    (mem_chart_source H' (g x))).mono fun y ↦ congr_arg f
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_target_aux**
 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_indep_chart_target_aux {g : X -> M'} {e : OpenPartialHome
omorph X H} {x : X} {s : Set X} (xe : x in e.source) (hf : f in G'.maximalAtlas 
M') (xf : g x in f.source) (hgs : ContinuousWithinAt g s x) : P ((chartAt H' (g 
x)) ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x)
参数：xe : x in e.source；hf : f in G'.maximalAtlas M'；xf : g x in f.source；hgs : Co
ntinuousWithinAt g s x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_target
_aux2`：liftPropWithinAt_indep_chart_target_aux2 (g : H -> M') {x : H} {s : Set H
} (hf : f in G'.maximalAtlas M') (xf : g x in f.source) (hgs : Cont…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem liftPropWithinAt_indep_chart_target_aux {g : X → M'} {e : OpenPartialHomeomorph X H} {x : X}
    {s : Set X} (xe : x ∈ e.source)
    (hf : f ∈ G'.maximalAtlas M') (xf : g x ∈ f.source) (hgs : ContinuousWithinAt g s x) :
    P ((chartAt H' (g x)) ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x)
      ↔ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [← e.left_inv xe] at xf hgs
  rw [← hG.liftPropWithinAt_indep_chart_target_aux2 (g ∘ e.symm) hf xf]
  · simp [xe]
  · exact hgs.comp (e.symm.continuousAt <| e.mapsTo xe).continuousWithinAt Subset.rfl

/-- If a property of a germ of function `g` on a pointed set `(s, x)` is invariant under the
structure groupoid (by composition in the source space and in the target space), then
expressing it in charted spaces does not depend on the element of the maximal atlas one uses
both in the source and in the target manifolds, provided they are defined around `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the local behavior
of `g` at `x` cannot be captured with a chart in the target). Version where one of the
charts is `chartAt`. -/
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_aux'** 是 Mat
hlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_indep_chart_aux' (he : e in G.maximalAtlas M) (xe : x in 
e.source) (hf : f in G'.maximalAtlas M') (xf : g x in f.source) (hgs : Continuou
sWithinAt g s x) : P ((chartAt H' (g x)) ∘ g ∘ (chartAt H x).symm) ((chartAt H x
).symm ⁻¹' s) (chartAt H x x) ↔ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x)
参数：he : e in G.maximalAtlas M；xe : x in e.source；hf : f in G'.maximalAtlas M'；xf
 : g x in f.source；hgs : ContinuousWithinAt g s x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_source
_aux`：liftPropWithinAt_indep_chart_source_aux (g : M -> H') (he : e in G.maximal
Atlas M) (xe : x in e.source) : P (g ∘ (chartAt H x).symm) ((chart…
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_target
_aux`：liftPropWithinAt_indep_chart_target_aux {g : X -> M'} {e : OpenPartialHome
omorph X H} {x : X} {s : Set X} (xe : x in e.source) (hf : f in G'…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If a property of a germ of function `g` on a pointed set `(s, x)` is invariant u
nder the
structure groupoid (by composition in the source space and in the target space),
 then
expressing it in charted spaces does not depend on the element of the maximal at
las one uses
both in the source and in the target manifolds, provided they are defined around
 `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the l
ocal behavior
of `g` at `x` cannot be captured with a chart in the target). Version where one 
of the
charts is `chartAt`.
-/
theorem liftPropWithinAt_indep_chart_aux' (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source)
    (hf : f ∈ G'.maximalAtlas M') (xf : g x ∈ f.source)
    (hgs : ContinuousWithinAt g s x) :
    P ((chartAt H' (g x)) ∘ g ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x)
      ↔ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [← Function.comp_assoc,
    hG.liftPropWithinAt_indep_chart_source_aux ((chartAt H' (g x)) ∘ g) he xe,
    Function.comp_assoc, hG.liftPropWithinAt_indep_chart_target_aux xe hf xf hgs]

/-- If a property of a germ of function `g` on a pointed set `(s, x)` is invariant under the
structure groupoid (by composition in the source space and in the target space), then
expressing it in charted spaces does not depend on the element of the maximal atlas one uses
both in the source and in the target manifolds, provided they are defined around `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the local behavior
of `g` at `x` cannot be captured with a chart in the target). -/
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_aux** 是 Math
lib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_indep_chart_aux (he : e in G.maximalAtlas M) (xe : x in e
.source) (he' : e' in G.maximalAtlas M) (xe' : x in e'.source) (hf : f in G'.max
imalAtlas M') (xf : g x in f.source) (hf' : f' in G'.maximalAtlas M') (xf' : g x
 in f'.source) (hgs : ContinuousWithinAt g s x) : P (f ∘ g ∘ e.symm) (e.symm ⁻¹'
 s) (e x) ↔ P (f' ∘ g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x)
参数：he : e in G.maximalAtlas M；xe : x in e.source；he' : e' in G.maximalAtlas M；xe
' : x in e'.source；hf : f in G'.maximalAtlas M'；xf : g x in f.source；hf' : f' in
 G'.maximalAtlas M'；xf' : g x in f'.source；hgs : ContinuousWithinAt g s x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_aux'`：
liftPropWithinAt_indep_chart_aux' (he : e in G.maximalAtlas M) (xe : x in e.sour
ce) (hf : f in G'.maximalAtlas M') (xf : g x in f.source) (h…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If a property of a germ of function `g` on a pointed set `(s, x)` is invariant u
nder the
structure groupoid (by composition in the source space and in the target space),
 then
expressing it in charted spaces does not depend on the element of the maximal at
las one uses
both in the source and in the target manifolds, provided they are defined around
 `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the l
ocal behavior
of `g` at `x` cannot be captured with a chart in the target).
-/
theorem liftPropWithinAt_indep_chart_aux (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source)
    (he' : e' ∈ G.maximalAtlas M) (xe' : x ∈ e'.source) (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) (hf' : f' ∈ G'.maximalAtlas M') (xf' : g x ∈ f'.source)
    (hgs : ContinuousWithinAt g s x) :
    P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (f' ∘ g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x) := by
  rw [← liftPropWithinAt_indep_chart_aux' hG he' xe' hf' xf' hgs,
    liftPropWithinAt_indep_chart_aux' hG he xe hf xf hgs]
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart** 是 Mathlib 
中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_indep_chart (he : e in G.maximalAtlas M) (xe : x in e.sou
rce) (hf : f in G'.maximalAtlas M') (xf : g x in f.source) : LiftPropWithinAt P 
g s x ↔ ContinuousWithinAt g s x ∧ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x)
参数：he : e in G.maximalAtlas M；xe : x in e.source；hf : f in G'.maximalAtlas M'；xf
 : g x in f.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_aux'`：
liftPropWithinAt_indep_chart_aux' (he : e in G.maximalAtlas M) (xe : x in e.sour
ce) (hf : f in G'.maximalAtlas M') (xf : g x in f.source) (h…
-/
theorem liftPropWithinAt_indep_chart
    (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source) (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) :
    LiftPropWithinAt P g s x ↔
    ContinuousWithinAt g s x ∧ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  simp only [liftPropWithinAt_iff']
  exact and_congr_right <| fun h ↦ hG.liftPropWithinAt_indep_chart_aux' he xe hf xf h

/-- A version of `liftPropWithinAt_indep_chart`, only for the source. -/
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_source** 是 M
athlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_indep_chart_source (he : e in G.maximalAtlas M) (xe : x i
n e.source) : LiftPropWithinAt P g s x ↔ LiftPropWithinAt P (g ∘ e.symm) (e.symm
 ⁻¹' s) (e x)
参数：he : e in G.maximalAtlas M；xe : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.liftPropWithinAt_self_source`：liftPropWithinAt_self_so
urce {f : H -> M'} {s : Set H} {x : H} : LiftPropWithinAt P f s x ↔ ContinuousWi
thinAt f s x ∧ P (chartAt H' (f x) ∘…
· 使用定理 `ChartedSpace.liftPropWithinAt_iff'`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
· 使用定理 `OpenPartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_rig
ht`：continuousWithinAt_iff_continuousWithinAt_comp_right {f : Y -> Z} {s : Set Y
} {x : Y} (h : x in e.target) : ContinuousWithinAt f s x ↔ Conti…
· 使用定理 `OpenPartialHomeomorph.symm_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph 
X Y), e.symm.symm = e
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_source
_aux`：liftPropWithinAt_indep_chart_source_aux (g : M -> H') (he : e in G.maximal
Atlas M) (xe : x in e.source) : P (g ∘ (chartAt H x).symm) ((chart…

--- 原说明 ---
A version of `liftPropWithinAt_indep_chart`, only for the source.
-/
theorem liftPropWithinAt_indep_chart_source (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source) :
    LiftPropWithinAt P g s x ↔ LiftPropWithinAt P (g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [liftPropWithinAt_self_source, liftPropWithinAt_iff',
    e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right xe, e.symm_symm]
  refine and_congr Iff.rfl ?_
  rw [Function.comp_apply, e.left_inv xe, ← Function.comp_assoc,
    hG.liftPropWithinAt_indep_chart_source_aux (chartAt _ (g x) ∘ g) he xe, Function.comp_assoc]

/-- A version of `liftPropWithinAt_indep_chart`, only for the target. -/
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_target** 是 M
athlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_indep_chart_target (hf : f in G'.maximalAtlas M') (xf : g
 x in f.source) : LiftPropWithinAt P g s x ↔ ContinuousWithinAt g s x ∧ LiftProp
WithinAt P (f ∘ g) s x
参数：hf : f in G'.maximalAtlas M'；xf : g x in f.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.liftPropWithinAt_self_target`：liftPropWithinAt_self_ta
rget {f : M -> H'} : LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P (f 
∘ (chartAt H x).symm) ((chartAt H x)…
· 使用定理 `ChartedSpace.liftPropWithinAt_iff'`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_target
_aux`：liftPropWithinAt_indep_chart_target_aux {g : X -> M'} {e : OpenPartialHome
omorph X H} {x : X} {s : Set X} (xe : x in e.source) (hf : f in G'…
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce

--- 原说明 ---
A version of `liftPropWithinAt_indep_chart`, only for the target.
-/
theorem liftPropWithinAt_indep_chart_target (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) :
    LiftPropWithinAt P g s x ↔ ContinuousWithinAt g s x ∧ LiftPropWithinAt P (f ∘ g) s x := by
  rw [liftPropWithinAt_self_target, liftPropWithinAt_iff', and_congr_right_iff]
  intro hg
  simp_rw [(f.continuousAt xf).comp_continuousWithinAt hg, true_and]
  exact hG.liftPropWithinAt_indep_chart_target_aux (mem_chart_source _ _) hf xf hg

/-- A version of `liftPropWithinAt_indep_chart`, that uses `LiftPropWithinAt` on both sides. -/
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart'** 是 Mathlib
 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_indep_chart' (he : e in G.maximalAtlas M) (xe : x in e.so
urce) (hf : f in G'.maximalAtlas M') (xf : g x in f.source) : LiftPropWithinAt P
 g s x ↔ ContinuousWithinAt g s x ∧ LiftPropWithinAt P (f ∘ g ∘ e.symm) (e.symm 
⁻¹' s) (e x)
参数：he : e in G.maximalAtlas M；xe : x in e.source；hf : f in G'.maximalAtlas M'；xf
 : g x in f.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart`：liftP
ropWithinAt_indep_chart (he : e in G.maximalAtlas M) (xe : x in e.source) (hf : 
f in G'.maximalAtlas M') (xf : g x in f.source) : LiftP…
· 使用定理 `StructureGroupoid.liftPropWithinAt_self`：liftPropWithinAt_self {f : H ->
 H'} {s : Set H} {x : H} : LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧
 P f s x
· 使用定理 `and_left_comm`：∀ {a b c : Prop}, a ∧ b ∧ c ↔ b ∧ a ∧ c
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `and_iff_right_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ b) ↔ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OpenPartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_rig
ht`：continuousWithinAt_iff_continuousWithinAt_comp_right {f : Y -> Z} {s : Set Y
} {x : Y} (h : x in e.target) : ContinuousWithinAt f s x ↔ Conti…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …

--- 原说明 ---
A version of `liftPropWithinAt_indep_chart`, that uses `LiftPropWithinAt` on bot
h sides.
-/
theorem liftPropWithinAt_indep_chart'
    (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source) (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) :
    LiftPropWithinAt P g s x ↔
      ContinuousWithinAt g s x ∧ LiftPropWithinAt P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [hG.liftPropWithinAt_indep_chart he xe hf xf, liftPropWithinAt_self, and_left_comm,
    Iff.comm, and_iff_right_iff_imp]
  intro h
  have h1 := (e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right xe).mp h.1
  have : ContinuousAt f ((g ∘ e.symm) (e x)) := by
    simp_rw [Function.comp, e.left_inv xe, f.continuousAt xf]
  exact this.comp_continuousWithinAt h1
/-
**StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart** 是 Mathlib 中的一个定理
，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropOn_indep_chart (he : e in G.maximalAtlas M) (hf : f in G'.maximalA
tlas M') (h : LiftPropOn P g s) {y : H} (hy : y in e.target inter e.symm ⁻¹' (s 
inter g ⁻¹' f.source)) : P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) y
参数：he : e in G.maximalAtlas M；hf : f in G'.maximalAtlas M'；h : LiftPropOn P g s；
hy : y in e.target inter e.symm ⁻¹' (s inter g ⁻¹' f.source)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart`：liftP
ropWithinAt_indep_chart (he : e in G.maximalAtlas M) (xe : x in e.source) (hf : 
f in G'.maximalAtlas M') (xf : g x in f.source) : LiftP…
· 使用定理 `OpenPartialHomeomorph.mapsTo_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorp
h X Y), Set.MapsTo (↑e.…
-/
theorem liftPropOn_indep_chart (he : e ∈ G.maximalAtlas M)
    (hf : f ∈ G'.maximalAtlas M') (h : LiftPropOn P g s) {y : H}
    (hy : y ∈ e.target ∩ e.symm ⁻¹' (s ∩ g ⁻¹' f.source)) :
    P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) y := by
  convert! ((hG.liftPropWithinAt_indep_chart he (e.mapsTo_symm hy.1) hf hy.2.2).1 (h _ hy.2.1)).2
  rw [e.right_inv hy.1]
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter'** 是 Mathlib 中的一个定
理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_inter' (ht : t in 𝓝[s] x) : LiftPropWithinAt P g (s inter
 t) x ↔ LiftPropWithinAt P g s x
参数：ht : t in 𝓝[s] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ChartedSpace.liftPropWithinAt_iff'`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
· 使用定理 `continuousWithinAt_inter'`：continuousWithinAt_inter' (h : t in 𝓝[s] x) :
 ContinuousWithinAt f (s inter t) x ↔ ContinuousWithinAt f s x
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_set`：congr_set {s t : Set H} 
{x : H} {f : H -> H'} (hu : s =ᶠ[𝓝 x] t) : P f s x ↔ P f t x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.eventually_nhds'`：eventually_nhds' {x : X} (p : X 
-> Prop) (hx : x in e.source) : (forallᶠ y in 𝓝 (e x), p (e.symm y)) ↔ forallᶠ x
 in 𝓝 x, p x
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `Filter.EventuallyEq.mem_iff`：∀ {α : Type u} {s t : Set α} {l : Filter α}
, s =ᶠ[l] t → ∀ᶠ (x : α) in l, x ∈ s ↔ x ∈ t
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_eventuallyEq`：mem_nhdsWithin_iff_eventuallyEq {s t : 
Set α} {x : α} : t in 𝓝[s] x ↔ s =ᶠ[𝓝 x] (s inter t : Set α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftPropWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    LiftPropWithinAt P g (s ∩ t) x ↔ LiftPropWithinAt P g s x := by
  rw [liftPropWithinAt_iff', liftPropWithinAt_iff', continuousWithinAt_inter' ht, hG.congr_set]
  simp_rw [eventuallyEq_set, mem_preimage,
    (chartAt _ x).eventually_nhds' (fun x ↦ x ∈ s ∩ t ↔ x ∈ s) (mem_chart_source _ x)]
  exact (mem_nhdsWithin_iff_eventuallyEq.mp ht).symm.mem_iff
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter** 是 Mathlib 中的一个定理
，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_inter (ht : t in 𝓝 x) : LiftPropWithinAt P g (s inter t) 
x ↔ LiftPropWithinAt P g s x
参数：ht : t in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter'`：liftPropWi
thinAt_inter' (ht : t in 𝓝[s] x) : LiftPropWithinAt P g (s inter t) x ↔ LiftProp
WithinAt P g s x
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
-/
theorem liftPropWithinAt_inter (ht : t ∈ 𝓝 x) :
    LiftPropWithinAt P g (s ∩ t) x ↔ LiftPropWithinAt P g s x :=
  hG.liftPropWithinAt_inter' (mem_nhdsWithin_of_mem_nhds ht)
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_set** 是 Mathlib 中的
一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_congr_set (hu : s =ᶠ[𝓝 x] t) : LiftPropWithinAt P g s x ↔
 LiftPropWithinAt P g t x
参数：hu : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter`：liftPropWit
hinAt_inter (ht : t in 𝓝 x) : LiftPropWithinAt P g (s inter t) x ↔ LiftPropWithi
nAt P g s x
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem liftPropWithinAt_congr_set (hu : s =ᶠ[𝓝 x] t) :
    LiftPropWithinAt P g s x ↔ LiftPropWithinAt P g t x := by
  rw [← hG.liftPropWithinAt_inter (s := s) hu, ← hG.liftPropWithinAt_inter (s := t) hu,
    ← eq_iff_iff]
  congr 1
  aesop
/-
**StructureGroupoid.LocalInvariantProp.liftPropAt_of_liftPropWithinAt** 是 Mathli
b 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropAt_of_liftPropWithinAt (h : LiftPropWithinAt P g s x) (hs : s in 𝓝
 x) : LiftPropAt P g x
参数：h : LiftPropWithinAt P g s x；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter`：liftPropWit
hinAt_inter (ht : t in 𝓝 x) : LiftPropWithinAt P g (s inter t) x ↔ LiftPropWithi
nAt P g s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem liftPropAt_of_liftPropWithinAt (h : LiftPropWithinAt P g s x) (hs : s ∈ 𝓝 x) :
    LiftPropAt P g x := by
  rwa [← univ_inter s, hG.liftPropWithinAt_inter hs] at h
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_of_liftPropAt_of_mem_nhd
s** 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_of_liftPropAt_of_mem_nhds (h : LiftPropAt P g x) (hs : s 
in 𝓝 x) : LiftPropWithinAt P g s x
参数：h : LiftPropAt P g x；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter`：liftPropWit
hinAt_inter (ht : t in 𝓝 x) : LiftPropWithinAt P g (s inter t) x ↔ LiftPropWithi
nAt P g s x
-/
theorem liftPropWithinAt_of_liftPropAt_of_mem_nhds (h : LiftPropAt P g x) (hs : s ∈ 𝓝 x) :
    LiftPropWithinAt P g s x := by
  rwa [← univ_inter s, hG.liftPropWithinAt_inter hs]
/-
**StructureGroupoid.LocalInvariantProp.liftPropOn_of_locally_liftPropOn** 是 Math
lib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropOn_of_locally_liftPropOn (h : forall x in s, exists u, IsOpen u ∧ 
x in u ∧ LiftPropOn P g (s inter u)) : LiftPropOn P g s
参数：h : forall x in s, exists u, IsOpen u ∧ x in u ∧ LiftPropOn P g (s inter u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter`：liftPropWit
hinAt_inter (ht : t in 𝓝 x) : LiftPropWithinAt P g (s inter t) x ↔ LiftPropWithi
nAt P g s x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem liftPropOn_of_locally_liftPropOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ LiftPropOn P g (s ∩ u)) : LiftPropOn P g s := by
  intro x hx
  rcases h x hx with ⟨u, u_open, xu, hu⟩
  have := hu x ⟨hx, xu⟩
  rwa [hG.liftPropWithinAt_inter] at this
  exact u_open.mem_nhds xu
/-
**StructureGroupoid.LocalInvariantProp.liftProp_of_locally_liftPropOn** 是 Mathli
b 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftProp_of_locally_liftPropOn (h : forall x, exists u, IsOpen u ∧ x in u 
∧ LiftPropOn P g u) : LiftProp P g
参数：h : forall x, exists u, IsOpen u ∧ x in u ∧ LiftPropOn P g u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StructureGroupoid.liftPropOn_univ`：liftPropOn_univ : LiftPropOn P g univ
 ↔ LiftProp P g
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_of_locally_liftPropOn`：l
iftPropOn_of_locally_liftPropOn (h : forall x in s, exists u, IsOpen u ∧ x in u 
∧ LiftPropOn P g (s inter u)) : LiftPropOn P g s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem liftProp_of_locally_liftPropOn (h : ∀ x, ∃ u, IsOpen u ∧ x ∈ u ∧ LiftPropOn P g u) :
    LiftProp P g := by
  rw [← liftPropOn_univ]
  refine hG.liftPropOn_of_locally_liftPropOn fun x _ ↦ ?_
  simp [h x]
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_of_eventuallyEq** 
是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_congr_of_eventuallyEq (h : LiftPropWithinAt P g s x) (h₁ 
: g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) : LiftPropWithinAt P g' s x
参数：h : LiftPropWithinAt P g s x；h₁ : g' =ᶠ[𝓝[s] x] g；hx : g' x = g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.congr_of_eventuallyEq`：ContinuousWithinAt.congr_of_ev
entuallyEq (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : g x = f x)
 : ContinuousWithinAt g s x
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_nhdsWithin'`：congr_nhdsWithin
' {s : Set H} {x : H} {f g : H -> H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x) (hP
 : P g s x) : P f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.eventually_nhdsWithin'`：eventually_nhdsWithin' {x 
: X} (p : X -> Prop) {s : Set X} (hx : x in e.source) : (forallᶠ y in 𝓝[e.symm ⁻
¹' s] e x, p (e.symm y)) ↔ forallᶠ…
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
-/
theorem liftPropWithinAt_congr_of_eventuallyEq (h : LiftPropWithinAt P g s x) (h₁ : g' =ᶠ[𝓝[s] x] g)
    (hx : g' x = g x) : LiftPropWithinAt P g' s x := by
  refine ⟨h.1.congr_of_eventuallyEq h₁ hx, ?_⟩
  refine hG.congr_nhdsWithin' ?_
    (by simp_rw [Function.comp_apply, (chartAt H x).left_inv (mem_chart_source H x), hx]) h.2
  simp_rw [EventuallyEq, Function.comp_apply]
  rw [(chartAt H x).eventually_nhdsWithin'
    (fun y ↦ chartAt H' (g' x) (g' y) = chartAt H' (g x) (g y)) (mem_chart_source H x)]
  exact h₁.mono fun y hy ↦ by rw [hx, hy]
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of
_mem** 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_congr_of_eventuallyEq_of_mem (h : LiftPropWithinAt P g s 
x) (h₁ : g' =ᶠ[𝓝[s] x] g) (h₂ : x in s) : LiftPropWithinAt P g' s x
参数：h : LiftPropWithinAt P g s x；h₁ : g' =ᶠ[𝓝[s] x] g；h₂ : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_of_eventuall
yEq`：liftPropWithinAt_congr_of_eventuallyEq (h : LiftPropWithinAt P g s x) (h₁ :
 g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) : LiftPropWithinAt P g' s x
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
-/
theorem liftPropWithinAt_congr_of_eventuallyEq_of_mem (h : LiftPropWithinAt P g s x)
    (h₁ : g' =ᶠ[𝓝[s] x] g) (h₂ : x ∈ s) : LiftPropWithinAt P g' s x :=
  liftPropWithinAt_congr_of_eventuallyEq hG h h₁ (mem_of_mem_nhdsWithin h₂ h₁ :)
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff_of_eventuallyE
q** 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g'
 x = g x) : LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x
参数：h₁ : g' =ᶠ[𝓝[s] x] g；hx : g' x = g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_of_eventuall
yEq`：liftPropWithinAt_congr_of_eventuallyEq (h : LiftPropWithinAt P g s x) (h₁ :
 g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) : LiftPropWithinAt P g' s x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem liftPropWithinAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  ⟨fun h ↦ hG.liftPropWithinAt_congr_of_eventuallyEq h h₁.symm hx.symm,
    fun h ↦ hG.liftPropWithinAt_congr_of_eventuallyEq h h₁ hx⟩
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff** 是 Mathlib 中的
一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_congr_iff (h₁ : forall y in s, g' y = g y) (hx : g' x = g
 x) : LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x
参数：h₁ : forall y in s, g' y = g y；hx : g' x = g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff_of_event
uallyEq`：liftPropWithinAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx :
 g' x = g x) : LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
-/
theorem liftPropWithinAt_congr_iff (h₁ : ∀ y ∈ s, g' y = g y) (hx : g' x = g x) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  hG.liftPropWithinAt_congr_iff_of_eventuallyEq (eventually_nhdsWithin_of_forall h₁) hx
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff_of_mem** 是 Mat
hlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_congr_iff_of_mem (h₁ : forall y in s, g' y = g y) (hx : x
 in s) : LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x
参数：h₁ : forall y in s, g' y = g y；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff_of_event
uallyEq`：liftPropWithinAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx :
 g' x = g x) : LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
-/
theorem liftPropWithinAt_congr_iff_of_mem (h₁ : ∀ y ∈ s, g' y = g y) (hx : x ∈ s) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  hG.liftPropWithinAt_congr_iff_of_eventuallyEq (eventually_nhdsWithin_of_forall h₁) (h₁ _ hx)
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr** 是 Mathlib 中的一个定理
，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_congr (h : LiftPropWithinAt P g s x) (h₁ : forall y in s,
 g' y = g y) (hx : g' x = g x) : LiftPropWithinAt P g' s x
参数：h : LiftPropWithinAt P g s x；h₁ : forall y in s, g' y = g y；hx : g' x = g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff`：liftPro
pWithinAt_congr_iff (h₁ : forall y in s, g' y = g y) (hx : g' x = g x) : LiftPro
pWithinAt P g' s x ↔ LiftPropWithinAt P g s x
-/
theorem liftPropWithinAt_congr (h : LiftPropWithinAt P g s x) (h₁ : ∀ y ∈ s, g' y = g y)
    (hx : g' x = g x) : LiftPropWithinAt P g' s x :=
  (hG.liftPropWithinAt_congr_iff h₁ hx).mpr h
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_of_mem** 是 Mathlib
 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_congr_of_mem (h : LiftPropWithinAt P g s x) (h₁ : forall 
y in s, g' y = g y) (hx : x in s) : LiftPropWithinAt P g' s x
参数：h : LiftPropWithinAt P g s x；h₁ : forall y in s, g' y = g y；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff`：liftPro
pWithinAt_congr_iff (h₁ : forall y in s, g' y = g y) (hx : g' x = g x) : LiftPro
pWithinAt P g' s x ↔ LiftPropWithinAt P g s x
-/
theorem liftPropWithinAt_congr_of_mem (h : LiftPropWithinAt P g s x) (h₁ : ∀ y ∈ s, g' y = g y)
    (hx : x ∈ s) : LiftPropWithinAt P g' s x :=
  (hG.liftPropWithinAt_congr_iff h₁ (h₁ _ hx)).mpr h
/-
**StructureGroupoid.LocalInvariantProp.liftPropAt_congr_iff_of_eventuallyEq** 是 
Mathlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝 x] g) : LiftPropAt P g'
 x ↔ LiftPropAt P g x
参数：h₁ : g' =ᶠ[𝓝 x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff_of_event
uallyEq`：liftPropWithinAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx :
 g' x = g x) : LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
-/
theorem liftPropAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝 x] g) :
    LiftPropAt P g' x ↔ LiftPropAt P g x :=
  hG.liftPropWithinAt_congr_iff_of_eventuallyEq (by simp_rw [nhdsWithin_univ, h₁]) h₁.eq_of_nhds
/-
**StructureGroupoid.LocalInvariantProp.liftPropAt_congr_of_eventuallyEq** 是 Math
lib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropAt_congr_of_eventuallyEq (h : LiftPropAt P g x) (h₁ : g' =ᶠ[𝓝 x] g
) : LiftPropAt P g' x
参数：h : LiftPropAt P g x；h₁ : g' =ᶠ[𝓝 x] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_congr_iff_of_eventuallyE
q`：liftPropAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝 x] g) : LiftPropAt P g' x 
↔ LiftPropAt P g x
-/
theorem liftPropAt_congr_of_eventuallyEq (h : LiftPropAt P g x) (h₁ : g' =ᶠ[𝓝 x] g) :
    LiftPropAt P g' x :=
  (hG.liftPropAt_congr_iff_of_eventuallyEq h₁).mpr h
/-
**StructureGroupoid.LocalInvariantProp.liftPropOn_congr** 是 Mathlib 中的一个定理，位于命名空
间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropOn_congr (h : LiftPropOn P g s) (h₁ : forall y in s, g' y = g y) :
 LiftPropOn P g' s
参数：h : LiftPropOn P g s；h₁ : forall y in s, g' y = g y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr`：liftPropWit
hinAt_congr (h : LiftPropWithinAt P g s x) (h₁ : forall y in s, g' y = g y) (hx 
: g' x = g x) : LiftPropWithinAt P g' s x
-/
theorem liftPropOn_congr (h : LiftPropOn P g s) (h₁ : ∀ y ∈ s, g' y = g y) : LiftPropOn P g' s :=
  fun x hx ↦ hG.liftPropWithinAt_congr (h x hx) h₁ (h₁ x hx)
/-
**StructureGroupoid.LocalInvariantProp.liftPropOn_congr_iff** 是 Mathlib 中的一个定理，位
于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropOn_congr_iff (h₁ : forall y in s, g' y = g y) : LiftPropOn P g' s 
↔ LiftPropOn P g s
参数：h₁ : forall y in s, g' y = g y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_congr`：liftPropOn_congr 
(h : LiftPropOn P g s) (h₁ : forall y in s, g' y = g y) : LiftPropOn P g' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem liftPropOn_congr_iff (h₁ : ∀ y ∈ s, g' y = g y) : LiftPropOn P g' s ↔ LiftPropOn P g s :=
  ⟨fun h ↦ hG.liftPropOn_congr h fun y hy ↦ (h₁ y hy).symm, fun h ↦ hG.liftPropOn_congr h h₁⟩

end

/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono_of_mem_nhdsWithin**
 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_mono_of_mem_nhdsWithin (mono_of_mem_nhdsWithin : forall ⦃
s x t⦄ ⦃f : H -> H'⦄, s in 𝓝[t] x -> P f s x -> P f t x) (h : LiftPropWithinAt P
 g s x) (hst : s in 𝓝[t] x) : LiftPropWithinAt P g t x
参数：mono_of_mem_nhdsWithin : forall ⦃s x t⦄ ⦃f : H -> H'⦄, s in 𝓝[t] x -> P f s x
 -> P f t x；h : LiftPropWithinAt P g s x；hst : s in 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mono_of_mem_nhdsWithin`：ContinuousWithinAt.mono_of_me
m_nhdsWithin (h : ContinuousWithinAt f t x) (hs : t in 𝓝[s] x) : ContinuousWithi
nAt f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.map_nhdsWithin_preimage_eq`：map_nhdsWithin_preimag
e_eq {x} (hx : x in e.source) (s : Set Y) : map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x
· 使用定理 `mem_chart_target`：mem_chart_target (x : M) : chartAt H x x in (chartAt H
 x).target
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem liftPropWithinAt_mono_of_mem_nhdsWithin
    (mono_of_mem_nhdsWithin : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, s ∈ 𝓝[t] x → P f s x → P f t x)
    (h : LiftPropWithinAt P g s x) (hst : s ∈ 𝓝[t] x) : LiftPropWithinAt P g t x := by
  simp only [liftPropWithinAt_iff'] at h ⊢
  refine ⟨h.1.mono_of_mem_nhdsWithin hst, mono_of_mem_nhdsWithin ?_ h.2⟩
  simp_rw [← mem_map, (chartAt H x).symm.map_nhdsWithin_preimage_eq (mem_chart_target H x),
    (chartAt H x).left_inv (mem_chart_source H x), hst]
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono** 是 Mathlib 中的一个定理，
位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_mono (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -
> P f s x -> P f t x) (h : LiftPropWithinAt P g s x) (hts : t subseteq s) : Lift
PropWithinAt P g t x
参数：mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x；h : L
iftPropWithinAt P g s x；hts : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
-/
theorem liftPropWithinAt_mono (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftPropWithinAt P g s x) (hts : t ⊆ s) : LiftPropWithinAt P g t x := by
  refine ⟨h.1.mono hts, mono (fun y hy ↦ ?_) h.2⟩
  simp only [mfld_simps] at hy
  simp only [hy, hts _, mfld_simps]
/-
**StructureGroupoid.LocalInvariantProp.liftPropWithinAt_of_liftPropAt** 是 Mathli
b 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropWithinAt_of_liftPropAt (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t sub
seteq s -> P f s x -> P f t x) (h : LiftPropAt P g x) : LiftPropWithinAt P g s x
参数：mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x；h : L
iftPropAt P g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono`：liftPropWith
inAt_mono (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t
 x) (h : LiftPropWithinAt P g s x) (hts : t subs…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StructureGroupoid.liftPropWithinAt_univ`：liftPropWithinAt_univ : LiftPro
pWithinAt P g univ x ↔ LiftPropAt P g x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem liftPropWithinAt_of_liftPropAt (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftPropAt P g x) : LiftPropWithinAt P g s x := by
  rw [← liftPropWithinAt_univ] at h
  exact liftPropWithinAt_mono mono h (subset_univ _)
/-
**StructureGroupoid.LocalInvariantProp.liftPropOn_mono** 是 Mathlib 中的一个定理，位于命名空间
 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropOn_mono (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f 
s x -> P f t x) (h : LiftPropOn P g t) (hst : s subseteq t) : LiftPropOn P g s
参数：mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x；h : L
iftPropOn P g t；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono`：liftPropWith
inAt_mono (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t
 x) (h : LiftPropWithinAt P g s x) (hts : t subs…
-/
theorem liftPropOn_mono (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftPropOn P g t) (hst : s ⊆ t) : LiftPropOn P g s :=
  fun x hx ↦ liftPropWithinAt_mono mono (h x (hst hx)) hst
/-
**StructureGroupoid.LocalInvariantProp.liftPropOn_of_liftProp** 是 Mathlib 中的一个定理
，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropOn_of_liftProp (mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s 
-> P f s x -> P f t x) (h : LiftProp P g) : LiftPropOn P g s
参数：mono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x；h : L
iftProp P g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_mono`：liftPropOn_mono (m
ono : forall ⦃s x t⦄ ⦃f : H -> H'⦄, t subseteq s -> P f s x -> P f t x) (h : Lif
tPropOn P g t) (hst : s subseteq t) : Lift…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StructureGroupoid.liftPropOn_univ`：liftPropOn_univ : LiftPropOn P g univ
 ↔ LiftProp P g
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem liftPropOn_of_liftProp (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftProp P g) : LiftPropOn P g s := by
  rw [← liftPropOn_univ] at h
  exact liftPropOn_mono mono h (subset_univ _)
/-
**StructureGroupoid.LocalInvariantProp.liftPropAt_of_mem_maximalAtlas** 是 Mathli
b 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropAt_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q) (hQ : foral
l y, Q id univ y) (he : e in maximalAtlas M G) (hx : x in e.source) : LiftPropAt
 Q e x
参数：hG : G.LocalInvariantProp G Q；hQ : forall y, Q id univ y；he : e in maximalAtl
as M G；hx : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart`：liftP
ropWithinAt_indep_chart (he : e in G.maximalAtlas M) (xe : x in e.source) (hf : 
f in G'.maximalAtlas M') (xf : g x in f.source) : LiftP…
· 使用定理 `StructureGroupoid.id_mem_maximalAtlas`：StructureGroupoid.id_mem_maximalA
tlas : OpenPartialHomeomorph.refl H in G.maximalAtlas H
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr'`：congr' {s : Set H} {x : H} 
{f g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x) : P f s x
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse'`：eventually_right_invers
e' {x} (hx : x in e.source) : forallᶠ y in 𝓝 (e x), e (e.symm y) = y
-/
theorem liftPropAt_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G) (hx : x ∈ e.source) : LiftPropAt Q e x := by
  simp_rw [LiftPropAt, hG.liftPropWithinAt_indep_chart he hx G.id_mem_maximalAtlas (mem_univ _),
    (e.continuousAt hx).continuousWithinAt, true_and]
  exact hG.congr' (e.eventually_right_inverse' hx) (hQ _)
/-
**StructureGroupoid.LocalInvariantProp.liftPropOn_of_mem_maximalAtlas** 是 Mathli
b 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropOn_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q) (hQ : foral
l y, Q id univ y) (he : e in maximalAtlas M G) : LiftPropOn Q e e.source
参数：hG : G.LocalInvariantProp G Q；hQ : forall y, Q id univ y；he : e in maximalAtl
as M G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_of_liftPropAt_of_m
em_nhds`：liftPropWithinAt_of_liftPropAt_of_mem_nhds (h : LiftPropAt P g x) (hs :
 s in 𝓝 x) : LiftPropWithinAt P g s x
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_of_mem_maximalAtlas`：lif
tPropAt_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id
 univ y) (he : e in maximalAtlas M G) (hx : x in e.source…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem liftPropOn_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G) : LiftPropOn Q e e.source := by
  intro x hx
  apply hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds (hG.liftPropAt_of_mem_maximalAtlas hQ he hx)
  exact e.open_source.mem_nhds hx
/-
**StructureGroupoid.LocalInvariantProp.liftPropAt_symm_of_mem_maximalAtlas** 是 M
athlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropAt_symm_of_mem_maximalAtlas {x : H} (hG : G.LocalInvariantProp G Q
) (hQ : forall y, Q id univ y) (he : e in maximalAtlas M G) (hx : x in e.target)
 : LiftPropAt Q e.symm x
参数：hG : G.LocalInvariantProp G Q；hQ : forall y, Q id univ y；he : e in maximalAtl
as M G；hx : x in e.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr'`：congr' {s : Set H} {x : H} 
{f g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x) : P f s x
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse`：eventually_right_inverse
 {x} (hx : x in e.target) : forallᶠ y in 𝓝 x, e (e.symm y) = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ChartedSpace.LiftPropAt.eq_1`：∀ {H : Type u_1} {M : Type u_2} {H' : Type
 u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalSpace M
] [inst_2 : Charte…
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart`：liftP
ropWithinAt_indep_chart (he : e in G.maximalAtlas M) (xe : x in e.source) (hf : 
f in G'.maximalAtlas M') (xf : g x in f.source) : LiftP…
· 使用定理 `StructureGroupoid.id_mem_maximalAtlas`：StructureGroupoid.id_mem_maximalA
tlas : OpenPartialHomeomorph.refl H in G.maximalAtlas H
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.refl_apply`：∀ (X : Type u_7) [inst : TopologicalSp
ace X], ↑(OpenPartialHomeomorph.refl X) = id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem liftPropAt_symm_of_mem_maximalAtlas {x : H}
    (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G)
    (hx : x ∈ e.target) : LiftPropAt Q e.symm x := by
  suffices h : Q (e ∘ e.symm) univ x by
    have : e.symm x ∈ e.source := by simp only [hx, mfld_simps]
    rw [LiftPropAt, hG.liftPropWithinAt_indep_chart G.id_mem_maximalAtlas (mem_univ _) he this]
    refine ⟨(e.symm.continuousAt hx).continuousWithinAt, ?_⟩
    simp only [h, mfld_simps]
  exact hG.congr' (e.eventually_right_inverse hx) (hQ x)
/-
**StructureGroupoid.LocalInvariantProp.liftPropOn_symm_of_mem_maximalAtlas** 是 M
athlib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropOn_symm_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q) (hQ : 
forall y, Q id univ y) (he : e in maximalAtlas M G) : LiftPropOn Q e.symm e.targ
et
参数：hG : G.LocalInvariantProp G Q；hQ : forall y, Q id univ y；he : e in maximalAtl
as M G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_of_liftPropAt_of_m
em_nhds`：liftPropWithinAt_of_liftPropAt_of_mem_nhds (h : LiftPropAt P g x) (hs :
 s in 𝓝 x) : LiftPropWithinAt P g s x
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_symm_of_mem_maximalAtlas
`：liftPropAt_symm_of_mem_maximalAtlas {x : H} (hG : G.LocalInvariantProp G Q) (h
Q : forall y, Q id univ y) (he : e in maximalAtlas M G) (hx : …
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem liftPropOn_symm_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G) : LiftPropOn Q e.symm e.target := by
  intro x hx
  apply hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds
    (hG.liftPropAt_symm_of_mem_maximalAtlas hQ he hx)
  exact e.open_target.mem_nhds hx
/-
**StructureGroupoid.LocalInvariantProp.liftPropAt_chart** 是 Mathlib 中的一个定理，位于命名空
间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropAt_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : f
orall y, Q id univ y) : LiftPropAt Q (chartAt (H
参数：hG : G.LocalInvariantProp G Q；hQ : forall y, Q id univ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_of_mem_maximalAtlas`：lif
tPropAt_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id
 univ y) (he : e in maximalAtlas M G) (hx : x in e.source…
· 使用定理 `StructureGroupoid.chart_mem_maximalAtlas`：StructureGroupoid.chart_mem_ma
ximalAtlas [HasGroupoid M G] (x : M) : chartAt H x in G.maximalAtlas M
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
-/
theorem liftPropAt_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) :
    LiftPropAt Q (chartAt (H := H) x) x :=
  hG.liftPropAt_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (mem_chart_source H x)
/-
**StructureGroupoid.LocalInvariantProp.liftPropOn_chart** 是 Mathlib 中的一个定理，位于命名空
间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropOn_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : f
orall y, Q id univ y) : LiftPropOn Q (chartAt (H
参数：hG : G.LocalInvariantProp G Q；hQ : forall y, Q id univ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_of_mem_maximalAtlas`：lif
tPropOn_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id
 univ y) (he : e in maximalAtlas M G) : LiftPropOn Q e e.…
· 使用定理 `StructureGroupoid.chart_mem_maximalAtlas`：StructureGroupoid.chart_mem_ma
ximalAtlas [HasGroupoid M G] (x : M) : chartAt H x in G.maximalAtlas M
-/
theorem liftPropOn_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) :
    LiftPropOn Q (chartAt (H := H) x) (chartAt (H := H) x).source :=
  hG.liftPropOn_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)
/-
**StructureGroupoid.LocalInvariantProp.liftPropAt_chart_symm** 是 Mathlib 中的一个定理，
位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropAt_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (h
Q : forall y, Q id univ y) : LiftPropAt Q (chartAt (H
参数：hG : G.LocalInvariantProp G Q；hQ : forall y, Q id univ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_symm_of_mem_maximalAtlas
`：liftPropAt_symm_of_mem_maximalAtlas {x : H} (hG : G.LocalInvariantProp G Q) (h
Q : forall y, Q id univ y) (he : e in maximalAtlas M G) (hx : …
· 使用定理 `StructureGroupoid.chart_mem_maximalAtlas`：StructureGroupoid.chart_mem_ma
ximalAtlas [HasGroupoid M G] (x : M) : chartAt H x in G.maximalAtlas M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem liftPropAt_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) : LiftPropAt Q (chartAt (H := H) x).symm ((chartAt H x) x) :=
  hG.liftPropAt_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (by simp)
/-
**StructureGroupoid.LocalInvariantProp.liftPropOn_chart_symm** 是 Mathlib 中的一个定理，
位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropOn_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (h
Q : forall y, Q id univ y) : LiftPropOn Q (chartAt (H
参数：hG : G.LocalInvariantProp G Q；hQ : forall y, Q id univ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_symm_of_mem_maximalAtlas
`：liftPropOn_symm_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q) (hQ : fora
ll y, Q id univ y) (he : e in maximalAtlas M G) : LiftPropOn Q…
· 使用定理 `StructureGroupoid.chart_mem_maximalAtlas`：StructureGroupoid.chart_mem_ma
ximalAtlas [HasGroupoid M G] (x : M) : chartAt H x in G.maximalAtlas M
-/
theorem liftPropOn_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) : LiftPropOn Q (chartAt (H := H) x).symm (chartAt H x).target :=
  hG.liftPropOn_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)
/-
**StructureGroupoid.LocalInvariantProp.liftPropAt_of_mem_groupoid** 是 Mathlib 中的
一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropAt_of_mem_groupoid (hG : G.LocalInvariantProp G Q) (hQ : forall y,
 Q id univ y) {f : OpenPartialHomeomorph H H} (hf : f in G) {x : H} (hx : x in f
.source) : LiftPropAt Q f x
参数：hG : G.LocalInvariantProp G Q；hQ : forall y, Q id univ y；hf : f in G；hx : x i
n f.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_of_mem_maximalAtlas`：lif
tPropAt_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id
 univ y) (he : e in maximalAtlas M G) (hx : x in e.source…
· 使用定理 `StructureGroupoid.mem_maximalAtlas_of_mem_groupoid`：StructureGroupoid.me
m_maximalAtlas_of_mem_groupoid {f : OpenPartialHomeomorph H H} (hf : f in G) : f
 in G.maximalAtlas H
-/
theorem liftPropAt_of_mem_groupoid (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y)
    {f : OpenPartialHomeomorph H H} (hf : f ∈ G) {x : H} (hx : x ∈ f.source) : LiftPropAt Q f x :=
  liftPropAt_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf) hx
/-
**StructureGroupoid.LocalInvariantProp.liftPropOn_of_mem_groupoid** 是 Mathlib 中的
一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropOn_of_mem_groupoid (hG : G.LocalInvariantProp G Q) (hQ : forall y,
 Q id univ y) {f : OpenPartialHomeomorph H H} (hf : f in G) : LiftPropOn Q f f.s
ource
参数：hG : G.LocalInvariantProp G Q；hQ : forall y, Q id univ y；hf : f in G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_of_mem_maximalAtlas`：lif
tPropOn_of_mem_maximalAtlas (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id
 univ y) (he : e in maximalAtlas M G) : LiftPropOn Q e e.…
· 使用定理 `StructureGroupoid.mem_maximalAtlas_of_mem_groupoid`：StructureGroupoid.me
m_maximalAtlas_of_mem_groupoid {f : OpenPartialHomeomorph H H} (hf : f in G) : f
 in G.maximalAtlas H
-/
theorem liftPropOn_of_mem_groupoid (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y)
    {f : OpenPartialHomeomorph H H} (hf : f ∈ G) : LiftPropOn Q f f.source :=
  liftPropOn_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf)
/-
**StructureGroupoid.LocalInvariantProp.liftProp_id** 是 Mathlib 中的一个定理，位于命名空间 `St
ructureGroupoid.LocalInvariantProp`。
形式化陈述：liftProp_id (hG : G.LocalInvariantProp G Q) (hQ : forall y, Q id univ y) :
 LiftProp Q (id : M -> M)
参数：hG : G.LocalInvariantProp G Q；hQ : forall y, Q id univ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr'`：congr' {s : Set H} {x : H} 
{f g : H -> H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x) : P f s x
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse`：eventually_right_inverse
 {x} (hx : x in e.target) : forallᶠ y in 𝓝 x, e (e.symm y) = y
· 使用定理 `mem_chart_target`：mem_chart_target (x : M) : chartAt H x x in (chartAt H
 x).target
-/
theorem liftProp_id (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) :
    LiftProp Q (id : M → M) := by
  simp_rw [liftProp_iff, continuous_id, true_and]
  exact fun x ↦ hG.congr' ((chartAt H x).eventually_right_inverse <| mem_chart_target H x) (hQ _)
/-
**StructureGroupoid.LocalInvariantProp.liftPropAt_iff_comp_subtype_val** 是 Mathl
ib 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropAt_iff_comp_subtype_val (hG : LocalInvariantProp G G' P) {U : Open
s M} (f : M -> M') (x : U) : LiftPropAt P f x ↔ LiftPropAt P (f ∘ Subtype.val) x
参数：hG : LocalInvariantProp G G' P；f : M -> M'；x : U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Topology.IsOpenEmbedding.continuousAt_iff`：∀ {X : Type u_1} {Y : Type u_
2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 
: TopologicalSpace Y] [inst_2 :…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding'`：isOpenEmbedding' (U : Opens α) 
: IsOpenEmbedding (Subtype.val : U -> α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_iff`：congr_iff {s : Set H} {x
 : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) : P f s x ↔ P g s x
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq`：chartAt_su
btype_val_symm_eventuallyEq (U : Opens M) {x : U} : (chartAt H x.val).symm =ᶠ[𝓝 
(chartAt H x.val x.val)] Subtype.val ∘ (chartAt H …
-/
theorem liftPropAt_iff_comp_subtype_val (hG : LocalInvariantProp G G' P) {U : Opens M}
    (f : M → M') (x : U) :
    LiftPropAt P f x ↔ LiftPropAt P (f ∘ Subtype.val) x := by
  simp only [LiftPropAt, liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · simp_rw [continuousWithinAt_univ, U.isOpenEmbedding'.continuousAt_iff]
  · apply hG.congr_iff
    exact (U.chartAt_subtype_val_symm_eventuallyEq).fun_comp (chartAt H' (f x) ∘ f)
/-
**StructureGroupoid.LocalInvariantProp.liftPropAt_iff_comp_inclusion** 是 Mathlib
 中的一个定理，位于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftPropAt_iff_comp_inclusion (hG : LocalInvariantProp G G' P) {U V : Open
s M} (hUV : U <= V) (f : V -> M') (x : U) : LiftPropAt P f (Set.inclusion hUV x)
 ↔ LiftPropAt P (f ∘ Set.inclusion hUV : U -> M') x
参数：hG : LocalInvariantProp G G' P；hUV : U <= V；f : V -> M'；x : U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Topology.IsOpenEmbedding.continuousAt_iff`：∀ {X : Type u_1} {Y : Type u_
2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 
: TopologicalSpace Y] [inst_2 :…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding_of_le`：isOpenEmbedding_of_le {U V
 : Opens α} (i : U <= V) : IsOpenEmbedding (Set.inclusion <| SetLike.coe_subset_
coe.2 i) where toIsEmbedding
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `StructureGroupoid.LocalInvariantProp.congr_iff`：congr_iff {s : Set H} {x
 : H} {f g : H -> H'} (h : f =ᶠ[𝓝 x] g) : P f s x ↔ P g s x
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `TopologicalSpace.Opens.chartAt_inclusion_symm_eventuallyEq`：chartAt_incl
usion_symm_eventuallyEq {U V : Opens M} (hUV : U <= V) {x : U} : (chartAt H (Ope
ns.inclusion hUV x)).symm =ᶠ[𝓝 (chartAt H (Opens…
-/
theorem liftPropAt_iff_comp_inclusion (hG : LocalInvariantProp G G' P) {U V : Opens M} (hUV : U ≤ V)
    (f : V → M') (x : U) :
    LiftPropAt P f (Set.inclusion hUV x) ↔ LiftPropAt P (f ∘ Set.inclusion hUV : U → M') x := by
  simp only [LiftPropAt, liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · simp_rw [continuousWithinAt_univ,
      (TopologicalSpace.Opens.isOpenEmbedding_of_le hUV).continuousAt_iff]
  · apply hG.congr_iff
    exact (TopologicalSpace.Opens.chartAt_inclusion_symm_eventuallyEq hUV).fun_comp
      (chartAt H' (f (Set.inclusion hUV x)) ∘ f)
/-
**StructureGroupoid.LocalInvariantProp.liftProp_subtype_val** 是 Mathlib 中的一个定理，位
于命名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftProp_subtype_val {Q : (H -> H) -> Set H -> H -> Prop} (hG : LocalInvar
iantProp G G Q) (hQ : forall y, Q id univ y) (U : Opens M) : LiftProp Q (Subtype
.val : U -> M)
参数：H -> H；hG : LocalInvariantProp G G Q；hQ : forall y, Q id univ y；U : Opens M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_iff_comp_subtype_val`：li
ftPropAt_iff_comp_subtype_val (hG : LocalInvariantProp G G' P) {U : Opens M} (f 
: M -> M') (x : U) : LiftPropAt P f x ↔ LiftPropAt P (f ∘ …
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftProp_id`：liftProp_id (hG : G.Lo
calInvariantProp G Q) (hQ : forall y, Q id univ y) : LiftProp Q (id : M -> M)
-/
theorem liftProp_subtype_val {Q : (H → H) → Set H → H → Prop} (hG : LocalInvariantProp G G Q)
    (hQ : ∀ y, Q id univ y) (U : Opens M) :
    LiftProp Q (Subtype.val : U → M) := by
  intro x
  change LiftPropAt Q (id ∘ Subtype.val) x
  rw [← hG.liftPropAt_iff_comp_subtype_val]
  apply hG.liftProp_id hQ
/-
**StructureGroupoid.LocalInvariantProp.liftProp_inclusion** 是 Mathlib 中的一个定理，位于命
名空间 `StructureGroupoid.LocalInvariantProp`。
形式化陈述：liftProp_inclusion {Q : (H -> H) -> Set H -> H -> Prop} (hG : LocalInvaria
ntProp G G Q) (hQ : forall y, Q id univ y) {U V : Opens M} (hUV : U <= V) : Lift
Prop Q (Opens.inclusion hUV : U -> V)
参数：H -> H；hG : LocalInvariantProp G G Q；hQ : forall y, Q id univ y；hUV : U <= V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_iff_comp_inclusion`：lift
PropAt_iff_comp_inclusion (hG : LocalInvariantProp G G' P) {U V : Opens M} (hUV 
: U <= V) (f : V -> M') (x : U) : LiftPropAt P f (Set.in…
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftProp_id`：liftProp_id (hG : G.Lo
calInvariantProp G Q) (hQ : forall y, Q id univ y) : LiftProp Q (id : M -> M)
-/
theorem liftProp_inclusion {Q : (H → H) → Set H → H → Prop} (hG : LocalInvariantProp G G Q)
    (hQ : ∀ y, Q id univ y) {U V : Opens M} (hUV : U ≤ V) :
    LiftProp Q (Opens.inclusion hUV : U → V) := by
  intro x
  change LiftPropAt Q (id ∘ Opens.inclusion hUV) x
  rw [← hG.liftPropAt_iff_comp_inclusion hUV]
  apply hG.liftProp_id hQ

end LocalInvariantProp

section LocalStructomorph

variable (G)

open OpenPartialHomeomorph

/-- A function from a model space `H` to itself is a local structomorphism, with respect to a
structure groupoid `G` for `H`, relative to a set `s` in `H`, if for all points `x` in the set, the
function agrees with a `G`-structomorphism on `s` in a neighbourhood of `x`. -/
/-
**StructureGroupoid.IsLocalStructomorphWithinAt** 是 Mathlib 中的一个定义，位于命名空间 `Struc
tureGroupoid`。
形式化陈述：IsLocalStructomorphWithinAt (f : H -> H) (s : Set H) (x : H) : Prop
参数：f : H -> H；s : Set H；x : H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function from a model space `H` to itself is a local structomorphism, with res
pect to a
structure groupoid `G` for `H`, relative to a set `s` in `H`, if for all points 
`x` in the set, the
function agrees with a `G`-structomorphism on `s` in a neighbourhood of `x`.
-/
def IsLocalStructomorphWithinAt (f : H → H) (s : Set H) (x : H) : Prop :=
  x ∈ s → ∃ e : OpenPartialHomeomorph H H, e ∈ G ∧ EqOn f e.toFun (s ∩ e.source) ∧ x ∈ e.source

/-- For a groupoid `G` which is `ClosedUnderRestriction`, being a local structomorphism is a local
invariant property. -/
/-
**StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp** 是 Mathlib 中
的一个定理，位于命名空间 `StructureGroupoid`。
形式化陈述：isLocalStructomorphWithinAt_localInvariantProp [ClosedUnderRestriction G] 
: LocalInvariantProp G G (IsLocalStructomorphWithinAt G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `closedUnderRestriction'`：closedUnderRestriction' {G : StructureGroupoid 
H} [ClosedUnderRestriction G] {e : OpenPartialHomeomorph H H} (he : e in G) {s :
 Set H} (hs :…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `StructureGroupoid.trans`：StructureGroupoid.trans (G : StructureGroupoid 
H) {e e' : OpenPartialHomeomorph H H} (he : e in G) (he' : e' in G) : e ≫ₕ e' in
 G
· 使用定理 `StructureGroupoid.symm`：StructureGroupoid.symm (G : StructureGroupoid H)
 {e : OpenPartialHomeomorph H H} (he : e in G) : e.symm in G
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
For a groupoid `G` which is `ClosedUnderRestriction`, being a local structomorph
ism is a local
invariant property.
-/
theorem isLocalStructomorphWithinAt_localInvariantProp [ClosedUnderRestriction G] :
    LocalInvariantProp G G (IsLocalStructomorphWithinAt G) :=
  { is_local := by
      intro s x u f hu hux
      constructor
      · rintro h hx
        rcases h hx.1 with ⟨e, heG, hef, hex⟩
        have : s ∩ u ∩ e.source ⊆ s ∩ e.source := by mfld_set_tac
        exact ⟨e, heG, hef.mono this, hex⟩
      · rintro h hx
        rcases h ⟨hx, hux⟩ with ⟨e, heG, hef, hex⟩
        refine ⟨e.restr (interior u), ?_, ?_, ?_⟩
        · exact closedUnderRestriction' heG isOpen_interior
        · have : s ∩ u ∩ e.source = s ∩ (e.source ∩ u) := by mfld_set_tac
          simpa only [this, interior_interior, hu.interior_eq, mfld_simps] using hef
        · simp only [*, hu.interior_eq, mfld_simps]
    right_invariance' := by
      intro s x f e' he'G he'x h hx
      have hxs : x ∈ s := by simpa only [e'.left_inv he'x, mfld_simps] using hx
      rcases h hxs with ⟨e, heG, hef, hex⟩
      refine ⟨e'.symm.trans e, G.trans (G.symm he'G) heG, ?_, ?_⟩
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [hef ⟨hy.1, hy.2.2⟩, mfld_simps]
      · simp only [hex, he'x, mfld_simps]
    congr_of_forall := by
      intro s x f g hfgs _ h hx
      rcases h hx with ⟨e, heG, hef, hex⟩
      refine ⟨e, heG, ?_, hex⟩
      intro y hy
      rw [← hef hy, hfgs y hy.1]
    left_invariance' := by
      intro s x f e' he'G _ hfx h hx
      rcases h hx with ⟨e, heG, hef, hex⟩
      refine ⟨e.trans e', G.trans heG he'G, ?_, ?_⟩
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [hef ⟨hy.1, hy.2.1⟩, mfld_simps]
      · simpa only [hex, hef ⟨hx, hex⟩, mfld_simps] using hfx }

/-- A slight reformulation of `IsLocalStructomorphWithinAt` when `f` is an open partial homeomorph.
  This gives us an `e` that is defined on a subset of `f.source`. -/
/-
**StructureGroupoid._root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff
** 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A slight reformulation of `IsLocalStructomorphWithinAt` when `f` is an open part
ial homeomorph.
  This gives us an `e` that is defined on a subset of `f.source`.
-/
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff {G : StructureGroupoid H}
    [ClosedUnderRestriction G] (f : OpenPartialHomeomorph H H) {s : Set H} {x : H}
    (hx : x ∈ f.source ∪ sᶜ) :
    G.IsLocalStructomorphWithinAt (⇑f) s x ↔
      x ∈ s → ∃ e : OpenPartialHomeomorph H H,
      e ∈ G ∧ e.source ⊆ f.source ∧ EqOn f (⇑e) (s ∩ e.source) ∧ x ∈ e.source := by
  constructor
  · intro hf h2x
    obtain ⟨e, he, hfe, hxe⟩ := hf h2x
    refine ⟨e.restr f.source, closedUnderRestriction' he f.open_source, ?_, ?_, hxe, ?_⟩
    · simp_rw [OpenPartialHomeomorph.restr_source]
      exact inter_subset_right.trans interior_subset
    · intro x' hx'
      exact hfe ⟨hx'.1, hx'.2.1⟩
    · rw [f.open_source.interior_eq]
      exact Or.resolve_right hx (not_not.mpr h2x)
  · intro hf hx
    obtain ⟨e, he, _, hfe, hxe⟩ := hf hx
    exact ⟨e, he, hfe, hxe⟩

/-- A slight reformulation of `IsLocalStructomorphWithinAt` when `f` is an open partial homeomorph
and the set we're considering is a superset of `f.source`. -/
/-
**StructureGroupoid._root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff
'** 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A slight reformulation of `IsLocalStructomorphWithinAt` when `f` is an open part
ial homeomorph
and the set we're considering is a superset of `f.source`.
-/
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff' {G : StructureGroupoid H}
    [ClosedUnderRestriction G] (f : OpenPartialHomeomorph H H) {s : Set H} {x : H}
    (hs : f.source ⊆ s) (hx : x ∈ f.source ∪ sᶜ) :
    G.IsLocalStructomorphWithinAt (⇑f) s x ↔
      x ∈ s → ∃ e : OpenPartialHomeomorph H H,
      e ∈ G ∧ e.source ⊆ f.source ∧ EqOn f (⇑e) e.source ∧ x ∈ e.source := by
  rw [f.isLocalStructomorphWithinAt_iff hx]
  refine imp_congr_right fun _ ↦ exists_congr fun e ↦ and_congr_right fun _ ↦ ?_
  refine and_congr_right fun h2e ↦ ?_
  rw [inter_eq_right.mpr (h2e.trans hs)]

/-- A slight reformulation of `IsLocalStructomorphWithinAt` when `f` is an open partial homeomorph
and the set we're considering is `f.source`. -/
/-
**StructureGroupoid._root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_sou
rce_iff** 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A slight reformulation of `IsLocalStructomorphWithinAt` when `f` is an open part
ial homeomorph
and the set we're considering is `f.source`.
-/
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
    {G : StructureGroupoid H} [ClosedUnderRestriction G] (f : OpenPartialHomeomorph H H) {x : H} :
    G.IsLocalStructomorphWithinAt (⇑f) f.source x ↔
      x ∈ f.source → ∃ e : OpenPartialHomeomorph H H,
      e ∈ G ∧ e.source ⊆ f.source ∧ EqOn f (⇑e) e.source ∧ x ∈ e.source :=
  haveI : x ∈ f.source ∪ f.sourceᶜ := by simp_rw [union_compl_self, mem_univ]
  f.isLocalStructomorphWithinAt_iff' Subset.rfl this

variable {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂] {H₃ : Type*}
  [TopologicalSpace H₃] [ChartedSpace H₁ H₂] [ChartedSpace H₂ H₃] {G₁ : StructureGroupoid H₁}
  [HasGroupoid H₂ G₁] [ClosedUnderRestriction G₁] (G₂ : StructureGroupoid H₂) [HasGroupoid H₃ G₂]
/-
**StructureGroupoid.HasGroupoid.comp** 是 Mathlib 中的一个定理，位于命名空间 `StructureGroupoi
d.HasGroupoid`。
形式化陈述：∀ {H₁ : Type u_6} [inst : TopologicalSpace H₁] {H₂ : Type u_7} [inst_1 : T
opologicalSpace H₂] {H₃ : Type u_8}   [inst_2 : TopologicalSpace H₃] [inst_3 : C
hartedSpace H₁ H₂] [inst_4 : ChartedSpace H₂ H₃] {G₁ : StructureGroupoid H₁}   [
HasGroupoid H₂ G₁] [ClosedUnderRestriction G₁] (G₂ : StructureGroupoid H₂) [HasG
roupoid H₃ G₂],   (∀ e ∈ G₂, ChartedSpace.LiftPropOn G₁.IsLocalStructomorphWithi
nAt (↑e) e.source) → HasGroupoid H₃ G₁
参数：G₂ : StructureGroupoid H₂；∀ e ∈ G₂, ChartedSpace.LiftPropOn G₁.IsLocalStructo
morphWithinAt (↑e) e.source。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.locality`：StructureGroupoid.locality (G : StructureGro
upoid H) {e : OpenPartialHomeomorph H H} (h : forall x in e.source, exists s, Is
Open s ∧ x in s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart`：liftPropOn_
indep_chart (he : e in G.maximalAtlas M) (hf : f in G'.maximalAtlas M') (h : Lif
tPropOn P g s) {y : H} (hy : y in e.target inter …
· 使用定理 `StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp`：isLoca
lStructomorphWithinAt_localInvariantProp [ClosedUnderRestriction G] : LocalInvar
iantProp G G (IsLocalStructomorphWithinAt G)
· 使用定理 `StructureGroupoid.subset_maximalAtlas`：StructureGroupoid.subset_maximalA
tlas [HasGroupoid M G] : atlas H M subseteq G.maximalAtlas M
· 使用定理 `StructureGroupoid.compatible`：StructureGroupoid.compatible {H : Type*} [
TopologicalSpace H] (G : StructureGroupoid H) {M : Type*} [TopologicalSpace M] [
ChartedSpace H M] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.trans_assoc`：trans_assoc (e'' : OpenPartialHomeomo
rph Z Z') : (e.trans e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `StructureGroupoid.mem_of_eqOnSource`：StructureGroupoid.mem_of_eqOnSource
 (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H} (he : e in G) (h :
 e' ≈ e) : e' in G
· 使用定理 `closedUnderRestriction'`：closedUnderRestriction' {G : StructureGroupoid 
H} [ClosedUnderRestriction G] {e : OpenPartialHomeomorph H H} (he : e in G) {s :
 Set H} (hs :…
· 使用定理 `OpenPartialHomeomorph.restr_source_inter`：restr_source_inter (s : Set X)
 : e.restr (e.source inter s) = e.restr s
· 使用定理 `OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source`：∀ {X : Type u_1} {Y : 
Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   {e e' : Op
enPartialHomeomorph X Y}, Set.EqOn (↑e…
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
-/
theorem HasGroupoid.comp
    (H : ∀ e ∈ G₂, LiftPropOn (IsLocalStructomorphWithinAt G₁) (e : H₂ → H₂) e.source) :
    @HasGroupoid H₁ _ H₃ _ (ChartedSpace.comp H₁ H₂ H₃) G₁ :=
  let _ := ChartedSpace.comp H₁ H₂ H₃
  { compatible := by
      rintro _ _ ⟨e, he, f, hf, rfl⟩ ⟨e', he', f', hf', rfl⟩
      apply G₁.locality
      intro x hx
      simp only [mfld_simps] at hx
      have hxs : x ∈ f.symm ⁻¹' (e.symm ≫ₕ e').source := by simp only [hx, mfld_simps]
      have hxs' : x ∈ f.target ∩
          f.symm ⁻¹' ((e.symm ≫ₕ e').source ∩ e.symm ≫ₕ e' ⁻¹' f'.source) := by
        simp only [hx, mfld_simps]
      obtain ⟨φ, hφG₁, hφ, hφ_dom⟩ := LocalInvariantProp.liftPropOn_indep_chart
        (isLocalStructomorphWithinAt_localInvariantProp G₁) (G₁.subset_maximalAtlas hf)
        (G₁.subset_maximalAtlas hf') (H _ (G₂.compatible he he')) hxs' hxs
      simp_rw [← OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_assoc] at hφ
      simp_rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
      have hs : IsOpen (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').source :=
        (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').open_source
      refine ⟨_, hs.inter φ.open_source, ?_, ?_⟩
      · simp only [hx, hφ_dom, mfld_simps]
      · refine G₁.mem_of_eqOnSource (closedUnderRestriction' hφG₁ hs) ?_
        rw [OpenPartialHomeomorph.restr_source_inter]
        refine OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source (hφ.mono ?_)
        mfld_set_tac }

end LocalStructomorph

end StructureGroupoid

