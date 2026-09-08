/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Etienne Marion
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Proper maps between topological spaces

This file develops the basic theory of proper maps between topological spaces. A map `f : X → Y`
between two topological spaces is said to be **proper** if it is continuous and satisfies
the following equivalent conditions:
1. `f` is closed and has compact fibers.
2. `f` is **universally closed**, in the sense that for any topological space `Z`, the map
  `Prod.map f id : X × Z → Y × Z` is closed.
3. For any `ℱ : Filter X`, all cluster points of `map f ℱ` are images by `f` of some cluster point
  of `ℱ`.

We take 3 as the definition in `IsProperMap`, and we show the equivalence with 1, 2, and some
other variations.

## Main statements

* `isProperMap_iff_ultrafilter`: characterization of proper maps in terms of limits of ultrafilters
  instead of cluster points of filters.
* `IsProperMap.pi_map`: any product of proper maps is proper.
* `isProperMap_iff_isClosedMap_and_compact_fibers`: a map is proper if and only if it is
  continuous, closed, and has compact fibers

## Implementation notes

In algebraic geometry, it is common to also ask that proper maps are *separated*, in the sense of
[Stacks: definition OCY1](https://stacks.math.columbia.edu/tag/0CY1). We don't follow this
convention because it is unclear whether it would give the right notion in all cases, and in
particular for the theory of proper group actions. That means that our terminology does **NOT**
align with that of [Stacks: Characterizing proper maps](https://stacks.math.columbia.edu/tag/005M),
instead our definition of `IsProperMap` coincides with what they call "Bourbaki-proper".

Regarding the proofs, we don't really follow Bourbaki and go for more filter-heavy proofs,
as usual. In particular, their arguments rely heavily on restriction of closed maps (see
`IsClosedMap.restrictPreimage`), which makes them somehow annoying to formalize in type theory.
In contrast, the filter-based proofs work really well thanks to the existing API.

In fact, the filter proofs work so well that I thought this would be a great pedagogical resource
about how we use filters. For that reason, **all interesting proofs in this file are commented**,
so don't hesitate to have a look!

## TODO

* prove the equivalence with condition 3 of
  [Stacks: Theorem 005R](https://stacks.math.columbia.edu/tag/005R). Note that they mean something
  different by "universally closed".

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [Stacks: Characterizing proper maps](https://stacks.math.columbia.edu/tag/005M)
-/

public section

assert_not_exists StoneCech

open Filter Topology Function Set
open Prod (fst snd)

variable {X Y Z W ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace W] {f : X → Y} {g : Y → Z}

/-- A map `f : X → Y` between two topological spaces is said to be **proper** if it is continuous
and, for all `ℱ : Filter X`, any cluster point of `map f ℱ` is the image by `f` of a cluster point
of `ℱ`. -/
@[mk_iff isProperMap_iff_clusterPt, fun_prop]
/-
**IsProperMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [TopologicalSpace X] → [TopologicalSpace
 Y] → (X → Y) → Prop
参数：X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f : X → Y` between two topological spaces is said to be **proper** if it 
is continuous
and, for all `ℱ : Filter X`, any cluster point of `map f ℱ` is the image by `f` 
of a cluster point
of `ℱ`.
-/
structure IsProperMap (f : X → Y) : Prop extends Continuous f where
  /-- By definition, if `f` is a proper map and `ℱ` is any filter on `X`, then any cluster point of
  `map f ℱ` is the image by `f` of some cluster point of `ℱ`. -/
  clusterPt_of_mapClusterPt :
    ∀ ⦃ℱ : Filter X⦄, ∀ ⦃y : Y⦄, MapClusterPt y ℱ f → ∃ x, f x = y ∧ ClusterPt x ℱ

/-- Definition of proper maps. See also `isClosedMap_iff_clusterPt` for a related criterion
for closed maps. -/
add_decl_doc isProperMap_iff_clusterPt

/-- By definition, a proper map is continuous. -/
@[fun_prop]
/-
**IsProperMap.continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsProperMap.continuous (h : IsProperMap f) : Continuous f
参数：h : IsProperMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsProperMap.toContinuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsProperMap f → Conti
nuous f

--- 原说明 ---
By definition, a proper map is continuous.
-/
lemma IsProperMap.continuous (h : IsProperMap f) : Continuous f := h.toContinuous

/-- A proper map is closed. -/
/-
**IsProperMap.isClosedMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsProperMap.isClosedMap (h : IsProperMap f) : IsClosedMap f
参数：h : IsProperMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isClosedMap_iff_clusterPt`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f ↔     
∀ (s : Set X) (…
· 使用定理 `IsProperMap.clusterPt_of_mapClusterPt`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsProper
Map f → ∀ ⦃ℱ : Filter X⦄ ⦃y…

--- 原说明 ---
A proper map is closed.
-/
lemma IsProperMap.isClosedMap (h : IsProperMap f) : IsClosedMap f := by
  rw [isClosedMap_iff_clusterPt]
  exact fun s y ↦ h.clusterPt_of_mapClusterPt (ℱ := 𝓟 s) (y := y)

/-- Characterization of proper maps by ultrafilters. -/
/-
**isProperMap_iff_ultrafilter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isProperMap_iff_ultrafilter : IsProperMap f ↔ Continuous f ∧ forall ⦃𝒰 : U
ltrafilter X⦄, forall ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) -> exists x, f x = y ∧ 𝒰 <= 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isProperMap_iff_clusterPt`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y),   IsProperMap f ↔ Cont
inuous f ∧ ∀ ⦃ℱ…
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b

--- 原说明 ---
Characterization of proper maps by ultrafilters.
-/
lemma isProperMap_iff_ultrafilter : IsProperMap f ↔ Continuous f ∧
    ∀ ⦃𝒰 : Ultrafilter X⦄, ∀ ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) → ∃ x, f x = y ∧ 𝒰 ≤ 𝓝 x := by
  -- This is morally trivial since ultrafilters give all the information about cluster points.
  rw [isProperMap_iff_clusterPt]
  refine and_congr_right (fun _ ↦ ?_)
  constructor <;> intro H
  · intro 𝒰 y (hY : (Ultrafilter.map f 𝒰 : Filter Y) ≤ _)
    simp_rw [← Ultrafilter.clusterPt_iff] at hY ⊢
    exact H hY
  · simp_rw [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, ← exists_ultrafilter_iff,
      forall_exists_index]
    intro ℱ y 𝒰 hy
    rcases H (tendsto_iff_comap.mpr <| hy.trans inf_le_left) with ⟨x, hxy, hx⟩
    exact ⟨x, hxy, 𝒰, le_inf hx (hy.trans inf_le_right)⟩
/-
**isProperMap_iff_ultrafilter_of_t2** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isProperMap_iff_ultrafilter_of_t2 [T2Space Y] : IsProperMap f ↔ Continuous
 f ∧ forall ⦃𝒰 : Ultrafilter X⦄, forall ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) -> exists x, 
𝒰.1 <= 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `isProperMap_iff_ultrafilter`：isProperMap_iff_ultrafilter : IsProperMap f
 ↔ Continuous f ∧ forall ⦃𝒰 : Ultrafilter X⦄, forall ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) 
-> exists x, f x …
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
-/
lemma isProperMap_iff_ultrafilter_of_t2 [T2Space Y] : IsProperMap f ↔ Continuous f ∧
    ∀ ⦃𝒰 : Ultrafilter X⦄, ∀ ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) → ∃ x, 𝒰.1 ≤ 𝓝 x :=
  isProperMap_iff_ultrafilter.trans <| and_congr_right fun hc ↦ forall₃_congr fun _𝒰 _y hy ↦
    exists_congr fun x ↦ and_iff_right_of_imp fun h ↦
      tendsto_nhds_unique ((hc.tendsto x).mono_left h) hy

/-- If `f` is proper and converges to `y` along some ultrafilter `𝒰`, then `𝒰` converges to some
`x` such that `f x = y`. -/
/-
**IsProperMap.ultrafilter_le_nhds_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsProperMap.ultrafilter_le_nhds_of_tendsto (h : IsProperMap f) ⦃𝒰 : Ultraf
ilter X⦄ ⦃y : Y⦄ (hy : Tendsto f 𝒰 (𝓝 y)) : exists x, f x = y ∧ 𝒰 <= 𝓝 x
参数：h : IsProperMap f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isProperMap_iff_ultrafilter`：isProperMap_iff_ultrafilter : IsProperMap f
 ↔ Continuous f ∧ forall ⦃𝒰 : Ultrafilter X⦄, forall ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) 
-> exists x, f x …

--- 原说明 ---
If `f` is proper and converges to `y` along some ultrafilter `𝒰`, then `𝒰` conve
rges to some
`x` such that `f x = y`.
-/
lemma IsProperMap.ultrafilter_le_nhds_of_tendsto (h : IsProperMap f) ⦃𝒰 : Ultrafilter X⦄ ⦃y : Y⦄
    (hy : Tendsto f 𝒰 (𝓝 y)) : ∃ x, f x = y ∧ 𝒰 ≤ 𝓝 x :=
  (isProperMap_iff_ultrafilter.mp h).2 hy

/-- The composition of two proper maps is proper. -/
/-
**IsProperMap.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMap f) : IsProperMap (
g ∘ f)
参数：hg : IsProperMap g；hf : IsProperMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用引理 `IsProperMap.continuous`：IsProperMap.continuous (h : IsProperMap f) : Con
tinuous f
· 使用定理 `IsProperMap.clusterPt_of_mapClusterPt`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsProper
Map f → ∀ ⦃ℱ : Filter X⦄ ⦃y…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mapClusterPt_comp`：mapClusterPt_comp {φ : α -> β} {u : β -> X} : MapClus
terPt x F (u ∘ φ) ↔ MapClusterPt x (map φ F) u

--- 原说明 ---
The composition of two proper maps is proper.
-/
lemma IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMap f) :
    IsProperMap (g ∘ f) := by
  refine ⟨by fun_prop, fun ℱ z h ↦ ?_⟩
  rw [mapClusterPt_comp] at h
  rcases hg.clusterPt_of_mapClusterPt h with ⟨y, rfl, hy⟩
  rcases hf.clusterPt_of_mapClusterPt hy with ⟨x, rfl, hx⟩
  use x, rfl

/-- If the composition of two continuous functions `g ∘ f` is proper and `f` is surjective,
then `g` is proper. -/
/-
**isProperMap_of_comp_of_surj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isProperMap_of_comp_of_surj (hf : Continuous f) (hg : Continuous g) (hgf :
 IsProperMap (g ∘ f)) (f_surj : f.Surjective) : IsProperMap g
参数：hf : Continuous f；hg : Continuous g；hgf : IsProperMap (g ∘ f)；f_surj : f.Surj
ective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsProperMap.clusterPt_of_mapClusterPt`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsProper
Map f → ∀ ⦃ℱ : Filter X⦄ ⦃y…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mapClusterPt_comp`：mapClusterPt_comp {φ : α -> β} {u : β -> X} : MapClus
terPt x F (u ∘ φ) ↔ MapClusterPt x (map φ F) u
· 使用定理 `Filter.map_comap_of_surjective`：map_comap_of_surjective {f : α -> β} (hf
 : Surjective f) (l : Filter β) : map f (comap f l) = l
· 使用定理 `ClusterPt.map`：ClusterPt.map {lx : Filter X} {ly : Filter Y} (H : Cluste
rPt x lx) (hfc : ContinuousAt f x) (hf : Tendsto f lx ly) : ClusterPt (f x) ly
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)

--- 原说明 ---
If the composition of two continuous functions `g ∘ f` is proper and `f` is surj
ective,
then `g` is proper.
-/
lemma isProperMap_of_comp_of_surj (hf : Continuous f)
    (hg : Continuous g) (hgf : IsProperMap (g ∘ f)) (f_surj : f.Surjective) : IsProperMap g := by
  refine ⟨hg, fun ℱ z h ↦ ?_⟩
  rw [← ℱ.map_comap_of_surjective f_surj, ← mapClusterPt_comp] at h
  rcases hgf.clusterPt_of_mapClusterPt h with ⟨x, rfl, hx⟩
  rw [← ℱ.map_comap_of_surjective f_surj]
  exact ⟨f x, rfl, hx.map hf.continuousAt tendsto_map⟩

/-- If the composition of two continuous functions `g ∘ f` is proper and `g` is injective,
then `f` is proper. -/
/-
**isProperMap_of_comp_of_inj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isProperMap_of_comp_of_inj {f : X -> Y} {g : Y -> Z} (hf : Continuous f) (
hg : Continuous g) (hgf : IsProperMap (g ∘ f)) (g_inj : g.Injective) : IsProperM
ap f
参数：hf : Continuous f；hg : Continuous g；hgf : IsProperMap (g ∘ f)；g_inj : g.Injec
tive。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsProperMap.clusterPt_of_mapClusterPt`：∀ {X : Type u_1} {Y : Type u_2} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsProper
Map f → ∀ ⦃ℱ : Filter X⦄ ⦃y…
· 使用定理 `ClusterPt.map`：ClusterPt.map {lx : Filter X} {ly : Filter Y} (H : Cluste
rPt x lx) (hfc : ContinuousAt f x) (hf : Tendsto f lx ly) : ClusterPt (f x) ly
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)

--- 原说明 ---
If the composition of two continuous functions `g ∘ f` is proper and `g` is inje
ctive,
then `f` is proper.
-/
lemma isProperMap_of_comp_of_inj {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g)
    (hgf : IsProperMap (g ∘ f)) (g_inj : g.Injective) : IsProperMap f := by
  refine ⟨hf, fun ℱ y h ↦ ?_⟩
  rcases hgf.clusterPt_of_mapClusterPt (h.map hg.continuousAt tendsto_map) with ⟨x, hx1, hx2⟩
  exact ⟨x, g_inj hx1, hx2⟩

/-- If the composition of two continuous functions `f : X → Y` and `g : Y → Z` is proper
and `Y` is T2, then `f` is proper. -/
/-
**isProperMap_of_comp_of_t2** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isProperMap_of_comp_of_t2 [T2Space Y] (hf : Continuous f) (hg : Continuous
 g) (hgf : IsProperMap (g ∘ f)) : IsProperMap f
参数：hf : Continuous f；hg : Continuous g；hgf : IsProperMap (g ∘ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isProperMap_iff_ultrafilter_of_t2`：isProperMap_iff_ultrafilter_of_t2 [T2
Space Y] : IsProperMap f ↔ Continuous f ∧ forall ⦃𝒰 : Ultrafilter X⦄, forall ⦃y 
: Y⦄, Tendsto f 𝒰 (𝓝 y)…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `isProperMap_iff_ultrafilter`：isProperMap_iff_ultrafilter : IsProperMap f
 ↔ Continuous f ∧ forall ⦃𝒰 : Ultrafilter X⦄, forall ⦃y : Y⦄, Tendsto f 𝒰 (𝓝 y) 
-> exists x, f x …
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))

--- 原说明 ---
If the composition of two continuous functions `f : X → Y` and `g : Y → Z` is pr
oper
and `Y` is T2, then `f` is proper.
-/
lemma isProperMap_of_comp_of_t2 [T2Space Y] (hf : Continuous f) (hg : Continuous g)
    (hgf : IsProperMap (g ∘ f)) : IsProperMap f := by
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨hf, fun 𝒰 y h ↦ ?_⟩
  rw [isProperMap_iff_ultrafilter] at hgf
  rcases hgf.2 ((hg.tendsto y).comp h) with ⟨x, -, hx⟩
  exact ⟨x, hx⟩

/-- A binary product of proper maps is proper. -/
/-
**IsProperMap.prodMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsProperMap.prodMap {g : Z -> W} (hf : IsProperMap f) (hg : IsProperMap g)
 : IsProperMap (Prod.map f g)
参数：hf : IsProperMap f；hg : IsProperMap g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Filter.le_prod`：le_prod {f : Filter (α × β)} {g : Filter α} {g' : Filter
 β} : (f <= g ×ˢ g') ↔ Tendsto Prod.fst f g ∧ Tendsto Prod.snd f g'

--- 原说明 ---
A binary product of proper maps is proper.
-/
lemma IsProperMap.prodMap {g : Z → W} (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (Prod.map f g) := by
  simp_rw [isProperMap_iff_ultrafilter] at hf hg ⊢
  constructor
  -- Continuity is clear.
  · exact hf.1.prodMap hg.1
  -- Let `𝒰 : Ultrafilter (X × Z)`, and assume that `f × g` tends to some `(y, w) : Y × W`
  -- along `𝒰`.
  · intro 𝒰 ⟨y, w⟩ hyw
  -- That means that `f` tends to `y` along `map fst 𝒰` and `g` tends to `w` along `map snd 𝒰`.
    simp_rw [nhds_prod_eq, tendsto_prod_iff'] at hyw
  -- Thus, by properness of `f` and `g`, we get some `x : X` and `z : Z` such that `f x = y`,
  -- `g z = w`, `map fst 𝒰` tends to  `x`, and `map snd 𝒰` tends to `y`.
    rcases hf.2 (show Tendsto f (Ultrafilter.map fst 𝒰) (𝓝 y) by simpa using! hyw.1) with
      ⟨x, hxy, hx⟩
    rcases hg.2 (show Tendsto g (Ultrafilter.map snd 𝒰) (𝓝 w) by simpa using! hyw.2) with
      ⟨z, hzw, hz⟩
  -- By the properties of the product topology, that means that `𝒰` tends to `(x, z)`,
  -- which completes the proof since `(f × g)(x, z) = (y, w)`.
    refine ⟨⟨x, z⟩, Prod.ext hxy hzw, ?_⟩
    rw [nhds_prod_eq, le_prod]
    exact ⟨hx, hz⟩

/-- Any product of proper maps is proper. -/
/-
**IsProperMap.pi_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsProperMap.pi_map {X Y : ι -> Type*} [forall i, TopologicalSpace (X i)] [
forall i, TopologicalSpace (Y i)] {f : (i : ι) -> X i -> Y i} (h : forall i, IsP
roperMap (f i)) : IsProperMap (fun (x : forall i, X i) i => f i (x i))
参数：X i；Y i；i : ι；h : forall i, IsProperMap (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.le_pi`：le_pi {g : Filter (forall i, α i)} : g <= pi f ↔ forall i,
 Tendsto (eval i) g (f i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Any product of proper maps is proper.
-/
lemma IsProperMap.pi_map {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : (i : ι) → X i → Y i} (h : ∀ i, IsProperMap (f i)) :
    IsProperMap (fun (x : ∀ i, X i) i ↦ f i (x i)) := by
  simp_rw [isProperMap_iff_ultrafilter] at h ⊢
  constructor
  -- Continuity is clear.
  · exact continuous_pi fun i ↦ (h i).1.comp (continuous_apply i)
  -- Let `𝒰 : Ultrafilter (Π i, X i)`, and assume that `Π i, f i` tends to some `y : Π i, Y i`
  -- along `𝒰`.
  · intro 𝒰 y hy
  -- That means that each `f i` tends to `y i` along `map (eval i) 𝒰`.
    have : ∀ i, Tendsto (f i) (Ultrafilter.map (eval i) 𝒰) (𝓝 (y i)) := by
      simpa [tendsto_pi_nhds] using! hy
  -- Thus, by properness of all the `f i`s, we can choose some `x : Π i, X i` such that, for all
  -- `i`, `f i (x i) = y i` and `map (eval i) 𝒰` tends to  `x i`.
    choose x hxy hx using fun i ↦ (h i).2 (this i)
  -- By the properties of the product topology, that means that `𝒰` tends to `x`,
  -- which completes the proof since `(Π i, f i) x = y`.
    refine ⟨x, funext hxy, ?_⟩
    rwa [nhds_pi, le_pi]

/-- The preimage of a compact set by a proper map is again compact. See also
`isProperMap_iff_isCompact_preimage` which proves that this property completely characterizes
proper map when the codomain is compactly generated and Hausdorff. -/
/-
**IsProperMap.isCompact_preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsProperMap.isCompact_preimage (h : IsProperMap f) {K : Set Y} (hK : IsCom
pact K) : IsCompact (f ⁻¹' K)
参数：h : IsProperMap f；hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompact_iff_ultrafilter_le_nhds`：isCompact_iff_ultrafilter_le_nhds : I
sCompact s ↔ forall f : Ultrafilter X, ↑f <= 𝓟 s -> exists x in s, ↑f <= 𝓝 x
· 使用定理 `IsCompact.ultrafilter_le_nhds`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X},   IsCompact s → ∀ (f : Ultrafilter X), ↑f ≤ Filter.principal s → 
∃ x ∈ s, ↑f ≤ nhds …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ultrafilter.coe_map`：coe_map (m : α -> β) (f : Ultrafilter α) : (map m f
 : Filter β) = Filter.map m ↑f
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用引理 `IsProperMap.ultrafilter_le_nhds_of_tendsto`：IsProperMap.ultrafilter_le_n
hds_of_tendsto (h : IsProperMap f) ⦃𝒰 : Ultrafilter X⦄ ⦃y : Y⦄ (hy : Tendsto f 𝒰
 (𝓝 y)) : exists x, f x = y ∧ 𝒰 …

--- 原说明 ---
The preimage of a compact set by a proper map is again compact. See also
`isProperMap_iff_isCompact_preimage` which proves that this property completely 
characterizes
proper map when the codomain is compactly generated and Hausdorff.
-/
lemma IsProperMap.isCompact_preimage (h : IsProperMap f) {K : Set Y} (hK : IsCompact K) :
    IsCompact (f ⁻¹' K) := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  -- Let `𝒰 ≤ 𝓟 (f ⁻¹' K)` an ultrafilter.
  intro 𝒰 h𝒰
  -- In other words, we have `map f 𝒰 ≤ 𝓟 K`
  rw [← comap_principal, ← map_le_iff_le_comap, ← Ultrafilter.coe_map] at h𝒰
  -- Thus, by compactness of `K`, the ultrafilter `map f 𝒰` tends to some `y ∈ K`.
  rcases hK.ultrafilter_le_nhds _ h𝒰 with ⟨y, hyK, hy⟩
  -- Then, by properness of `f`, that means that `𝒰` tends to some `x ∈ f ⁻¹' {y} ⊆ f ⁻¹' K`,
  -- which completes the proof.
  rcases h.ultrafilter_le_nhds_of_tendsto hy with ⟨x, rfl, hx⟩
  exact ⟨x, hyK, hx⟩

/-- A map is proper if and only if it is closed and its fibers are compact. -/
/-
**isProperMap_iff_isClosedMap_and_compact_fibers** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isProperMap_iff_isClosedMap_and_compact_fibers : IsProperMap f ↔ Continuou
s f ∧ IsClosedMap f ∧ forall y, IsCompact (f ⁻¹' {y})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsProperMap.continuous`：IsProperMap.continuous (h : IsProperMap f) : Con
tinuous f
· 使用引理 `IsProperMap.isClosedMap`：IsProperMap.isClosedMap (h : IsProperMap f) : I
sClosedMap f
· 使用引理 `IsProperMap.isCompact_preimage`：IsProperMap.isCompact_preimage (h : IsPr
operMap f) {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isProperMap_iff_clusterPt`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y),   IsProperMap f ↔ Cont
inuous f ∧ ∀ ⦃ℱ…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.lift'`：lift'_top (h : Set α -> Set β) : (⊤ : Filter α).lift' h = 
𝓟 (h univ)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsClosedMap.mapClusterPt_iff_lift'_closure`：∀ {X : Type u_1} {Y : Type u
_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {F : F
ilter X},   IsClosedMap f → Cont…
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `clusterPt_lift'_closure_iff`：∀ {X : Type u} [inst : TopologicalSpace X] 
{x : X} {F : Filter X}, ClusterPt x (F.lift' closure) ↔ ClusterPt x F
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
A map is proper if and only if it is closed and its fibers are compact.
-/
theorem isProperMap_iff_isClosedMap_and_compact_fibers :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ ∀ y, IsCompact (f ⁻¹' {y}) := by
  constructor <;> intro H
  -- Note: In Bourbaki, the direct implication is proved by going through universally closed maps.
  -- We could do the same (using a `TFAE` cycle) but proving it directly from
  -- `IsProperMap.isCompact_preimage` is nice enough already so we don't bother with that.
  · exact ⟨H.continuous, H.isClosedMap, fun y ↦ H.isCompact_preimage isCompact_singleton⟩
  · rw [isProperMap_iff_clusterPt]
  -- Let `ℱ : Filter X` and `y` some cluster point of `map f ℱ`.
    refine ⟨H.1, fun ℱ y hy ↦ ?_⟩
  -- That means that the singleton `pure y` meets the "closure" of `map f ℱ`, by which we mean
  -- `Filter.lift' (map f ℱ) closure`. But `f` is closed, so
  -- `closure (map f ℱ) = map f (closure ℱ)` (see `IsClosedMap.lift'_closure_map_eq`).
  -- Thus `map f (closure ℱ ⊓ 𝓟 (f ⁻¹' {y})) = map f (closure ℱ) ⊓ 𝓟 {y} ≠ ⊥`, hence
  -- `closure ℱ ⊓ 𝓟 (f ⁻¹' {y}) ≠ ⊥`.
    rw [H.2.1.mapClusterPt_iff_lift'_closure H.1] at hy
  -- Now, applying the compactness of `f ⁻¹' {y}` to the nontrivial filter
  -- `closure ℱ ⊓ 𝓟 (f ⁻¹' {y})`, we obtain that it has a cluster point `x ∈ f ⁻¹' {y}`.
    rcases H.2.2 y (f := Filter.lift' ℱ closure ⊓ 𝓟 (f ⁻¹' {y})) inf_le_right with ⟨x, hxy, hx⟩
    refine ⟨x, hxy, ?_⟩
  -- In particular `x` is a cluster point of `closure ℱ`. Since cluster points of `closure ℱ`
  -- are exactly cluster points of `ℱ` (see `clusterPt_lift'_closure_iff`), this completes
  -- the proof.
    rw [← clusterPt_lift'_closure_iff]
    exact hx.mono inf_le_left

/-- An injective and continuous function is proper if and only if it is closed. -/
/-
**isProperMap_iff_isClosedMap_of_inj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isProperMap_iff_isClosedMap_of_inj (f_cont : Continuous f) (f_inj : f.Inje
ctive) : IsProperMap f ↔ IsClosedMap f
参数：f_cont : Continuous f；f_inj : f.Injective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsProperMap.isClosedMap`：IsProperMap.isClosedMap (h : IsProperMap f) : I
sClosedMap f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isProperMap_iff_isClosedMap_and_compact_fibers`：isProperMap_iff_isClosed
Map_and_compact_fibers : IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ forall y
, IsCompact (f ⁻¹' {y})
· 使用定理 `Set.Subsingleton.isCompact`：Set.Subsingleton.isCompact (hs : s.Subsingle
ton) : IsCompact s
· 使用定理 `Set.Subsingleton.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
s : Set β}, s.Subsingleton → Function.Injective f → (f ⁻¹' s).Subsingleton
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton

--- 原说明 ---
An injective and continuous function is proper if and only if it is closed.
-/
lemma isProperMap_iff_isClosedMap_of_inj (f_cont : Continuous f) (f_inj : f.Injective) :
    IsProperMap f ↔ IsClosedMap f := by
  refine ⟨fun h ↦ h.isClosedMap, fun h ↦ ?_⟩
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  exact ⟨f_cont, h, fun y ↦ (subsingleton_singleton.preimage f_inj).isCompact⟩

/-- An injective continuous and closed map is proper. -/
/-
**isProperMap_of_isClosedMap_of_inj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isProperMap_of_isClosedMap_of_inj (f_cont : Continuous f) (f_inj : f.Injec
tive) (f_closed : IsClosedMap f) : IsProperMap f
参数：f_cont : Continuous f；f_inj : f.Injective；f_closed : IsClosedMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isProperMap_iff_isClosedMap_of_inj`：isProperMap_iff_isClosedMap_of_inj (
f_cont : Continuous f) (f_inj : f.Injective) : IsProperMap f ↔ IsClosedMap f

--- 原说明 ---
An injective continuous and closed map is proper.
-/
lemma isProperMap_of_isClosedMap_of_inj (f_cont : Continuous f) (f_inj : f.Injective)
    (f_closed : IsClosedMap f) : IsProperMap f :=
  (isProperMap_iff_isClosedMap_of_inj f_cont f_inj).2 f_closed

/-- A homeomorphism is proper. -/
/-
**Homeomorph.isProperMap** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : X ≃ₜ Y), IsProperMap ⇑e
参数：e : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isProperMap_of_isClosedMap_of_inj`：isProperMap_of_isClosedMap_of_inj (f_
cont : Continuous f) (f_inj : f.Injective) (f_closed : IsClosedMap f) : IsProper
Map f
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Homeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h

--- 原说明 ---
A homeomorphism is proper.
-/
@[simp] lemma Homeomorph.isProperMap (e : X ≃ₜ Y) : IsProperMap e :=
  isProperMap_of_isClosedMap_of_inj e.continuous e.injective e.isClosedMap
/-
**IsHomeomorph.isProperMap** 是 Mathlib 中的一个定理，位于命名空间 `IsHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   IsHomeomorph f → IsProperMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isProperMap_of_isClosedMap_of_inj`：isProperMap_of_isClosedMap_of_inj (f_
cont : Continuous f) (f_inj : f.Injective) (f_closed : IsClosedMap f) : IsProper
Map f
· 使用定理 `IsHomeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Conti
nuous f
· 使用定理 `IsHomeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Functi
on.Injective…
· 使用定理 `IsHomeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → IsCl
osedMap f
-/
protected lemma IsHomeomorph.isProperMap (hf : IsHomeomorph f) : IsProperMap f :=
  isProperMap_of_isClosedMap_of_inj hf.continuous hf.injective hf.isClosedMap

/-- The identity is proper. -/
/-
**isProperMap_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], IsProperMap id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorph.isProperMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → IsPr
operMap f
· 使用定理 `IsHomeomorph.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsHomeomo
rph id

--- 原说明 ---
The identity is proper.
-/
@[simp] lemma isProperMap_id : IsProperMap (id : X → X) := IsHomeomorph.id.isProperMap

/-- A closed embedding is proper. -/
/-
**Topology.IsClosedEmbedding.isProperMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.isProperMap (hf : IsClosedEmbedding f) : IsProp
erMap f
参数：hf : IsClosedEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isProperMap_of_isClosedMap_of_inj`：isProperMap_of_isClosedMap_of_inj (f_
cont : Continuous f) (f_inj : f.Injective) (f_closed : IsClosedMap f) : IsProper
Map f
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…

--- 原说明 ---
A closed embedding is proper.
-/
lemma Topology.IsClosedEmbedding.isProperMap (hf : IsClosedEmbedding f) : IsProperMap f :=
  isProperMap_of_isClosedMap_of_inj hf.continuous hf.injective hf.isClosedMap

/-- The coercion from a closed subset is proper. -/
/-
**IsClosed.isProperMap_subtypeVal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.isProperMap_subtypeVal {C : Set X} (hC : IsClosed C) : IsProperMa
p ((↑) : C -> X)
参数：hC : IsClosed C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsClosedEmbedding.isProperMap`：Topology.IsClosedEmbedding.isPro
perMap (hf : IsClosedEmbedding f) : IsProperMap f
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)

--- 原说明 ---
The coercion from a closed subset is proper.
-/
lemma IsClosed.isProperMap_subtypeVal {C : Set X} (hC : IsClosed C) : IsProperMap ((↑) : C → X) :=
  hC.isClosedEmbedding_subtypeVal.isProperMap

/-- The restriction of a proper map to a closed subset is proper. -/
/-
**IsProperMap.restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsProperMap.restrict {C : Set X} (hf : IsProperMap f) (hC : IsClosed C) : 
IsProperMap fun x : C => f x
参数：hf : IsProperMap f；hC : IsClosed C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsProperMap.comp`：IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMa
p f) : IsProperMap (g ∘ f)
· 使用引理 `IsClosed.isProperMap_subtypeVal`：IsClosed.isProperMap_subtypeVal {C : Se
t X} (hC : IsClosed C) : IsProperMap ((↑) : C -> X)

--- 原说明 ---
The restriction of a proper map to a closed subset is proper.
-/
lemma IsProperMap.restrict {C : Set X} (hf : IsProperMap f) (hC : IsClosed C) :
    IsProperMap fun x : C ↦ f x := hf.comp hC.isProperMap_subtypeVal

/-- The range of a proper map is closed. -/
/-
**IsProperMap.isClosed_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsProperMap.isClosed_range (hf : IsProperMap f) : IsClosed (range f)
参数：hf : IsProperMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.isClosed_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → IsC
losed (Set.range…
· 使用引理 `IsProperMap.isClosedMap`：IsProperMap.isClosedMap (h : IsProperMap f) : I
sClosedMap f

--- 原说明 ---
The range of a proper map is closed.
-/
lemma IsProperMap.isClosed_range (hf : IsProperMap f) : IsClosed (range f) :=
  hf.isClosedMap.isClosed_range

/-- Version of `isProperMap_iff_isClosedMap_and_compact_fibers` in terms of `cofinite` and
`cocompact`. Only works when the codomain is `T1`. -/
/-
**isProperMap_iff_isClosedMap_and_tendsto_cofinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isProperMap_iff_isClosedMap_and_tendsto_cofinite [T1Space Y] : IsProperMap
 f ↔ Continuous f ∧ IsClosedMap f ∧ Tendsto f (cocompact X) cofinite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `IsCompact.compl_mem_cocompact`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X}, IsCompact s → sᶜ ∈ Filter.cocompact X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `compl_le_compl_iff_le`：compl_le_compl_iff_le : yᶜ <= xᶜ ↔ x <= y

--- 原说明 ---
Version of `isProperMap_iff_isClosedMap_and_compact_fibers` in terms of `cofinit
e` and
`cocompact`. Only works when the codomain is `T1`.
-/
lemma isProperMap_iff_isClosedMap_and_tendsto_cofinite [T1Space Y] :
    IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ Tendsto f (cocompact X) cofinite := by
  simp_rw [isProperMap_iff_isClosedMap_and_compact_fibers, Tendsto,
    le_cofinite_iff_compl_singleton_mem, mem_map, preimage_compl]
  refine and_congr_right fun f_cont ↦ and_congr_right fun _ ↦
    ⟨fun H y ↦ (H y).compl_mem_cocompact, fun H y ↦ ?_⟩
  rcases mem_cocompact.mp (H y) with ⟨K, hK, hKy⟩
  exact hK.of_isClosed_subset (isClosed_singleton.preimage f_cont)
    (compl_le_compl_iff_le.mp hKy)

/-- A continuous map from a compact space to a T₂ space is a proper map. -/
/-
**Continuous.isProperMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.isProperMap [CompactSpace X] [T2Space Y] (hf : Continuous f) : 
IsProperMap f
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isProperMap_iff_isClosedMap_and_tendsto_cofinite`：isProperMap_iff_isClos
edMap_and_tendsto_cofinite [T1Space Y] : IsProperMap f ↔ Continuous f ∧ IsClosed
Map f ∧ Tendsto f (cocompact X) cofini…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Continuous.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [T2Space Y]   {f : X 
→ Y}, Contin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.cocompact_eq_bot`：Filter.cocompact_eq_bot [CompactSpace X] : Filt
er.cocompact X = ⊥

--- 原说明 ---
A continuous map from a compact space to a T₂ space is a proper map.
-/
theorem Continuous.isProperMap [CompactSpace X] [T2Space Y] (hf : Continuous f) : IsProperMap f :=
  isProperMap_iff_isClosedMap_and_tendsto_cofinite.2 ⟨hf, hf.isClosedMap, by simp⟩

/-- A constant map to a T₁ space is proper if and only if its domain is compact. -/
/-
**isProperMap_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isProperMap_const_iff [T1Space Y] (y : Y) : IsProperMap (fun _ : X => y) ↔
 CompactSpace X
参数：y : Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isProperMap_iff_isClosedMap_and_compact_fibers`：isProperMap_iff_isClosed
Map_and_compact_fibers : IsProperMap f ↔ Continuous f ∧ IsClosedMap f ∧ forall y
, IsCompact (f ⁻¹' {y})
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `isClosedMap_const`：isClosedMap_const {X Y} [TopologicalSpace X] [Topolog
icalSpace Y] [T1Space Y] {y : Y} : IsClosedMap (Function.const X y)
· 使用定理 `Set.preimage_const`：preimage_const (b : β) (s : Set β) [Decidable (b in 
s)] : (fun _ : α => b) ⁻¹' s = if b in s then univ else ∅
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a

--- 原说明 ---
A constant map to a T₁ space is proper if and only if its domain is compact.
-/
theorem isProperMap_const_iff [T1Space Y] (y : Y) :
    IsProperMap (fun _ : X ↦ y) ↔ CompactSpace X := by
  classical
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  constructor
  · rintro ⟨-, -, h⟩
    exact ⟨by simpa using h y⟩
  · intro H
    refine ⟨continuous_const, isClosedMap_const, fun y' ↦ ?_⟩
    simp [preimage_const, mem_singleton_iff, apply_ite, isCompact_univ]
/-
**isProperMap_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isProperMap_const [h : CompactSpace X] [T1Space Y] (y : Y) : IsProperMap (
fun _ : X => y)
参数：y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isProperMap_const_iff`：isProperMap_const_iff [T1Space Y] (y : Y) : IsPro
perMap (fun _ : X => y) ↔ CompactSpace X
-/
theorem isProperMap_const [h : CompactSpace X] [T1Space Y] (y : Y) :
    IsProperMap (fun _ : X ↦ y) :=
  isProperMap_const_iff y |>.mpr h

/-- If `Y` is a compact topological space, then `Prod.fst : X × Y → X` is a proper map. -/
/-
**isProperMap_fst_of_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isProperMap_fst_of_compactSpace [CompactSpace Y] : IsProperMap (Prod.fst :
 X × Y -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsProperMap.comp`：IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMa
p f) : IsProperMap (g ∘ f)
· 使用定理 `Homeomorph.isProperMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y), IsProperMap ⇑e
· 使用引理 `IsProperMap.prodMap`：IsProperMap.prodMap {g : Z -> W} (hf : IsProperMap 
f) (hg : IsProperMap g) : IsProperMap (Prod.map f g)
· 使用定理 `isProperMap_id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsProperMa
p id
· 使用定理 `isProperMap_const`：isProperMap_const [h : CompactSpace X] [T1Space Y] (y
 : Y) : IsProperMap (fun _ : X => y)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `instDiscreteTopologyPUnit`：DiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
If `Y` is a compact topological space, then `Prod.fst : X × Y → X` is a proper m
ap.
-/
theorem isProperMap_fst_of_compactSpace [CompactSpace Y] :
    IsProperMap (Prod.fst : X × Y → X) :=
  Homeomorph.prodPUnit X |>.isProperMap.comp (isProperMap_id.prodMap (isProperMap_const ()))

/-- If `X` is a compact topological space, then `Prod.snd : X × Y → Y` is a proper map. -/
/-
**isProperMap_snd_of_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isProperMap_snd_of_compactSpace [CompactSpace X] : IsProperMap (Prod.snd :
 X × Y -> Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsProperMap.comp`：IsProperMap.comp (hg : IsProperMap g) (hf : IsProperMa
p f) : IsProperMap (g ∘ f)
· 使用定理 `Homeomorph.isProperMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y), IsProperMap ⇑e
· 使用引理 `IsProperMap.prodMap`：IsProperMap.prodMap {g : Z -> W} (hf : IsProperMap 
f) (hg : IsProperMap g) : IsProperMap (Prod.map f g)
· 使用定理 `isProperMap_const`：isProperMap_const [h : CompactSpace X] [T1Space Y] (y
 : Y) : IsProperMap (fun _ : X => y)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `instDiscreteTopologyPUnit`：DiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `isProperMap_id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsProperMa
p id

--- 原说明 ---
If `X` is a compact topological space, then `Prod.snd : X × Y → Y` is a proper m
ap.
-/
theorem isProperMap_snd_of_compactSpace [CompactSpace X] :
    IsProperMap (Prod.snd : X × Y → Y) :=
  Homeomorph.punitProd Y |>.isProperMap.comp ((isProperMap_const ()).prodMap isProperMap_id)

/-- If `Y` is a compact topological space, then `Prod.fst : X × Y → X` is a closed map. -/
/-
**isClosedMap_fst_of_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_fst_of_compactSpace [CompactSpace Y] : IsClosedMap (Prod.fst :
 X × Y -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsProperMap.isClosedMap`：IsProperMap.isClosedMap (h : IsProperMap f) : I
sClosedMap f
· 使用定理 `isProperMap_fst_of_compactSpace`：isProperMap_fst_of_compactSpace [Compac
tSpace Y] : IsProperMap (Prod.fst : X × Y -> X)

--- 原说明 ---
If `Y` is a compact topological space, then `Prod.fst : X × Y → X` is a closed m
ap.
-/
theorem isClosedMap_fst_of_compactSpace [CompactSpace Y] :
    IsClosedMap (Prod.fst : X × Y → X) :=
  isProperMap_fst_of_compactSpace.isClosedMap

/-- If `X` is a compact topological space, then `Prod.snd : X × Y → Y` is a closed map. -/
/-
**isClosedMap_snd_of_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_snd_of_compactSpace [CompactSpace X] : IsClosedMap (Prod.snd :
 X × Y -> Y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsProperMap.isClosedMap`：IsProperMap.isClosedMap (h : IsProperMap f) : I
sClosedMap f
· 使用定理 `isProperMap_snd_of_compactSpace`：isProperMap_snd_of_compactSpace [Compac
tSpace X] : IsProperMap (Prod.snd : X × Y -> Y)

--- 原说明 ---
If `X` is a compact topological space, then `Prod.snd : X × Y → Y` is a closed m
ap.
-/
theorem isClosedMap_snd_of_compactSpace [CompactSpace X] :
    IsClosedMap (Prod.snd : X × Y → Y) :=
  isProperMap_snd_of_compactSpace.isClosedMap

/-- A proper map `f : X → Y` is **universally closed**: for any topological space `Z`, the map
`Prod.map f id : X × Z → Y × Z` is closed. We will prove in `isProperMap_iff_universally_closed`
that proper maps are exactly continuous maps which have this property, but this result should be
easier to use because it allows `Z` to live in any universe. -/
/-
**IsProperMap.universally_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProperMap.universally_closed (Z) [TopologicalSpace Z] (h : IsProperMap f
) : IsClosedMap (Prod.map f id : X × Z -> Y × Z)
参数：Z；h : IsProperMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsProperMap.isClosedMap`：IsProperMap.isClosedMap (h : IsProperMap f) : I
sClosedMap f
· 使用引理 `IsProperMap.prodMap`：IsProperMap.prodMap {g : Z -> W} (hf : IsProperMap 
f) (hg : IsProperMap g) : IsProperMap (Prod.map f g)
· 使用定理 `isProperMap_id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsProperMa
p id

--- 原说明 ---
A proper map `f : X → Y` is **universally closed**: for any topological space `Z
`, the map
`Prod.map f id : X × Z → Y × Z` is closed. We will prove in `isProperMap_iff_uni
versally_closed`
that proper maps are exactly continuous maps which have this property, but this 
result should be
easier to use because it allows `Z` to live in any universe.
-/
theorem IsProperMap.universally_closed (Z) [TopologicalSpace Z] (h : IsProperMap f) :
    IsClosedMap (Prod.map f id : X × Z → Y × Z) :=
  -- `f × id` is proper as a product of proper maps, hence closed.
  (h.prodMap isProperMap_id).isClosedMap
