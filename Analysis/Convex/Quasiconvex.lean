/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Antoine Chambert-Loir, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Quasiconvex and quasiconcave functions

This file defines quasiconvexity, quasiconcavity and quasilinearity of functions, which are
generalizations of unimodality and monotonicity. Convexity implies quasiconvexity, concavity implies
quasiconcavity, and monotonicity implies quasilinearity.

## Main declarations

* `QuasiconvexOn 𝕜 s f`: Quasiconvexity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex.
* `QuasiconcaveOn 𝕜 s f`: Quasiconcavity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex.
* `QuasilinearOn 𝕜 s f`: Quasilinearity of the function `f` on the set `s` with scalars `𝕜`. This
  means that `f` is both quasiconvex and quasiconcave.

## References

* https://en.wikipedia.org/wiki/Quasiconvex_function
-/

@[expose] public section


open Function OrderDual Set

variable {𝕜 E β : Type*}

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]

section LE_β

variable (𝕜) [LE β] [SMul 𝕜 E] (s : Set E) (f : E -> β)

/--
Definition of `QuasiconvexOn` / `QuasiconvexOn` 的定义

English:
definition QuasiconvexOn
  signature: : Prop
  body: forall r, Convex 𝕜 ({ x in s | f x <= r })

中文:
定义 QuasiconvexOn
  签名: : 命题
  定义体: forall r, Convex 𝕜 ({ x in s | f x <= r })

Depends on / 依赖: Convex
-/
def QuasiconvexOn : Prop :=
  forall r, Convex 𝕜 ({ x in s | f x <= r })

/--
Definition of `QuasiconcaveOn` / `QuasiconcaveOn` 的定义

English:
definition QuasiconcaveOn
  signature: : Prop
  body: forall r, Convex 𝕜 ({ x in s | r <= f x })

中文:
定义 QuasiconcaveOn
  签名: : 命题
  定义体: forall r, Convex 𝕜 ({ x in s | r <= f x })

Depends on / 依赖: Convex
-/
def QuasiconcaveOn : Prop :=
  forall r, Convex 𝕜 ({ x in s | r <= f x })

/--
Definition of `QuasilinearOn` / `QuasilinearOn` 的定义

English:
definition QuasilinearOn
  signature: : Prop
  body: QuasiconvexOn 𝕜 s f ∧ QuasiconcaveOn 𝕜 s f

中文:
定义 QuasilinearOn
  签名: : 命题
  定义体: QuasiconvexOn 𝕜 s f ∧ QuasiconcaveOn 𝕜 s f

Depends on / 依赖: QuasiconcaveOn, QuasiconvexOn
-/
def QuasilinearOn : Prop :=
  QuasiconvexOn 𝕜 s f ∧ QuasiconcaveOn 𝕜 s f

variable {𝕜 s f}

/--
theorem `QuasiconvexOn.dual` / 定理 `QuasiconvexOn.dual`

English:
theorem QuasiconvexOn.dual
  statement: QuasiconvexOn 𝕜 s f -> QuasiconcaveOn 𝕜 s (toDual ∘ f)
  proof: id

中文:
定理 QuasiconvexOn.dual
  结论: QuasiconvexOn 𝕜 s f -> QuasiconcaveOn 𝕜 s (toDual ∘ f)
  证明: id
-/
theorem QuasiconvexOn.dual : QuasiconvexOn 𝕜 s f -> QuasiconcaveOn 𝕜 s (toDual ∘ f) :=
  id

/--
theorem `QuasiconcaveOn.dual` / 定理 `QuasiconcaveOn.dual`

English:
theorem QuasiconcaveOn.dual
  statement: QuasiconcaveOn 𝕜 s f -> QuasiconvexOn 𝕜 s (toDual ∘ f)
  proof: id

中文:
定理 QuasiconcaveOn.dual
  结论: QuasiconcaveOn 𝕜 s f -> QuasiconvexOn 𝕜 s (toDual ∘ f)
  证明: id
-/
theorem QuasiconcaveOn.dual : QuasiconcaveOn 𝕜 s f -> QuasiconvexOn 𝕜 s (toDual ∘ f) :=
  id

/--
theorem `QuasilinearOn.dual` / 定理 `QuasilinearOn.dual`

English:
theorem QuasilinearOn.dual
  statement: QuasilinearOn 𝕜 s f -> QuasilinearOn 𝕜 s (toDual ∘ f)
  proof: And.symm

中文:
定理 QuasilinearOn.dual
  结论: QuasilinearOn 𝕜 s f -> QuasilinearOn 𝕜 s (toDual ∘ f)
  证明: And.symm

Depends on / 依赖: And.symm
-/
theorem QuasilinearOn.dual : QuasilinearOn 𝕜 s f -> QuasilinearOn 𝕜 s (toDual ∘ f) :=
  And.symm

/--
theorem `Convex.quasiconvexOn_of_convex_le` / 定理 `Convex.quasiconvexOn_of_convex_le`

English:
theorem Convex.quasiconvexOn_of_convex_le
  given: (hs : Convex 𝕜 s) (h : forall r, Convex 𝕜 { x | f x <= r })
  proof: fun r => hs.inter (h r)

中文:
定理 凸.quasiconvexOn_of_convex_le
  条件: (hs : 凸 𝕜 s) (h : 对任意 r, 凸 𝕜 { x | f x <= r })
  证明: fun r => hs.inter (h r)

Depends on / 依赖: hs.inter
-/
theorem Convex.quasiconvexOn_of_convex_le (hs : Convex 𝕜 s) (h : forall r, Convex 𝕜 { x | f x <= r }) :
    QuasiconvexOn 𝕜 s f := fun r => hs.inter (h r)

/--
theorem `Convex.quasiconcaveOn_of_convex_ge` / 定理 `Convex.quasiconcaveOn_of_convex_ge`

English:
theorem Convex.quasiconcaveOn_of_convex_ge
  given: (hs : Convex 𝕜 s) (h : forall r, Convex 𝕜 { x | r <= f x })
  proof: Convex.quasiconvexOn_of_convex_le (β := βᵒᵈ) hs h

中文:
定理 凸.quasiconcaveOn_of_convex_ge
  条件: (hs : 凸 𝕜 s) (h : 对任意 r, 凸 𝕜 { x | r <= f x })
  证明: Convex.quasiconvexOn_of_convex_le (β := βᵒᵈ) hs h

Depends on / 依赖: Convex, Convex.quasiconvexOn_of_convex_le, quasiconvexOn_of_convex_le
-/
theorem Convex.quasiconcaveOn_of_convex_ge (hs : Convex 𝕜 s) (h : forall r, Convex 𝕜 { x | r <= f x }) :
    QuasiconcaveOn 𝕜 s f :=
  Convex.quasiconvexOn_of_convex_le (β := βᵒᵈ) hs h

/--
theorem `QuasiconvexOn.convex` / 定理 `QuasiconvexOn.convex`

English:
theorem QuasiconvexOn.convex
  given: [IsDirectedOrder β] (hf : QuasiconvexOn 𝕜 s f)
  statement: Convex 𝕜 s
  proof: fun x hx y hy _ _ ha hb hab =>
  let ⟨_, hxz, hyz⟩ := exists_ge_ge (f x) (f y)
  (hf _ ⟨hx, hxz⟩ ⟨hy, hyz⟩ ha hb hab).1

中文:
定理 QuasiconvexOn.convex
  条件: [IsDirectedOrder β] (hf : QuasiconvexOn 𝕜 s f)
  结论: 凸 𝕜 s
  证明: fun x hx y hy _ _ ha hb hab =>
  let ⟨_, hxz, hyz⟩ := exists_ge_ge (f x) (f y)
  (hf _ ⟨hx, hxz⟩ ⟨hy, hyz⟩ ha hb hab).1

Depends on / 依赖: exists_ge_ge
-/
theorem QuasiconvexOn.convex [IsDirectedOrder β] (hf : QuasiconvexOn 𝕜 s f) : Convex 𝕜 s :=
  fun x hx y hy _ _ ha hb hab =>
  let ⟨_, hxz, hyz⟩ := exists_ge_ge (f x) (f y)
  (hf _ ⟨hx, hxz⟩ ⟨hy, hyz⟩ ha hb hab).1

/--
theorem `QuasiconcaveOn.convex` / 定理 `QuasiconcaveOn.convex`

English:
theorem QuasiconcaveOn.convex
  given: [IsCodirectedOrder β] (hf : QuasiconcaveOn 𝕜 s f)
  statement: Convex 𝕜 s
  proof: hf.dual.convex

中文:
定理 QuasiconcaveOn.convex
  条件: [IsCodirectedOrder β] (hf : QuasiconcaveOn 𝕜 s f)
  结论: 凸 𝕜 s
  证明: hf.dual.convex

Depends on / 依赖: convex, hf.dual.convex
-/
theorem QuasiconcaveOn.convex [IsCodirectedOrder β] (hf : QuasiconcaveOn 𝕜 s f) : Convex 𝕜 s :=
  hf.dual.convex

end LE_β

section Composition

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
variable {β γ : Type*} [LinearOrder β] [Preorder γ]
variable {s : Set E} {f : E -> β} {g : β -> γ}

/--
theorem `QuasiconvexOn.monotone_comp` / 定理 `QuasiconvexOn.monotone_comp`

English:
theorem QuasiconvexOn.monotone_comp
  proof: fun c x hx y hy => by
  simp only [Function.comp_apply, mem_ofPred_eq] at hx hy
  intro a b ha hb hab
  simp only [Function.comp_apply, mem_ofPred_eq]
  wlog h : f x <= f y
  · grind
  specialize hf (f y) ⟨hx.1, h⟩ ⟨hy.1, le_rfl⟩ ha hb hab
  simp only [mem_ofPred_eq] at hf
  exact ⟨hf.1, le_trans (h

中文:
定理 QuasiconvexOn.monotone_comp
  证明: fun c x hx y hy => by
  simp only [Function.comp_apply, mem_ofPred_eq] at hx hy
  intro a b ha hb hab
  simp only [Function.comp_apply, mem_ofPred_eq]
  wlog h : f x <= f y
  · grind
  specialize hf (f y) ⟨hx.1, h⟩ ⟨hy.1, le_rfl⟩ ha hb hab
  simp only [mem_ofPred_eq] at hf
  exact ⟨hf.1, le_trans (h

Depends on / 依赖: Function, Function.comp_apply, comp_apply, le_rfl, le_trans, mem_ofPred_eq, specialize
-/
theorem QuasiconvexOn.monotone_comp
    (hg : Monotone g) (hf : QuasiconvexOn 𝕜 s f) :
    QuasiconvexOn 𝕜 s (g ∘ f) := fun c x hx y hy => by
  simp only [Function.comp_apply, mem_ofPred_eq] at hx hy
  intro a b ha hb hab
  simp only [Function.comp_apply, mem_ofPred_eq]
  wlog h : f x <= f y
  · grind
  specialize hf (f y) ⟨hx.1, h⟩ ⟨hy.1, le_rfl⟩ ha hb hab
  simp only [mem_ofPred_eq] at hf
  exact ⟨hf.1, le_trans (hg hf.2) hy.2⟩

/--
theorem `QuasiconvexOn.antitone_comp` / 定理 `QuasiconvexOn.antitone_comp`

English:
theorem QuasiconvexOn.antitone_comp
  given: (hg : Antitone g) (hf : QuasiconvexOn 𝕜 s f)
  proof: hf.monotone_comp (γ := γᵒᵈ) hg

中文:
定理 QuasiconvexOn.antitone_comp
  条件: (hg : 递减 g) (hf : QuasiconvexOn 𝕜 s f)
  证明: hf.monotone_comp (γ := γᵒᵈ) hg

Depends on / 依赖: hf.monotone_comp, monotone_comp
-/
theorem QuasiconvexOn.antitone_comp (hg : Antitone g) (hf : QuasiconvexOn 𝕜 s f) :
    QuasiconcaveOn 𝕜 s (g ∘ f) :=
  hf.monotone_comp (γ := γᵒᵈ) hg

/--
theorem `QuasiconcaveOn.monotone_comp` / 定理 `QuasiconcaveOn.monotone_comp`

English:
theorem QuasiconcaveOn.monotone_comp
  given: (hg : Monotone g) (hf : QuasiconcaveOn 𝕜 s f)
  proof: QuasiconvexOn.monotone_comp hg.dual hf

中文:
定理 QuasiconcaveOn.monotone_comp
  条件: (hg : 递增 g) (hf : QuasiconcaveOn 𝕜 s f)
  证明: QuasiconvexOn.monotone_comp hg.dual hf

Depends on / 依赖: QuasiconvexOn, QuasiconvexOn.monotone_comp, hg.dual, monotone_comp
-/
theorem QuasiconcaveOn.monotone_comp (hg : Monotone g) (hf : QuasiconcaveOn 𝕜 s f) :
    QuasiconcaveOn 𝕜 s (g ∘ f) :=
  QuasiconvexOn.monotone_comp hg.dual hf

/--
theorem `QuasiconcaveOn.antitone_comp` / 定理 `QuasiconcaveOn.antitone_comp`

English:
theorem QuasiconcaveOn.antitone_comp
  given: (hg : Antitone g) (hf : QuasiconcaveOn 𝕜 s f)
  proof: QuasiconvexOn.monotone_comp (β := βᵒᵈ) hg.dual hf

中文:
定理 QuasiconcaveOn.antitone_comp
  条件: (hg : 递减 g) (hf : QuasiconcaveOn 𝕜 s f)
  证明: QuasiconvexOn.monotone_comp (β := βᵒᵈ) hg.dual hf

Depends on / 依赖: QuasiconvexOn, QuasiconvexOn.monotone_comp, hg.dual, monotone_comp
-/
theorem QuasiconcaveOn.antitone_comp (hg : Antitone g) (hf : QuasiconcaveOn 𝕜 s f) :
    QuasiconvexOn 𝕜 s (g ∘ f) :=
  QuasiconvexOn.monotone_comp (β := βᵒᵈ) hg.dual hf

/--
theorem `QuasilinearOn.monotone_comp` / 定理 `QuasilinearOn.monotone_comp`

English:
theorem QuasilinearOn.monotone_comp
  given: (hg : Monotone g) (hf : QuasilinearOn 𝕜 s f)
  proof: ⟨hf.1.monotone_comp hg, hf.2.monotone_comp hg⟩

中文:
定理 QuasilinearOn.monotone_comp
  条件: (hg : 递增 g) (hf : QuasilinearOn 𝕜 s f)
  证明: ⟨hf.1.monotone_comp hg, hf.2.monotone_comp hg⟩

Depends on / 依赖: monotone_comp
-/
theorem QuasilinearOn.monotone_comp (hg : Monotone g) (hf : QuasilinearOn 𝕜 s f) :
    QuasilinearOn 𝕜 s (g ∘ f) :=
  ⟨hf.1.monotone_comp hg, hf.2.monotone_comp hg⟩

/--
theorem `QuasilinearOn.antitone_comp` / 定理 `QuasilinearOn.antitone_comp`

English:
theorem QuasilinearOn.antitone_comp
  given: (hg : Antitone g) (hf : QuasilinearOn 𝕜 s f)
  proof: ⟨hf.2.antitone_comp hg, hf.1.antitone_comp hg⟩

中文:
定理 QuasilinearOn.antitone_comp
  条件: (hg : 递减 g) (hf : QuasilinearOn 𝕜 s f)
  证明: ⟨hf.2.antitone_comp hg, hf.1.antitone_comp hg⟩

Depends on / 依赖: antitone_comp
-/
theorem QuasilinearOn.antitone_comp (hg : Antitone g) (hf : QuasilinearOn 𝕜 s f) :
    QuasilinearOn 𝕜 s (g ∘ f) :=
  ⟨hf.2.antitone_comp hg, hf.1.antitone_comp hg⟩

end Composition

section Restriction

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [Preorder β]
variable {s : Set E} {f : E -> β}

/--
theorem `Convex.quasiconvexOn_restrict` / 定理 `Convex.quasiconvexOn_restrict`

English:
theorem Convex.quasiconvexOn_restrict
  statement: {t : Set E} (hf : QuasiconvexOn 𝕜 s f) (hst : t subseteq s)
  proof: by
  intro b
  rw [Set.sep_eq_inter_sep hst]
  exact Convex.inter ht (hf b)

中文:
定理 凸.quasiconvexOn_restrict
  结论: {t : 集合 E} (hf : QuasiconvexOn 𝕜 s f) (hst : t subseteq s)
  证明: by
  intro b
  rw [Set.sep_eq_inter_sep hst]
  exact Convex.inter ht (hf b)

Depends on / 依赖: Convex, Convex.inter, Set.sep_eq_inter_sep, sep_eq_inter_sep
-/
theorem Convex.quasiconvexOn_restrict {t : Set E} (hf : QuasiconvexOn 𝕜 s f) (hst : t subseteq s)
    (ht : Convex 𝕜 t) : QuasiconvexOn 𝕜 t f := by
  intro b
  rw [Set.sep_eq_inter_sep hst]
  exact Convex.inter ht (hf b)

/--
theorem `Convex.quasiconcaveOn_restrict` / 定理 `Convex.quasiconcaveOn_restrict`

English:
theorem Convex.quasiconcaveOn_restrict
  statement: {t : Set E} (hf : QuasiconcaveOn 𝕜 s f) (hst : t subseteq s)
  proof: by
  intro b
  rw [Set.sep_eq_inter_sep hst]
  exact Convex.inter ht (hf b)

中文:
定理 凸.quasiconcaveOn_restrict
  结论: {t : 集合 E} (hf : QuasiconcaveOn 𝕜 s f) (hst : t subseteq s)
  证明: by
  intro b
  rw [Set.sep_eq_inter_sep hst]
  exact Convex.inter ht (hf b)

Depends on / 依赖: Convex, Convex.inter, Set.sep_eq_inter_sep, sep_eq_inter_sep
-/
theorem Convex.quasiconcaveOn_restrict {t : Set E} (hf : QuasiconcaveOn 𝕜 s f) (hst : t subseteq s)
    (ht : Convex 𝕜 t) : QuasiconcaveOn 𝕜 t f := by
  intro b
  rw [Set.sep_eq_inter_sep hst]
  exact Convex.inter ht (hf b)

end Restriction

section Preconnected

variable {E : Type*} [AddCommGroup E] [Module Real E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul Real E]

variable {β : Type*} [Preorder β] {f : E -> β}

open scoped Set.Notation

/--
theorem `QuasiconcaveOn.isPreconnected_preimage_subtype` / 定理 `QuasiconcaveOn.isPreconnected_preimage_subtype`

English:
theorem QuasiconcaveOn.isPreconnected_preimage_subtype
  statement: {s : Set E} {t : β}
  proof: by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]; rw [image_preimage_eq_inter_range]; rw [Subtype.range_coe]; rw [inter_comm]
  exact (hfc t).isPreconnected

中文:
定理 QuasiconcaveOn.isPreconnected_preimage_subtype
  结论: {s : 集合 E} {t : β}
  证明: by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]; rw [image_preimage_eq_inter_range]; rw [Subtype.range_coe]; rw [inter_comm]
  exact (hfc t).isPreconnected

Depends on / 依赖: IsInducing, Subtype, Subtype.range_coe, Topology, Topology.IsInducing.subtypeVal.isPreconnected_image, image_preimage_eq_inter_range, inter_comm, isPreconnected, isPreconnected_image, range_coe, subtypeVal
-/
theorem QuasiconcaveOn.isPreconnected_preimage_subtype {s : Set E} {t : β}
    (hfc : QuasiconcaveOn Real s f) :
    IsPreconnected (s ↓inter (f ⁻¹' Ici t)) := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]; rw [image_preimage_eq_inter_range]; rw [Subtype.range_coe]; rw [inter_comm]
  exact (hfc t).isPreconnected

/--
theorem `QuasiconvexOn.isPreconnected_preimage_subtype` / 定理 `QuasiconvexOn.isPreconnected_preimage_subtype`

English:
theorem QuasiconvexOn.isPreconnected_preimage_subtype
  statement: {s : Set E} {t : β}
  proof: QuasiconcaveOn.isPreconnected_preimage_subtype (β := βᵒᵈ) hfc

中文:
定理 QuasiconvexOn.isPreconnected_preimage_subtype
  结论: {s : 集合 E} {t : β}
  证明: QuasiconcaveOn.isPreconnected_preimage_subtype (β := βᵒᵈ) hfc

Depends on / 依赖: QuasiconcaveOn, QuasiconcaveOn.isPreconnected_preimage_subtype, isPreconnected_preimage_subtype
-/
theorem QuasiconvexOn.isPreconnected_preimage_subtype {s : Set E} {t : β}
    (hfc : QuasiconvexOn Real s f) :
    IsPreconnected (s ↓inter (f ⁻¹' Iic t)) :=
  QuasiconcaveOn.isPreconnected_preimage_subtype (β := βᵒᵈ) hfc

/--
theorem `QuasilinearOn.isPreconnected_preimage_subtype` / 定理 `QuasilinearOn.isPreconnected_preimage_subtype`

English:
theorem QuasilinearOn.isPreconnected_preimage_subtype
  statement: {s : Set E} {t : β}
  proof: hfc.left.isPreconnected_preimage_subtype

中文:
定理 QuasilinearOn.isPreconnected_preimage_subtype
  结论: {s : 集合 E} {t : β}
  证明: hfc.left.isPreconnected_preimage_subtype

Depends on / 依赖: hfc.left.isPreconnected_preimage_subtype, isPreconnected_preimage_subtype
-/
theorem QuasilinearOn.isPreconnected_preimage_subtype {s : Set E} {t : β}
    (hfc : QuasilinearOn Real s f) :
    IsPreconnected (s ↓inter f ⁻¹' Iic t) :=
  hfc.left.isPreconnected_preimage_subtype

end Preconnected

section Semilattice_β

variable [SMul 𝕜 E] {s : Set E} {f g : E -> β}

/--
theorem `QuasiconvexOn.sup` / 定理 `QuasiconvexOn.sup`

English:
theorem QuasiconvexOn.sup
  statement: [SemilatticeSup β] (hf : QuasiconvexOn 𝕜 s f)
  proof: by
  intro r
  simp_rw [Pi.sup_def, sup_le_iff, Set.sep_and]
  exact (hf r).inter (hg r)

中文:
定理 QuasiconvexOn.上确界
  结论: [SemilatticeSup β] (hf : QuasiconvexOn 𝕜 s f)
  证明: by
  intro r
  simp_rw [Pi.sup_def, sup_le_iff, Set.sep_and]
  exact (hf r).inter (hg r)

Depends on / 依赖: Pi.sup_def, Set.sep_and, sep_and, simp_rw, sup_def, sup_le_iff
-/
theorem QuasiconvexOn.sup [SemilatticeSup β] (hf : QuasiconvexOn 𝕜 s f)
    (hg : QuasiconvexOn 𝕜 s g) : QuasiconvexOn 𝕜 s (f ⊔ g) := by
  intro r
  simp_rw [Pi.sup_def, sup_le_iff, Set.sep_and]
  exact (hf r).inter (hg r)

/--
theorem `QuasiconcaveOn.inf` / 定理 `QuasiconcaveOn.inf`

English:
theorem QuasiconcaveOn.inf
  statement: [SemilatticeInf β] (hf : QuasiconcaveOn 𝕜 s f)
  proof: hf.dual.sup hg

中文:
定理 QuasiconcaveOn.下确界
  结论: [SemilatticeInf β] (hf : QuasiconcaveOn 𝕜 s f)
  证明: hf.dual.sup hg

Depends on / 依赖: hf.dual.sup
-/
theorem QuasiconcaveOn.inf [SemilatticeInf β] (hf : QuasiconcaveOn 𝕜 s f)
    (hg : QuasiconcaveOn 𝕜 s g) : QuasiconcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg

end Semilattice_β

section LinearOrder_β

variable [LinearOrder β] [SMul 𝕜 E] {s : Set E} {f : E -> β}

/--
theorem `quasiconvexOn_iff_le_max` / 定理 `quasiconvexOn_iff_le_max`

English:
theorem quasiconvexOn_iff_le_max
  statement: QuasiconvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄,
  proof: ⟨fun hf =>
    ⟨hf.convex, fun _ hx _ hy _ _ ha hb hab =>
      (hf _ ⟨hx, le_max_left _ _⟩ ⟨hy, le_max_right _ _⟩ ha hb hab).2⟩,
    fun hf _ _ hx _ hy _ _ ha hb hab =>
⟨hf.1 hx.1 hy.1 ha hb hab, (hf.2 hx.1 hy.1 ha hb hab).trans max_le hx.2 hy.2⟩⟩

中文:
定理 quasiconvexOn_iff_le_max
  结论: QuasiconvexOn 𝕜 s f ↔ 凸 𝕜 s ∧ 对任意 ⦃x⦄, x in s -> 对任意 ⦃y⦄,
  证明: ⟨fun hf =>
    ⟨hf.convex, fun _ hx _ hy _ _ ha hb hab =>
      (hf _ ⟨hx, le_max_left _ _⟩ ⟨hy, le_max_right _ _⟩ ha hb hab).2⟩,
    fun hf _ _ hx _ hy _ _ ha hb hab =>
⟨hf.1 hx.1 hy.1 ha hb hab, (hf.2 hx.1 hy.1 ha hb hab).trans max_le hx.2 hy.2⟩⟩

Depends on / 依赖: convex, hf.convex, le_max_left, le_max_right, max_le
-/
theorem quasiconvexOn_iff_le_max : QuasiconvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄,
    y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 -> f (a • x + b • y) <= max (f x) (f y) :=
  ⟨fun hf =>
    ⟨hf.convex, fun _ hx _ hy _ _ ha hb hab =>
      (hf _ ⟨hx, le_max_left _ _⟩ ⟨hy, le_max_right _ _⟩ ha hb hab).2⟩,
    fun hf _ _ hx _ hy _ _ ha hb hab =>
⟨hf.1 hx.1 hy.1 ha hb hab, (hf.2 hx.1 hy.1 ha hb hab).trans max_le hx.2 hy.2⟩⟩

/--
theorem `quasiconcaveOn_iff_min_le` / 定理 `quasiconcaveOn_iff_min_le`

English:
theorem quasiconcaveOn_iff_min_le
  statement: QuasiconcaveOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄,
  proof: quasiconvexOn_iff_le_max (β := βᵒᵈ)

中文:
定理 quasiconcaveOn_iff_min_le
  结论: QuasiconcaveOn 𝕜 s f ↔ 凸 𝕜 s ∧ 对任意 ⦃x⦄, x in s -> 对任意 ⦃y⦄,
  证明: quasiconvexOn_iff_le_max (β := βᵒᵈ)

Depends on / 依赖: quasiconvexOn_iff_le_max
-/
theorem quasiconcaveOn_iff_min_le : QuasiconcaveOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄,
    y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 -> min (f x) (f y) <= f (a • x + b • y) :=
  quasiconvexOn_iff_le_max (β := βᵒᵈ)

/--
theorem `quasilinearOn_iff_mem_uIcc` / 定理 `quasilinearOn_iff_mem_uIcc`

English:
theorem quasilinearOn_iff_mem_uIcc
  statement: QuasilinearOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄,
  proof: by
  rw [QuasilinearOn]; rw [quasiconvexOn_iff_le_max]; rw [quasiconcaveOn_iff_min_le]; rw [and_and_and_comm]; rw [and_self_iff]
  apply and_congr_right'
  simp_rw [← forall_and, ← Icc_min_max, mem_Icc, and_comm]

中文:
定理 quasilinearOn_iff_mem_uIcc
  结论: QuasilinearOn 𝕜 s f ↔ 凸 𝕜 s ∧ 对任意 ⦃x⦄, x in s -> 对任意 ⦃y⦄,
  证明: by
  rw [QuasilinearOn]; rw [quasiconvexOn_iff_le_max]; rw [quasiconcaveOn_iff_min_le]; rw [and_and_and_comm]; rw [and_self_iff]
  apply and_congr_right'
  simp_rw [← forall_and, ← Icc_min_max, mem_Icc, and_comm]

Depends on / 依赖: Icc_min_max, QuasilinearOn, and_and_and_comm, and_comm, and_congr_right, and_self_iff, forall_and, mem_Icc, quasiconcaveOn_iff_min_le, quasiconvexOn_iff_le_max, simp_rw
-/
theorem quasilinearOn_iff_mem_uIcc : QuasilinearOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄,
    y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 -> f (a • x + b • y) in uIcc (f x) (f y) := by
  rw [QuasilinearOn]; rw [quasiconvexOn_iff_le_max]; rw [quasiconcaveOn_iff_min_le]; rw [and_and_and_comm]; rw [and_self_iff]
  apply and_congr_right'
  simp_rw [← forall_and, ← Icc_min_max, mem_Icc, and_comm]

/--
theorem `QuasiconvexOn.convex_lt` / 定理 `QuasiconvexOn.convex_lt`

English:
theorem QuasiconvexOn.convex_lt
  given: (hf : QuasiconvexOn 𝕜 s f) (r : β)
  proof: by
  intro x hx y hy a b ha hb hab
  have h := hf _ ⟨hx.1, le_max_left _ _⟩ ⟨hy.1, le_max_right _ _⟩ ha hb hab
exact ⟨h.1, h.2.trans_lt max_lt hx.2 hy.2⟩

中文:
定理 QuasiconvexOn.convex_lt
  条件: (hf : QuasiconvexOn 𝕜 s f) (r : β)
  证明: by
  intro x hx y hy a b ha hb hab
  have h := hf _ ⟨hx.1, le_max_left _ _⟩ ⟨hy.1, le_max_right _ _⟩ ha hb hab
exact ⟨h.1, h.2.trans_lt max_lt hx.2 hy.2⟩

Depends on / 依赖: le_max_left, le_max_right, max_lt, trans_lt
-/
theorem QuasiconvexOn.convex_lt (hf : QuasiconvexOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x in s | f x < r }) := by
  intro x hx y hy a b ha hb hab
  have h := hf _ ⟨hx.1, le_max_left _ _⟩ ⟨hy.1, le_max_right _ _⟩ ha hb hab
exact ⟨h.1, h.2.trans_lt max_lt hx.2 hy.2⟩

/--
theorem `QuasiconcaveOn.convex_gt` / 定理 `QuasiconcaveOn.convex_gt`

English:
theorem QuasiconcaveOn.convex_gt
  given: (hf : QuasiconcaveOn 𝕜 s f) (r : β)
  proof: hf.dual.convex_lt r

中文:
定理 QuasiconcaveOn.convex_gt
  条件: (hf : QuasiconcaveOn 𝕜 s f) (r : β)
  证明: hf.dual.convex_lt r

Depends on / 依赖: convex_lt, hf.dual.convex_lt
-/
theorem QuasiconcaveOn.convex_gt (hf : QuasiconcaveOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x in s | r < f x }) :=
  hf.dual.convex_lt r

end LinearOrder_β

section PosSMulMono

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module 𝕜 E] [Module 𝕜 β] [PosSMulMono 𝕜 β]
  {s : Set E} {f : E -> β}

/--
theorem `ConvexOn.quasiconvexOn` / 定理 `ConvexOn.quasiconvexOn`

English:
theorem ConvexOn.quasiconvexOn
  given: (hf : ConvexOn 𝕜 s f)
  statement: QuasiconvexOn 𝕜 s f
  proof: hf.convex_le

中文:
定理 ConvexOn.quasiconvexOn
  条件: (hf : ConvexOn 𝕜 s f)
  结论: QuasiconvexOn 𝕜 s f
  证明: hf.convex_le

Depends on / 依赖: convex_le, hf.convex_le
-/
theorem ConvexOn.quasiconvexOn (hf : ConvexOn 𝕜 s f) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le

/--
theorem `ConcaveOn.quasiconcaveOn` / 定理 `ConcaveOn.quasiconcaveOn`

English:
theorem ConcaveOn.quasiconcaveOn
  given: (hf : ConcaveOn 𝕜 s f)
  statement: QuasiconcaveOn 𝕜 s f
  proof: hf.convex_ge

中文:
定理 ConcaveOn.quasiconcaveOn
  条件: (hf : ConcaveOn 𝕜 s f)
  结论: QuasiconcaveOn 𝕜 s f
  证明: hf.convex_ge

Depends on / 依赖: convex_ge, hf.convex_ge
-/
theorem ConcaveOn.quasiconcaveOn (hf : ConcaveOn 𝕜 s f) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge

end PosSMulMono

section LinearOrder

variable [LinearOrder E] [IsOrderedAddMonoid E] [PartialOrder β] [Module 𝕜 E] [PosSMulMono 𝕜 E]
  {s : Set E} {f : E -> β}

/--
theorem `MonotoneOn.quasiconvexOn` / 定理 `MonotoneOn.quasiconvexOn`

English:
theorem MonotoneOn.quasiconvexOn
  given: (hf : MonotoneOn f s) (hs : Convex 𝕜 s)
  statement: QuasiconvexOn 𝕜 s f
  proof: hf.convex_le hs

中文:
定理 MonotoneOn.quasiconvexOn
  条件: (hf : MonotoneOn f s) (hs : 凸 𝕜 s)
  结论: QuasiconvexOn 𝕜 s f
  证明: hf.convex_le hs

Depends on / 依赖: convex_le, hf.convex_le
-/
theorem MonotoneOn.quasiconvexOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le hs

/--
theorem `MonotoneOn.quasiconcaveOn` / 定理 `MonotoneOn.quasiconcaveOn`

English:
theorem MonotoneOn.quasiconcaveOn
  given: (hf : MonotoneOn f s) (hs : Convex 𝕜 s)
  statement: QuasiconcaveOn 𝕜 s f
  proof: hf.convex_ge hs

中文:
定理 MonotoneOn.quasiconcaveOn
  条件: (hf : MonotoneOn f s) (hs : 凸 𝕜 s)
  结论: QuasiconcaveOn 𝕜 s f
  证明: hf.convex_ge hs

Depends on / 依赖: convex_ge, hf.convex_ge
-/
theorem MonotoneOn.quasiconcaveOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge hs

/--
theorem `MonotoneOn.quasilinearOn` / 定理 `MonotoneOn.quasilinearOn`

English:
theorem MonotoneOn.quasilinearOn
  given: (hf : MonotoneOn f s) (hs : Convex 𝕜 s)
  statement: QuasilinearOn 𝕜 s f
  proof: ⟨hf.quasiconvexOn hs, hf.quasiconcaveOn hs⟩

中文:
定理 MonotoneOn.quasilinearOn
  条件: (hf : MonotoneOn f s) (hs : 凸 𝕜 s)
  结论: QuasilinearOn 𝕜 s f
  证明: ⟨hf.quasiconvexOn hs, hf.quasiconcaveOn hs⟩

Depends on / 依赖: hf.quasiconcaveOn, hf.quasiconvexOn, quasiconcaveOn, quasiconvexOn
-/
theorem MonotoneOn.quasilinearOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f :=
  ⟨hf.quasiconvexOn hs, hf.quasiconcaveOn hs⟩

/--
theorem `AntitoneOn.quasiconvexOn` / 定理 `AntitoneOn.quasiconvexOn`

English:
theorem AntitoneOn.quasiconvexOn
  given: (hf : AntitoneOn f s) (hs : Convex 𝕜 s)
  statement: QuasiconvexOn 𝕜 s f
  proof: hf.convex_le hs

中文:
定理 AntitoneOn.quasiconvexOn
  条件: (hf : AntitoneOn f s) (hs : 凸 𝕜 s)
  结论: QuasiconvexOn 𝕜 s f
  证明: hf.convex_le hs

Depends on / 依赖: CompleteSpace, HasOrthogonalProjection, HasOrthogonalProjection.ofCompleteSpace, convex_le, hf.convex_le, ofCompleteSpace
-/
theorem AntitoneOn.quasiconvexOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le hs

/--
theorem `AntitoneOn.quasiconcaveOn` / 定理 `AntitoneOn.quasiconcaveOn`

English:
theorem AntitoneOn.quasiconcaveOn
  given: (hf : AntitoneOn f s) (hs : Convex 𝕜 s)
  statement: QuasiconcaveOn 𝕜 s f
  proof: hf.convex_ge hs

中文:
定理 AntitoneOn.quasiconcaveOn
  条件: (hf : AntitoneOn f s) (hs : 凸 𝕜 s)
  结论: QuasiconcaveOn 𝕜 s f
  证明: hf.convex_ge hs

Depends on / 依赖: convex_ge, hf.convex_ge
-/
theorem AntitoneOn.quasiconcaveOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge hs

/--
theorem `AntitoneOn.quasilinearOn` / 定理 `AntitoneOn.quasilinearOn`

English:
theorem AntitoneOn.quasilinearOn
  given: (hf : AntitoneOn f s) (hs : Convex 𝕜 s)
  statement: QuasilinearOn 𝕜 s f
  proof: ⟨hf.quasiconvexOn hs, hf.quasiconcaveOn hs⟩

中文:
定理 AntitoneOn.quasilinearOn
  条件: (hf : AntitoneOn f s) (hs : 凸 𝕜 s)
  结论: QuasilinearOn 𝕜 s f
  证明: ⟨hf.quasiconvexOn hs, hf.quasiconcaveOn hs⟩

Depends on / 依赖: hf.quasiconcaveOn, hf.quasiconvexOn, quasiconcaveOn, quasiconvexOn
-/
theorem AntitoneOn.quasilinearOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f :=
  ⟨hf.quasiconvexOn hs, hf.quasiconcaveOn hs⟩

/--
theorem `Monotone.quasiconvexOn` / 定理 `Monotone.quasiconvexOn`

English:
theorem Monotone.quasiconvexOn
  given: (hf : Monotone f)
  statement: QuasiconvexOn 𝕜 univ f
  proof: (hf.monotoneOn _).quasiconvexOn convex_univ

中文:
定理 递增.quasiconvexOn
  条件: (hf : 递增 f)
  结论: QuasiconvexOn 𝕜 univ f
  证明: (hf.monotoneOn _).quasiconvexOn convex_univ

Depends on / 依赖: convex_univ, hf.monotoneOn, monotoneOn, quasiconvexOn
-/
theorem Monotone.quasiconvexOn (hf : Monotone f) : QuasiconvexOn 𝕜 univ f :=
  (hf.monotoneOn _).quasiconvexOn convex_univ

/--
theorem `Monotone.quasiconcaveOn` / 定理 `Monotone.quasiconcaveOn`

English:
theorem Monotone.quasiconcaveOn
  given: (hf : Monotone f)
  statement: QuasiconcaveOn 𝕜 univ f
  proof: (hf.monotoneOn _).quasiconcaveOn convex_univ

中文:
定理 递增.quasiconcaveOn
  条件: (hf : 递增 f)
  结论: QuasiconcaveOn 𝕜 univ f
  证明: (hf.monotoneOn _).quasiconcaveOn convex_univ

Depends on / 依赖: convex_univ, hf.monotoneOn, monotoneOn, quasiconcaveOn
-/
theorem Monotone.quasiconcaveOn (hf : Monotone f) : QuasiconcaveOn 𝕜 univ f :=
  (hf.monotoneOn _).quasiconcaveOn convex_univ

/--
theorem `Monotone.quasilinearOn` / 定理 `Monotone.quasilinearOn`

English:
theorem Monotone.quasilinearOn
  given: (hf : Monotone f)
  statement: QuasilinearOn 𝕜 univ f
  proof: ⟨hf.quasiconvexOn, hf.quasiconcaveOn⟩

中文:
定理 递增.quasilinearOn
  条件: (hf : 递增 f)
  结论: QuasilinearOn 𝕜 univ f
  证明: ⟨hf.quasiconvexOn, hf.quasiconcaveOn⟩

Depends on / 依赖: K.isClosed, hf.quasiconcaveOn, hf.quasiconvexOn, infer_instance, isClosed, quasiconcaveOn, quasiconvexOn
-/
theorem Monotone.quasilinearOn (hf : Monotone f) : QuasilinearOn 𝕜 univ f :=
  ⟨hf.quasiconvexOn, hf.quasiconcaveOn⟩

/--
theorem `Antitone.quasiconvexOn` / 定理 `Antitone.quasiconvexOn`

English:
theorem Antitone.quasiconvexOn
  given: (hf : Antitone f)
  statement: QuasiconvexOn 𝕜 univ f
  proof: (hf.antitoneOn _).quasiconvexOn convex_univ

中文:
定理 递减.quasiconvexOn
  条件: (hf : 递减 f)
  结论: QuasiconvexOn 𝕜 univ f
  证明: (hf.antitoneOn _).quasiconvexOn convex_univ

Depends on / 依赖: antitoneOn, convex_univ, hf.antitoneOn, quasiconvexOn
-/
theorem Antitone.quasiconvexOn (hf : Antitone f) : QuasiconvexOn 𝕜 univ f :=
  (hf.antitoneOn _).quasiconvexOn convex_univ

/--
theorem `Antitone.quasiconcaveOn` / 定理 `Antitone.quasiconcaveOn`

English:
theorem Antitone.quasiconcaveOn
  given: (hf : Antitone f)
  statement: QuasiconcaveOn 𝕜 univ f
  proof: (hf.antitoneOn _).quasiconcaveOn convex_univ

中文:
定理 递减.quasiconcaveOn
  条件: (hf : 递减 f)
  结论: QuasiconcaveOn 𝕜 univ f
  证明: (hf.antitoneOn _).quasiconcaveOn convex_univ

Depends on / 依赖: antitoneOn, convex_univ, hf.antitoneOn, quasiconcaveOn
-/
theorem Antitone.quasiconcaveOn (hf : Antitone f) : QuasiconcaveOn 𝕜 univ f :=
  (hf.antitoneOn _).quasiconcaveOn convex_univ

/--
theorem `Antitone.quasilinearOn` / 定理 `Antitone.quasilinearOn`

English:
theorem Antitone.quasilinearOn
  given: (hf : Antitone f)
  statement: QuasilinearOn 𝕜 univ f
  proof: ⟨hf.quasiconvexOn, hf.quasiconcaveOn⟩

中文:
定理 递减.quasilinearOn
  条件: (hf : 递减 f)
  结论: QuasilinearOn 𝕜 univ f
  证明: ⟨hf.quasiconvexOn, hf.quasiconcaveOn⟩

Depends on / 依赖: hf.quasiconcaveOn, hf.quasiconvexOn, quasiconcaveOn, quasiconvexOn
-/
theorem Antitone.quasilinearOn (hf : Antitone f) : QuasilinearOn 𝕜 univ f :=
  ⟨hf.quasiconvexOn, hf.quasiconcaveOn⟩

end LinearOrder
end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} {f : 𝕜 -> β}

/--
theorem `QuasilinearOn.monotoneOn_or_antitoneOn` / 定理 `QuasilinearOn.monotoneOn_or_antitoneOn`

English:
theorem QuasilinearOn.monotoneOn_or_antitoneOn
  given: [LinearOrder β] (hf : QuasilinearOn 𝕜 s f)
  proof: by
  simp_rw [monotoneOn_or_antitoneOn_iff_uIcc, ← segment_eq_uIcc]
  rintro a ha b hb c _ h
  refine ⟨((hf.2 _).segment_subset ?_ ?_ h).2, ((hf.1 _).segment_subset ?_ ?_ h).2⟩ <;> simp [*]

中文:
定理 QuasilinearOn.monotoneOn_or_antitoneOn
  条件: [线性序 β] (hf : QuasilinearOn 𝕜 s f)
  证明: by
  simp_rw [monotoneOn_or_antitoneOn_iff_uIcc, ← segment_eq_uIcc]
  rintro a ha b hb c _ h
  refine ⟨((hf.2 _).segment_subset ?_ ?_ h).2, ((hf.1 _).segment_subset ?_ ?_ h).2⟩ <;> simp [*]

Depends on / 依赖: monotoneOn_or_antitoneOn_iff_uIcc, segment_eq_uIcc, segment_subset, simp_rw
-/
theorem QuasilinearOn.monotoneOn_or_antitoneOn [LinearOrder β] (hf : QuasilinearOn 𝕜 s f) :
    MonotoneOn f s ∨ AntitoneOn f s := by
  simp_rw [monotoneOn_or_antitoneOn_iff_uIcc, ← segment_eq_uIcc]
  rintro a ha b hb c _ h
  refine ⟨((hf.2 _).segment_subset ?_ ?_ h).2, ((hf.1 _).segment_subset ?_ ?_ h).2⟩ <;> simp [*]

/--
theorem `quasilinearOn_iff_monotoneOn_or_antitoneOn` / 定理 `quasilinearOn_iff_monotoneOn_or_antitoneOn`

English:
theorem quasilinearOn_iff_monotoneOn_or_antitoneOn
  statement: [LinearOrder β]
  proof: ⟨fun h => h.monotoneOn_or_antitoneOn, fun h =>
    h.elim (fun h => h.quasilinearOn hs) fun h => h.quasilinearOn hs⟩

中文:
定理 quasilinearOn_iff_monotoneOn_or_antitoneOn
  结论: [线性序 β]
  证明: ⟨fun h => h.monotoneOn_or_antitoneOn, fun h =>
    h.elim (fun h => h.quasilinearOn hs) fun h => h.quasilinearOn hs⟩

Depends on / 依赖: h.elim, h.monotoneOn_or_antitoneOn, h.quasilinearOn, monotoneOn_or_antitoneOn, quasilinearOn
-/
theorem quasilinearOn_iff_monotoneOn_or_antitoneOn [LinearOrder β]
    (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f ↔ MonotoneOn f s ∨ AntitoneOn f s :=
  ⟨fun h => h.monotoneOn_or_antitoneOn, fun h =>
    h.elim (fun h => h.quasilinearOn hs) fun h => h.quasilinearOn hs⟩

end LinearOrderedField
