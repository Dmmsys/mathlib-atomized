/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.RelIso.Basic

/-!
# Order continuity

We say that a function is *left order continuous* if it sends all least upper bounds
to least upper bounds. The order dual notion is called *right order continuity*.

For monotone functions `ℝ → ℝ` these notions correspond to the usual left and right continuity.

We prove some basic lemmas (`map_sup`, `map_sSup` etc) and prove that a `RelIso` is both left
and right order continuous.
-/

@[expose] public section


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open Function OrderDual Set

/-!
### Definitions
-/


/-- A function `f` between preorders is left order continuous if it preserves all suprema of
nonempty sets. We define it using `IsLUB` instead of `sSup` so that the proof works both for
complete lattices and conditionally complete lattices. -/
@[to_dual
/-- A function `f` between preorders is right order continuous if it preserves all infima of
nonempty sets. We define it using `IsGLB` instead of `sInf` so that the proof works both for
complete lattices and conditionally complete lattices. -/]
/--
Definition of `LeftOrdContinuous` / `LeftOrdContinuous` 的定义

English:
definition LeftOrdContinuous
  signature: [Preorder α] [Preorder β] (f : α -> β)
  body: forall ⦃s : Set α⦄ ⦃x⦄, s.Nonempty -> IsLUB s x -> IsLUB (f '' s) (f x)

中文:
定义 LeftOrdContinuous
  签名: [Preorder α] [Preorder β] (f : α -> β)
  定义体: forall ⦃s : Set α⦄ ⦃x⦄, s.Nonempty -> IsLUB s x -> IsLUB (f '' s) (f x)

Depends on / 依赖: Nonempty, s.Nonempty
-/
def LeftOrdContinuous [Preorder α] [Preorder β] (f : α -> β) :=
  forall ⦃s : Set α⦄ ⦃x⦄, s.Nonempty -> IsLUB s x -> IsLUB (f '' s) (f x)

namespace LeftOrdContinuous

section Preorder

variable (α) [Preorder α] [Preorder β] [Preorder γ] {g : β -> γ} {f : α -> β}

@[to_dual]
/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: LeftOrdContinuous (id : α -> α)
  proof: fun s _ x h => by
  simpa only [image_id] using! h

中文:
定理 id
  结论: LeftOrdContinuous (id : α -> α)
  证明: fun s _ x h => by
  simpa only [image_id] using! h
-/
protected theorem id : LeftOrdContinuous (id : α -> α) := fun s _ x h => by
  simpa only [image_id] using! h

variable {α}

@[to_dual]
/--
theorem `dual` / 定理 `dual`

English:
theorem dual
  proof: id

@[deprecated (since := "2026-04-08")] alias rightOrdContinuous_dual := LeftOrdContinuous.dual

@[deprecated (since := "2026-04-08")] alias _root_.RightOrdContinuous.orderDual :=
  RightOrdContinuous.dual

@[to_dual]

中文:
定理 dual
  证明: id

@[deprecated (since := "2026-04-08")] alias rightOrdContinuous_dual := LeftOrdContinuous.dual

@[deprecated (since := "2026-04-08")] alias _root_.RightOrdContinuous.orderDual :=
  RightOrdContinuous.dual

@[to_dual]
-/
protected theorem dual :
    LeftOrdContinuous f -> RightOrdContinuous (toDual ∘ f ∘ ofDual) :=
  id

@[deprecated (since := "2026-04-08")] alias rightOrdContinuous_dual := LeftOrdContinuous.dual

@[deprecated (since := "2026-04-08")] alias _root_.RightOrdContinuous.orderDual :=
  RightOrdContinuous.dual

@[to_dual]
/--
theorem `map_isGreatest` / 定理 `map_isGreatest`

English:
theorem map_isGreatest
  given: (hf : LeftOrdContinuous f) {s : Set α} {x : α} (h : IsGreatest s x)
  proof: ⟨mem_image_of_mem f h.1, (hf ⟨x, h.1⟩ h.isLUB).1⟩

@[to_dual]

中文:
定理 map_isGreatest
  条件: (hf : LeftOrdContinuous f) {s : Set α} {x : α} (h : IsGreatest s x)
  证明: ⟨mem_image_of_mem f h.1, (hf ⟨x, h.1⟩ h.isLUB).1⟩

@[to_dual]

Depends on / 依赖: h.isLUB, mem_image_of_mem
-/
theorem map_isGreatest (hf : LeftOrdContinuous f) {s : Set α} {x : α} (h : IsGreatest s x) :
    IsGreatest (f '' s) (f x) :=
  ⟨mem_image_of_mem f h.1, (hf ⟨x, h.1⟩ h.isLUB).1⟩

@[to_dual]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (hf : LeftOrdContinuous f)
  statement: Monotone f
  proof: fun a₁ a₂ h =>
  have : IsGreatest {a₁, a₂} a₂ := ⟨Or.inr rfl, by simp [*]⟩
(hf.map_isGreatest this).2 mem_image_of_mem _ (Or.inl rfl)

@[to_dual]

中文:
定理 mono
  条件: (hf : LeftOrdContinuous f)
  结论: Monotone f
  证明: fun a₁ a₂ h =>
  have : IsGreatest {a₁, a₂} a₂ := ⟨Or.inr rfl, by simp [*]⟩
(hf.map_isGreatest this).2 mem_image_of_mem _ (Or.inl rfl)

@[to_dual]
-/
theorem mono (hf : LeftOrdContinuous f) : Monotone f := fun a₁ a₂ h =>
  have : IsGreatest {a₁, a₂} a₂ := ⟨Or.inr rfl, by simp [*]⟩
(hf.map_isGreatest this).2 mem_image_of_mem _ (Or.inl rfl)

@[to_dual]
/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hg : LeftOrdContinuous g) (hf : LeftOrdContinuous f)
  statement: LeftOrdContinuous (g ∘ f)
  proof: fun s x hs h => by simpa only [image_image] using! hg (.image _ hs) (hf hs h)

@[to_dual]

中文:
定理 comp
  条件: (hg : LeftOrdContinuous g) (hf : LeftOrdContinuous f)
  结论: LeftOrdContinuous (g ∘ f)
  证明: fun s x hs h => by simpa only [image_image] using! hg (.image _ hs) (hf hs h)

@[to_dual]

Depends on / 依赖: image_image
-/
theorem comp (hg : LeftOrdContinuous g) (hf : LeftOrdContinuous f) : LeftOrdContinuous (g ∘ f) :=
  fun s x hs h => by simpa only [image_image] using! hg (.image _ hs) (hf hs h)

@[to_dual]
/--
theorem `iterate` / 定理 `iterate`

English:
theorem iterate
  given: {f : α -> α} (hf : LeftOrdContinuous f) (n : Nat)
  proof: match n with
  | 0 => LeftOrdContinuous.id α
  | (n + 1) => (LeftOrdContinuous.iterate hf n).comp hf

中文:
定理 iterate
  条件: {f : α -> α} (hf : LeftOrdContinuous f) (n : 自然数)
  证明: match n with
  | 0 => LeftOrdContinuous.id α
  | (n + 1) => (LeftOrdContinuous.iterate hf n).comp hf
-/
protected theorem iterate {f : α -> α} (hf : LeftOrdContinuous f) (n : Nat) :
    LeftOrdContinuous f^[n] :=
  match n with
  | 0 => LeftOrdContinuous.id α
  | (n + 1) => (LeftOrdContinuous.iterate hf n).comp hf

end Preorder

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {f : α -> β}

@[to_dual]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (hf : LeftOrdContinuous f) (x y : α)
  statement: f (x ⊔ y) = f x ⊔ f y
  proof: (hf (insert_nonempty ..) isLUB_pair).unique by simp only [image_pair, isLUB_pair]

@[to_dual]

中文:
定理 map_sup
  条件: (hf : LeftOrdContinuous f) (x y : α)
  结论: f (x ⊔ y) = f x ⊔ f y
  证明: (hf (insert_nonempty ..) isLUB_pair).unique by simp only [image_pair, isLUB_pair]

@[to_dual]

Depends on / 依赖: image_pair, insert_nonempty, isLUB_pair, unique
-/
theorem map_sup (hf : LeftOrdContinuous f) (x y : α) : f (x ⊔ y) = f x ⊔ f y :=
(hf (insert_nonempty ..) isLUB_pair).unique by simp only [image_pair, isLUB_pair]

@[to_dual]
/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  given: (hf : LeftOrdContinuous f) (h : Injective f) {x y}
  statement: f x <= f y ↔ x <= y
  proof: by
  simp only [← sup_eq_right, ← hf.map_sup, h.eq_iff]

@[to_dual]

中文:
定理 le_iff
  条件: (hf : LeftOrdContinuous f) (h : Injective f) {x y}
  结论: f x <= f y ↔ x <= y
  证明: by
  simp only [← sup_eq_right, ← hf.map_sup, h.eq_iff]

@[to_dual]

Depends on / 依赖: eq_iff, h.eq_iff, hf.map_sup, map_sup, sup_eq_right
-/
theorem le_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x <= f y ↔ x <= y := by
  simp only [← sup_eq_right, ← hf.map_sup, h.eq_iff]

@[to_dual]
/--
theorem `lt_iff` / 定理 `lt_iff`

English:
theorem lt_iff
  given: (hf : LeftOrdContinuous f) (h : Injective f) {x y}
  statement: f x < f y ↔ x < y
  proof: by
  simp only [lt_iff_le_not_ge, hf.le_iff h]

中文:
定理 lt_iff
  条件: (hf : LeftOrdContinuous f) (h : Injective f) {x y}
  结论: f x < f y ↔ x < y
  证明: by
  simp only [lt_iff_le_not_ge, hf.le_iff h]

Depends on / 依赖: hf.le_iff, le_iff, lt_iff_le_not_ge
-/
theorem lt_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x < f y ↔ x < y := by
  simp only [lt_iff_le_not_ge, hf.le_iff h]

variable (f)

/-- Convert an injective left order continuous function to an order embedding. -/
@[to_dual
/-- Convert an injective right order continuous function to an order embedding. -/]
/--
Definition of `toOrderEmbedding` / `toOrderEmbedding` 的定义

English:
definition toOrderEmbedding
  signature: (hf : LeftOrdContinuous f) (h : Injective f)
  body: ⟨⟨f, h⟩, hf.le_iff h⟩

中文:
定义 toOrderEmbedding
  签名: (hf : LeftOrdContinuous f) (h : Injective f)
  定义体: ⟨⟨f, h⟩, hf.le_iff h⟩

Depends on / 依赖: hf.le_iff, le_iff
-/
def toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) : α ↪o β :=
  ⟨⟨f, h⟩, hf.le_iff h⟩

variable {f}

@[to_dual (attr := simp)]
/--
theorem `coe_toOrderEmbedding` / 定理 `coe_toOrderEmbedding`

English:
theorem coe_toOrderEmbedding
  given: (hf : LeftOrdContinuous f) (h : Injective f)
  proof: rfl

中文:
定理 coe_toOrderEmbedding
  条件: (hf : LeftOrdContinuous f) (h : Injective f)
  证明: rfl
-/
theorem coe_toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) :
    ⇑(hf.toOrderEmbedding f h) = f :=
  rfl

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α -> β}

@[to_dual]
/--
theorem `map_sSup'` / 定理 `map_sSup'`

English:
theorem map_sSup'
  given: (hf : LeftOrdContinuous f) {s : Set α} (hs : s.Nonempty)
  proof: (hf hs <| isLUB_sSup s).sSup_eq.symm

@[to_dual]

中文:
定理 map_sSup'
  条件: (hf : LeftOrdContinuous f) {s : Set α} (hs : s.Nonempty)
  证明: (hf hs <| isLUB_sSup s).sSup_eq.symm

@[to_dual]

Depends on / 依赖: IsMaximal, isLUB_sSup, isMaximal, jacobson, jacobson.isMaximal, sSup_eq, sSup_eq.symm
-/
theorem map_sSup' (hf : LeftOrdContinuous f) {s : Set α} (hs : s.Nonempty) :
    f (sSup s) = sSup (f '' s) :=
  (hf hs <| isLUB_sSup s).sSup_eq.symm

@[to_dual]
/--
theorem `map_sSup` / 定理 `map_sSup`

English:
theorem map_sSup
  given: (hf : LeftOrdContinuous f) {s : Set α} (hs : s.Nonempty)
  proof: by
  rw [hf.map_sSup' hs]; rw [sSup_image]

@[to_dual]

中文:
定理 map_sSup
  条件: (hf : LeftOrdContinuous f) {s : Set α} (hs : s.Nonempty)
  证明: by
  rw [hf.map_sSup' hs]; rw [sSup_image]

@[to_dual]

Depends on / 依赖: hf.map_sSup, map_sSup, sSup_image
-/
theorem map_sSup (hf : LeftOrdContinuous f) {s : Set α} (hs : s.Nonempty) :
    f (sSup s) = ⨆ x in s, f x := by
  rw [hf.map_sSup' hs]; rw [sSup_image]

@[to_dual]
/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: (hf : LeftOrdContinuous f) [Nonempty ι] (g : ι -> α)
  proof: by
  simp only [iSup, hf.map_sSup' (range_nonempty g), ← range_comp]
  rfl

中文:
定理 map_iSup
  条件: (hf : LeftOrdContinuous f) [Nonempty ι] (g : ι -> α)
  证明: by
  simp only [iSup, hf.map_sSup' (range_nonempty g), ← range_comp]
  rfl

Depends on / 依赖: hf.map_sSup, map_sSup, range_comp, range_nonempty
-/
theorem map_iSup (hf : LeftOrdContinuous f) [Nonempty ι] (g : ι -> α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [iSup, hf.map_sSup' (range_nonempty g), ← range_comp]
  rfl

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α -> β}

@[to_dual]
/--
theorem `map_csSup` / 定理 `map_csSup`

English:
theorem map_csSup
  given: (hf : LeftOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddAbove s)
  proof: ((hf sne <| isLUB_csSup sne sbdd).csSup_eq <| sne.image f).symm

@[to_dual]

中文:
定理 map_csSup
  条件: (hf : LeftOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddAbove s)
  证明: ((hf sne <| isLUB_csSup sne sbdd).csSup_eq <| sne.image f).symm

@[to_dual]

Depends on / 依赖: csSup_eq, isLUB_csSup, sne.image
-/
theorem map_csSup (hf : LeftOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddAbove s) :
    f (sSup s) = sSup (f '' s) :=
  ((hf sne <| isLUB_csSup sne sbdd).csSup_eq <| sne.image f).symm

@[to_dual]
/--
theorem `map_ciSup` / 定理 `map_ciSup`

English:
theorem map_ciSup
  given: (hf : LeftOrdContinuous f) {g : ι -> α} (hg : BddAbove (range g))
  proof: by
  simp only [iSup, hf.map_csSup (range_nonempty _) hg, ← range_comp]
  rfl

中文:
定理 map_ciSup
  条件: (hf : LeftOrdContinuous f) {g : ι -> α} (hg : BddAbove (range g))
  证明: by
  simp only [iSup, hf.map_csSup (range_nonempty _) hg, ← range_comp]
  rfl

Depends on / 依赖: hf.map_csSup, map_csSup, range_comp, range_nonempty
-/
theorem map_ciSup (hf : LeftOrdContinuous f) {g : ι -> α} (hg : BddAbove (range g)) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [iSup, hf.map_csSup (range_nonempty _) hg, ← range_comp]
  rfl

end ConditionallyCompleteLattice

end LeftOrdContinuous

namespace GaloisConnection
variable [Preorder α] [Preorder β] {f : α -> β} {g : β -> α}

/--
lemma `leftOrdContinuous` / 引理 `leftOrdContinuous`

English:
lemma leftOrdContinuous
  given: (gc : GaloisConnection f g)
  statement: LeftOrdContinuous f
  proof: fun _ _ _ => gc.isLUB_l_image

中文:
引理 leftOrdContinuous
  条件: (gc : GaloisConnection f g)
  结论: LeftOrdContinuous f
  证明: fun _ _ _ => gc.isLUB_l_image

Depends on / 依赖: gc.isLUB_l_image, isLUB_l_image
-/
lemma leftOrdContinuous (gc : GaloisConnection f g) : LeftOrdContinuous f :=
  fun _ _ _ => gc.isLUB_l_image

/--
lemma `rightOrdContinuous` / 引理 `rightOrdContinuous`

English:
lemma rightOrdContinuous
  given: (gc : GaloisConnection f g)
  statement: RightOrdContinuous g
  proof: fun _ _ _ => gc.isGLB_u_image

中文:
引理 rightOrdContinuous
  条件: (gc : GaloisConnection f g)
  结论: RightOrdContinuous g
  证明: fun _ _ _ => gc.isGLB_u_image

Depends on / 依赖: gc.isGLB_u_image, isGLB_u_image
-/
lemma rightOrdContinuous (gc : GaloisConnection f g) : RightOrdContinuous g :=
  fun _ _ _ => gc.isGLB_u_image

end GaloisConnection

namespace OrderIso
variable [Preorder α] [Preorder β] (e : α ≃o β)

/--
lemma `leftOrdContinuous` / 引理 `leftOrdContinuous`

English:
lemma leftOrdContinuous
  statement: LeftOrdContinuous e
  proof: e.to_galoisConnection.leftOrdContinuous

@[to_dual existing]

中文:
引理 leftOrdContinuous
  结论: LeftOrdContinuous e
  证明: e.to_galoisConnection.leftOrdContinuous

@[to_dual existing]
-/
protected lemma leftOrdContinuous : LeftOrdContinuous e := e.to_galoisConnection.leftOrdContinuous

@[to_dual existing]
/--
lemma `rightOrdContinuous` / 引理 `rightOrdContinuous`

English:
lemma rightOrdContinuous
  statement: RightOrdContinuous e
  proof: e.symm.to_galoisConnection.rightOrdContinuous

中文:
引理 rightOrdContinuous
  结论: RightOrdContinuous e
  证明: e.symm.to_galoisConnection.rightOrdContinuous
-/
protected lemma rightOrdContinuous : RightOrdContinuous e :=
  e.symm.to_galoisConnection.rightOrdContinuous

end OrderIso
