/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Infinite sums and products in topological groups

Lemmas on topological sums in groups (as opposed to monoids).
-/

public section

noncomputable section

open Filter Finset Function

open scoped Topology

variable {α β γ : Type*} {L : SummationFilter β}

section IsTopologicalGroup

variable [CommGroup α] [TopologicalSpace α] [IsTopologicalGroup α]
variable {f g : β -> α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
@[to_additive]
/--
theorem `HasProd.inv` / 定理 `HasProd.inv`

English:
theorem HasProd.inv
  given: (h : HasProd f a L)
  statement: HasProd (fun b => (f b)⁻¹) a⁻¹ L
  proof: by
  simpa only using! h.map (MonoidHom.id α)⁻¹ continuous_inv

@[to_additive]

中文:
定理 有积类型.inv
  条件: (h : 有积类型 f a L)
  结论: 有积类型 (fun b => (f b)⁻¹) a⁻¹ L
  证明: by
  simpa only using! h.map (MonoidHom.id α)⁻¹ continuous_inv

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.id, continuous_inv, h.map
-/
theorem HasProd.inv (h : HasProd f a L) : HasProd (fun b => (f b)⁻¹) a⁻¹ L := by
  simpa only using! h.map (MonoidHom.id α)⁻¹ continuous_inv

@[to_additive]
/--
theorem `Multipliable.inv` / 定理 `Multipliable.inv`

English:
theorem Multipliable.inv
  given: (hf : Multipliable f L)
  statement: Multipliable (fun b => (f b)⁻¹) L
  proof: hf.hasProd.inv.multipliable

@[to_additive]

中文:
定理 Multipliable.inv
  条件: (hf : Multipliable f L)
  结论: Multipliable (fun b => (f b)⁻¹) L
  证明: hf.hasProd.inv.multipliable

@[to_additive]

Depends on / 依赖: hasProd, hf.hasProd.inv.multipliable, multipliable
-/
theorem Multipliable.inv (hf : Multipliable f L) : Multipliable (fun b => (f b)⁻¹) L :=
  hf.hasProd.inv.multipliable

@[to_additive]
/--
theorem `Multipliable.of_inv` / 定理 `Multipliable.of_inv`

English:
theorem Multipliable.of_inv
  given: (hf : Multipliable (fun b => (f b)⁻¹) L)
  statement: Multipliable f L
  proof: by
  simpa only [inv_inv] using hf.inv

@[to_additive]

中文:
定理 Multipliable.of_inv
  条件: (hf : Multipliable (fun b => (f b)⁻¹) L)
  结论: Multipliable f L
  证明: by
  simpa only [inv_inv] using hf.inv

@[to_additive]

Depends on / 依赖: hf.inv, inv_inv
-/
theorem Multipliable.of_inv (hf : Multipliable (fun b => (f b)⁻¹) L) : Multipliable f L := by
  simpa only [inv_inv] using hf.inv

@[to_additive]
/--
theorem `multipliable_inv_iff` / 定理 `multipliable_inv_iff`

English:
theorem multipliable_inv_iff
  statement: (Multipliable (fun b => (f b)⁻¹) L) ↔ Multipliable f L
  proof: ⟨Multipliable.of_inv, Multipliable.inv⟩

@[to_additive]

中文:
定理 multipliable_inv_iff
  结论: (Multipliable (fun b => (f b)⁻¹) L) ↔ Multipliable f L
  证明: ⟨Multipliable.of_inv, Multipliable.inv⟩

@[to_additive]

Depends on / 依赖: Multipliable, Multipliable.inv, Multipliable.of_inv, of_inv
-/
theorem multipliable_inv_iff : (Multipliable (fun b => (f b)⁻¹) L) ↔ Multipliable f L :=
  ⟨Multipliable.of_inv, Multipliable.inv⟩

@[to_additive]
/--
theorem `HasProd.div` / 定理 `HasProd.div`

English:
theorem HasProd.div
  given: (hf : HasProd f a₁ L) (hg : HasProd g a₂ L)
  proof: by
  simp only [div_eq_mul_inv]
  exact hf.mul hg.inv

@[to_additive]

中文:
定理 有积类型.div
  条件: (hf : 有积类型 f a₁ L) (hg : 有积类型 g a₂ L)
  证明: by
  simp only [div_eq_mul_inv]
  exact hf.mul hg.inv

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
theorem HasProd.div (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) :
    HasProd (fun b => f b / g b) (a₁ / a₂) L := by
  simp only [div_eq_mul_inv]
  exact hf.mul hg.inv

@[to_additive]
/--
theorem `Multipliable.div` / 定理 `Multipliable.div`

English:
theorem Multipliable.div
  given: (hf : Multipliable f L) (hg : Multipliable g L)
  proof: (hf.hasProd.div hg.hasProd).multipliable

@[to_additive]

中文:
定理 Multipliable.div
  条件: (hf : Multipliable f L) (hg : Multipliable g L)
  证明: (hf.hasProd.div hg.hasProd).multipliable

@[to_additive]

Depends on / 依赖: hasProd, hf.hasProd.div, hg.hasProd, multipliable
-/
theorem Multipliable.div (hf : Multipliable f L) (hg : Multipliable g L) :
    Multipliable (fun b => f b / g b) L :=
  (hf.hasProd.div hg.hasProd).multipliable

@[to_additive]
/--
theorem `Multipliable.trans_div` / 定理 `Multipliable.trans_div`

English:
theorem Multipliable.trans_div
  given: (hg : Multipliable g L) (hfg : Multipliable (fun b => f b / g b) L)
  proof: by
  simpa only [div_mul_cancel] using hfg.mul hg

@[to_additive]

中文:
定理 Multipliable.trans_div
  条件: (hg : Multipliable g L) (hfg : Multipliable (fun b => f b / g b) L)
  证明: by
  simpa only [div_mul_cancel] using hfg.mul hg

@[to_additive]

Depends on / 依赖: div_mul_cancel, hfg.mul
-/
theorem Multipliable.trans_div (hg : Multipliable g L) (hfg : Multipliable (fun b => f b / g b) L) :
    Multipliable f L := by
  simpa only [div_mul_cancel] using hfg.mul hg

@[to_additive]
/--
theorem `multipliable_iff_of_multipliable_div` / 定理 `multipliable_iff_of_multipliable_div`

English:
theorem multipliable_iff_of_multipliable_div
  given: (hfg : Multipliable (fun b => f b / g b) L)
  proof: ⟨fun hf => hf.trans_div by simpa only [inv_div] using hfg.inv, fun hg => hg.trans_div hfg⟩

@[to_additive]

中文:
定理 multipliable_iff_of_multipliable_div
  条件: (hfg : Multipliable (fun b => f b / g b) L)
  证明: ⟨fun hf => hf.trans_div by simpa only [inv_div] using hfg.inv, fun hg => hg.trans_div hfg⟩

@[to_additive]

Depends on / 依赖: hf.trans_div, hfg.inv, hg.trans_div, inv_div, trans_div
-/
theorem multipliable_iff_of_multipliable_div (hfg : Multipliable (fun b => f b / g b) L) :
    Multipliable f L ↔ Multipliable g L :=
⟨fun hf => hf.trans_div by simpa only [inv_div] using hfg.inv, fun hg => hg.trans_div hfg⟩

@[to_additive]
/--
theorem `HasProd.update` / 定理 `HasProd.update`

English:
theorem HasProd.update
  given: [L.LeAtTop] (hf : HasProd f a₁ L) (b : β) [DecidableEq β] (a : α)
  proof: by
  convert! (hasProd_ite_eq b (a / f b) (L := L)).mul hf with b'
  by_cases h : b' = b
  · rw [h, update_self]
    simp
  · simp only [h, update_of_ne, if_false, Ne, one_mul, not_false_iff]

@[to_additive]

中文:
定理 有积类型.update
  条件: [L.LeAtTop] (hf : 有积类型 f a₁ L) (b : β) [DecidableEq β] (a : α)
  证明: by
  convert! (hasProd_ite_eq b (a / f b) (L := L)).mul hf with b'
  by_cases h : b' = b
  · rw [h, update_self]
    simp
  · simp only [h, update_of_ne, if_false, Ne, one_mul, not_false_iff]

@[to_additive]

Depends on / 依赖: convert, hasProd_ite_eq, if_false, not_false_iff, one_mul, update_of_ne, update_self
-/
theorem HasProd.update [L.LeAtTop] (hf : HasProd f a₁ L) (b : β) [DecidableEq β] (a : α) :
    HasProd (update f b a) (a / f b * a₁) L := by
  convert! (hasProd_ite_eq b (a / f b) (L := L)).mul hf with b'
  by_cases h : b' = b
  · rw [h, update_self]
    simp
  · simp only [h, update_of_ne, if_false, Ne, one_mul, not_false_iff]

@[to_additive]
/--
theorem `Multipliable.update` / 定理 `Multipliable.update`

English:
theorem Multipliable.update
  given: [L.LeAtTop] (hf : Multipliable f L) (b : β) [DecidableEq β] (a : α)
  proof: (hf.hasProd.update b a).multipliable

@[to_additive]

中文:
定理 Multipliable.update
  条件: [L.LeAtTop] (hf : Multipliable f L) (b : β) [DecidableEq β] (a : α)
  证明: (hf.hasProd.update b a).multipliable

@[to_additive]

Depends on / 依赖: hasProd, hf.hasProd.update, multipliable, update
-/
theorem Multipliable.update [L.LeAtTop] (hf : Multipliable f L) (b : β) [DecidableEq β] (a : α) :
    Multipliable (update f b a) L :=
  (hf.hasProd.update b a).multipliable

@[to_additive]
/--
theorem `HasProd.hasProd_compl_iff` / 定理 `HasProd.hasProd_compl_iff`

English:
theorem HasProd.hasProd_compl_iff
  given: {s : Set β} (hf : HasProd (f ∘ (↑) : s -> α) a₁)
  proof: by
  refine ⟨fun h => hf.mul_compl h, fun h => ?_⟩
  rw [hasProd_subtype_iff_mulIndicator] at hf ⊢
  rw [Set.mulIndicator_compl]
  simpa only [div_eq_mul_inv, mul_inv_cancel_comm] using! h.div hf

@[to_additive]

中文:
定理 有积类型.hasProd_compl_iff
  条件: {s : 集合 β} (hf : 有积类型 (f ∘ (↑) : s -> α) a₁)
  证明: by
  refine ⟨fun h => hf.mul_compl h, fun h => ?_⟩
  rw [hasProd_subtype_iff_mulIndicator] at hf ⊢
  rw [Set.mulIndicator_compl]
  simpa only [div_eq_mul_inv, mul_inv_cancel_comm] using! h.div hf

@[to_additive]

Depends on / 依赖: Set.mulIndicator_compl, div_eq_mul_inv, h.div, hasProd_subtype_iff_mulIndicator, hf.mul_compl, mulIndicator_compl, mul_compl, mul_inv_cancel_comm
-/
theorem HasProd.hasProd_compl_iff {s : Set β} (hf : HasProd (f ∘ (↑) : s -> α) a₁) :
    HasProd (f ∘ (↑) : ↑sᶜ -> α) a₂ ↔ HasProd f (a₁ * a₂) := by
  refine ⟨fun h => hf.mul_compl h, fun h => ?_⟩
  rw [hasProd_subtype_iff_mulIndicator] at hf ⊢
  rw [Set.mulIndicator_compl]
  simpa only [div_eq_mul_inv, mul_inv_cancel_comm] using! h.div hf

@[to_additive]
/--
theorem `HasProd.hasProd_iff_compl` / 定理 `HasProd.hasProd_iff_compl`

English:
theorem HasProd.hasProd_iff_compl
  given: {s : Set β} (hf : HasProd (f ∘ (↑) : s -> α) a₁)
  proof: Iff.symm hf.hasProd_compl_iff.trans by rw [mul_div_cancel]

@[to_additive]

中文:
定理 有积类型.hasProd_iff_compl
  条件: {s : 集合 β} (hf : 有积类型 (f ∘ (↑) : s -> α) a₁)
  证明: Iff.symm hf.hasProd_compl_iff.trans by rw [mul_div_cancel]

@[to_additive]

Depends on / 依赖: Iff.symm, hasProd_compl_iff, hf.hasProd_compl_iff.trans, mul_div_cancel
-/
theorem HasProd.hasProd_iff_compl {s : Set β} (hf : HasProd (f ∘ (↑) : s -> α) a₁) :
    HasProd f a₂ ↔ HasProd (f ∘ (↑) : ↑sᶜ -> α) (a₂ / a₁) :=
Iff.symm hf.hasProd_compl_iff.trans by rw [mul_div_cancel]

@[to_additive]
/--
theorem `Multipliable.multipliable_compl_iff` / 定理 `Multipliable.multipliable_compl_iff`

English:
theorem Multipliable.multipliable_compl_iff
  given: {s : Set β} (hf : Multipliable (f ∘ (↑) : s -> α))
  proof: fun ⟨_, ha⟩ => (hf.hasProd.hasProd_compl_iff.1 ha).multipliable
  mpr := fun ⟨_, ha⟩ => (hf.hasProd.hasProd_iff_compl.1 ha).multipliable

@[to_additive]

中文:
定理 Multipliable.multipliable_compl_iff
  条件: {s : 集合 β} (hf : Multipliable (f ∘ (↑) : s -> α))
  证明: fun ⟨_, ha⟩ => (hf.hasProd.hasProd_compl_iff.1 ha).multipliable
  mpr := fun ⟨_, ha⟩ => (hf.hasProd.hasProd_iff_compl.1 ha).multipliable

@[to_additive]

Depends on / 依赖: hasProd, hasProd_compl_iff, hf.hasProd.hasProd_compl_iff, multipliable
-/
theorem Multipliable.multipliable_compl_iff {s : Set β} (hf : Multipliable (f ∘ (↑) : s -> α)) :
    Multipliable (f ∘ (↑) : ↑sᶜ -> α) ↔ Multipliable f where
  mp := fun ⟨_, ha⟩ => (hf.hasProd.hasProd_compl_iff.1 ha).multipliable
  mpr := fun ⟨_, ha⟩ => (hf.hasProd.hasProd_iff_compl.1 ha).multipliable

@[to_additive]
/--
theorem `Finset.hasProd_compl_iff` / 定理 `Finset.hasProd_compl_iff`

English:
theorem Finset.hasProd_compl_iff
  given: (s : Finset β)
  proof: (s.hasProd f).hasProd_compl_iff.trans by rw [mul_comm]

@[to_additive]

中文:
定理 有限集.hasProd_compl_iff
  条件: (s : 有限集 β)
  证明: (s.hasProd f).hasProd_compl_iff.trans by rw [mul_comm]

@[to_additive]
-/
protected theorem Finset.hasProd_compl_iff (s : Finset β) :
    HasProd (fun x : { x // x ∉ s } => f x) a ↔ HasProd f (a * ∏ i in s, f i) :=
(s.hasProd f).hasProd_compl_iff.trans by rw [mul_comm]

@[to_additive]
/--
theorem `Finset.hasProd_iff_compl` / 定理 `Finset.hasProd_iff_compl`

English:
theorem Finset.hasProd_iff_compl
  given: (s : Finset β)
  proof: (s.hasProd f).hasProd_iff_compl

@[to_additive]

中文:
定理 有限集.hasProd_iff_compl
  条件: (s : 有限集 β)
  证明: (s.hasProd f).hasProd_iff_compl

@[to_additive]
-/
protected theorem Finset.hasProd_iff_compl (s : Finset β) :
    HasProd f a ↔ HasProd (fun x : { x // x ∉ s } => f x) (a / ∏ i in s, f i) :=
  (s.hasProd f).hasProd_iff_compl

@[to_additive]
/--
theorem `Finset.multipliable_compl_iff` / 定理 `Finset.multipliable_compl_iff`

English:
theorem Finset.multipliable_compl_iff
  given: (s : Finset β)
  proof: (s.multipliable f).multipliable_compl_iff

@[to_additive]

中文:
定理 有限集.multipliable_compl_iff
  条件: (s : 有限集 β)
  证明: (s.multipliable f).multipliable_compl_iff

@[to_additive]
-/
protected theorem Finset.multipliable_compl_iff (s : Finset β) :
    (Multipliable fun x : { x // x ∉ s } => f x) ↔ Multipliable f :=
  (s.multipliable f).multipliable_compl_iff

@[to_additive]
/--
theorem `Set.Finite.multipliable_compl_iff` / 定理 `Set.Finite.multipliable_compl_iff`

English:
theorem Set.Finite.multipliable_compl_iff
  given: {s : Set β} (hs : s.Finite)
  proof: (hs.multipliable f).multipliable_compl_iff

@[to_additive]

中文:
定理 集合.有限.multipliable_compl_iff
  条件: {s : 集合 β} (hs : s.有限)
  证明: (hs.multipliable f).multipliable_compl_iff

@[to_additive]

Depends on / 依赖: hs.multipliable, multipliable, multipliable_compl_iff
-/
theorem Set.Finite.multipliable_compl_iff {s : Set β} (hs : s.Finite) :
    Multipliable (f ∘ (↑) : ↑sᶜ -> α) ↔ Multipliable f :=
  (hs.multipliable f).multipliable_compl_iff

@[to_additive]
/--
theorem `hasProd_ite_div_hasProd` / 定理 `hasProd_ite_div_hasProd`

English:
theorem hasProd_ite_div_hasProd
  given: [L.LeAtTop] [DecidableEq β] (hf : HasProd f a L) (b : β)
  proof: by
  convert! hf.update b 1 using 1
  · ext n
    rw [Function.update_apply]
  · rw [div_mul_eq_mul_div, one_mul]

中文:
定理 hasProd_ite_div_hasProd
  条件: [L.LeAtTop] [DecidableEq β] (hf : 有积类型 f a L) (b : β)
  证明: by
  convert! hf.update b 1 using 1
  · ext n
    rw [Function.update_apply]
  · rw [div_mul_eq_mul_div, one_mul]

Depends on / 依赖: Function, Function.update_apply, convert, div_mul_eq_mul_div, hf.update, one_mul, update, update_apply
-/
theorem hasProd_ite_div_hasProd [L.LeAtTop] [DecidableEq β] (hf : HasProd f a L) (b : β) :
    HasProd (fun n => ite (n = b) 1 (f n)) (a / f b) L := by
  convert! hf.update b 1 using 1
  · ext n
    rw [Function.update_apply]
  · rw [div_mul_eq_mul_div, one_mul]

/-- A more general version of `Multipliable.congr`, allowing the functions to
disagree on a finite set.

Note that this requires the target to be a group, and hence fails for products valued
in a ring. See `Multipliable.congr_cofinite₀` for a version applying in this case,
with an additional non-vanishing hypothesis.
-/
@[to_additive /-- A more general version of `Summable.congr`, allowing the functions to
disagree on a finite set. -/]
/--
theorem `Multipliable.congr_cofinite` / 定理 `Multipliable.congr_cofinite`

English:
theorem Multipliable.congr_cofinite
  given: (hf : Multipliable f) (hfg : f =ᶠ[cofinite] g)
  proof: hfg.multipliable_compl_iff.mp (hfg.multipliable_compl_iff.mpr hf).congr (by simp)

中文:
定理 Multipliable.congr_cofinite
  条件: (hf : Multipliable f) (hfg : f =ᶠ[cofinite] g)
  证明: hfg.multipliable_compl_iff.mp (hfg.multipliable_compl_iff.mpr hf).congr (by simp)

Depends on / 依赖: hfg.multipliable_compl_iff.mp, hfg.multipliable_compl_iff.mpr, multipliable_compl_iff
-/
theorem Multipliable.congr_cofinite (hf : Multipliable f) (hfg : f =ᶠ[cofinite] g) :
    Multipliable g :=
hfg.multipliable_compl_iff.mp (hfg.multipliable_compl_iff.mpr hf).congr (by simp)

/-- A more general version of `multipliable_congr`, allowing the functions to
disagree on a finite set. -/
@[to_additive /-- A more general version of `summable_congr`, allowing the functions to
disagree on a finite set. -/]
/--
theorem `multipliable_congr_cofinite` / 定理 `multipliable_congr_cofinite`

English:
theorem multipliable_congr_cofinite
  given: (hfg : f =ᶠ[cofinite] g)
  proof: ⟨fun h => h.congr_cofinite hfg, fun h => h.congr_cofinite (hfg.mono fun _ h' => h'.symm)⟩

@[to_additive]

中文:
定理 multipliable_congr_cofinite
  条件: (hfg : f =ᶠ[cofinite] g)
  证明: ⟨fun h => h.congr_cofinite hfg, fun h => h.congr_cofinite (hfg.mono fun _ h' => h'.symm)⟩

@[to_additive]

Depends on / 依赖: congr_cofinite, h.congr_cofinite, hfg.mono
-/
theorem multipliable_congr_cofinite (hfg : f =ᶠ[cofinite] g) :
    Multipliable f ↔ Multipliable g :=
  ⟨fun h => h.congr_cofinite hfg, fun h => h.congr_cofinite (hfg.mono fun _ h' => h'.symm)⟩

@[to_additive]
/--
theorem `Multipliable.congr_atTop` / 定理 `Multipliable.congr_atTop`

English:
theorem Multipliable.congr_atTop
  given: {f₁ g₁ : Nat -> α} (hf : Multipliable f₁) (hfg : f₁ =ᶠ[atTop] g₁)
  proof: hf.congr_cofinite (Nat.cofinite_eq_atTop ▸ hfg)

@[to_additive]

中文:
定理 Multipliable.congr_atTop
  条件: {f₁ g₁ : 自然数 -> α} (hf : Multipliable f₁) (hfg : f₁ =ᶠ[atTop] g₁)
  证明: hf.congr_cofinite (Nat.cofinite_eq_atTop ▸ hfg)

@[to_additive]

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, congr_cofinite, hf.congr_cofinite
-/
theorem Multipliable.congr_atTop {f₁ g₁ : Nat -> α} (hf : Multipliable f₁) (hfg : f₁ =ᶠ[atTop] g₁) :
    Multipliable g₁ := hf.congr_cofinite (Nat.cofinite_eq_atTop ▸ hfg)

@[to_additive]
/--
theorem `multipliable_congr_atTop` / 定理 `multipliable_congr_atTop`

English:
theorem multipliable_congr_atTop
  given: {f₁ g₁ : Nat -> α} (hfg : f₁ =ᶠ[atTop] g₁)
  proof: multipliable_congr_cofinite (Nat.cofinite_eq_atTop ▸ hfg)

中文:
定理 multipliable_congr_atTop
  条件: {f₁ g₁ : 自然数 -> α} (hfg : f₁ =ᶠ[atTop] g₁)
  证明: multipliable_congr_cofinite (Nat.cofinite_eq_atTop ▸ hfg)

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, multipliable_congr_cofinite
-/
theorem multipliable_congr_atTop {f₁ g₁ : Nat -> α} (hfg : f₁ =ᶠ[atTop] g₁) :
    Multipliable f₁ ↔ Multipliable g₁ := multipliable_congr_cofinite (Nat.cofinite_eq_atTop ▸ hfg)

section tprod

variable [T2Space α]

@[to_additive]
/--
theorem `tprod_inv` / 定理 `tprod_inv`

English:
theorem tprod_inv
  statement: ∏'[L] b, (f b)⁻¹ = (∏'[L] b, f b)⁻¹
  proof: ((Homeomorph.inv α).isClosedEmbedding.map_tprod f (g := MulEquiv.inv α)).symm

@[to_additive]

中文:
定理 tprod_inv
  结论: ∏'[L] b, (f b)⁻¹ = (∏'[L] b, f b)⁻¹
  证明: ((Homeomorph.inv α).isClosedEmbedding.map_tprod f (g := MulEquiv.inv α)).symm

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.inv, MulEquiv, MulEquiv.inv, isClosedEmbedding, isClosedEmbedding.map_tprod, map_tprod
-/
theorem tprod_inv : ∏'[L] b, (f b)⁻¹ = (∏'[L] b, f b)⁻¹ :=
  ((Homeomorph.inv α).isClosedEmbedding.map_tprod f (g := MulEquiv.inv α)).symm

@[to_additive]
/--
theorem `Multipliable.tprod_div` / 定理 `Multipliable.tprod_div`

English:
theorem Multipliable.tprod_div
  given: [L.NeBot] (hf : Multipliable f L) (hg : Multipliable g L)
  proof: (hf.hasProd.div hg.hasProd).tprod_eq

@[to_additive]

中文:
定理 Multipliable.tprod_div
  条件: [L.NeBot] (hf : Multipliable f L) (hg : Multipliable g L)
  证明: (hf.hasProd.div hg.hasProd).tprod_eq

@[to_additive]
-/
protected theorem Multipliable.tprod_div [L.NeBot] (hf : Multipliable f L) (hg : Multipliable g L) :
    ∏'[L] b, (f b / g b) = (∏'[L] b, f b) / ∏'[L] b, g b :=
  (hf.hasProd.div hg.hasProd).tprod_eq

@[to_additive]
/--
theorem `Multipliable.prod_mul_tprod_compl` / 定理 `Multipliable.prod_mul_tprod_compl`

English:
theorem Multipliable.prod_mul_tprod_compl
  given: {s : Finset β} (hf : Multipliable f)
  proof: ((s.hasProd f).mul_compl (s.multipliable_compl_iff.2 hf).hasProd).tprod_eq.symm

中文:
定理 Multipliable.prod_mul_tprod_compl
  条件: {s : 有限集 β} (hf : Multipliable f)
  证明: ((s.hasProd f).mul_compl (s.multipliable_compl_iff.2 hf).hasProd).tprod_eq.symm
-/
protected theorem Multipliable.prod_mul_tprod_compl {s : Finset β} (hf : Multipliable f) :
    (∏ x in s, f x) * ∏' x : ↑(s : Set β)ᶜ, f x = ∏' x, f x :=
  ((s.hasProd f).mul_compl (s.multipliable_compl_iff.2 hf).hasProd).tprod_eq.symm

/-- Let `f : β → α` be a multipliable function and let `b ∈ β` be an index.
Lemma `tprod_eq_mul_tprod_ite` writes `∏ n, f n` as `f b` times the product of the
remaining terms. -/
@[to_additive /-- Let `f : β → α` be a summable function and let `b ∈ β` be an index.
Lemma `tsum_eq_add_tsum_ite` writes `Σ' n, f n` as `f b` plus the sum of the
remaining terms. -/]
/--
theorem `Multipliable.tprod_eq_mul_tprod_ite` / 定理 `Multipliable.tprod_eq_mul_tprod_ite`

English:
theorem Multipliable.tprod_eq_mul_tprod_ite
  statement: [DecidableEq β] (hf : Multipliable f)
  proof: by
  rw [(hasProd_ite_div_hasProd hf.hasProd b).tprod_eq]
  exact (mul_div_cancel _ _).symm

中文:
定理 Multipliable.tprod_eq_mul_tprod_ite
  结论: [DecidableEq β] (hf : Multipliable f)
  证明: by
  rw [(hasProd_ite_div_hasProd hf.hasProd b).tprod_eq]
  exact (mul_div_cancel _ _).symm
-/
protected theorem Multipliable.tprod_eq_mul_tprod_ite [DecidableEq β] (hf : Multipliable f)
    (b : β) : ∏' n, f n = f b * ∏' n, ite (n = b) 1 (f n) := by
  rw [(hasProd_ite_div_hasProd hf.hasProd b).tprod_eq]
  exact (mul_div_cancel _ _).symm

end tprod

end IsTopologicalGroup

section IsUniformGroup

variable [UniformSpace α]

/-- The **Cauchy criterion** for infinite products, also known as the **Cauchy convergence test** -/
@[to_additive /-- The **Cauchy criterion** for infinite sums, also known as the
**Cauchy convergence test** -/]
/--
theorem `multipliable_iff_cauchySeq_finset` / 定理 `multipliable_iff_cauchySeq_finset`

English:
theorem multipliable_iff_cauchySeq_finset
  given: [CommMonoid α] [CompleteSpace α] {f : β -> α}
  proof: by
  exact cauchy_map_iff_exists_tendsto.symm

中文:
定理 multipliable_iff_cauchySeq_finset
  条件: [交换幺半群 α] [完备空间 α] {f : β -> α}
  证明: by
  exact cauchy_map_iff_exists_tendsto.symm

Depends on / 依赖: cauchy_map_iff_exists_tendsto, cauchy_map_iff_exists_tendsto.symm
-/
theorem multipliable_iff_cauchySeq_finset [CommMonoid α] [CompleteSpace α] {f : β -> α} :
    Multipliable f ↔ CauchySeq fun s : Finset β => ∏ b in s, f b := by
  exact cauchy_map_iff_exists_tendsto.symm

variable [CommGroup α] [IsUniformGroup α] {f g : β -> α}

@[to_additive]
/--
theorem `cauchySeq_finset_iff_prod_vanishing` / 定理 `cauchySeq_finset_iff_prod_vanishing`

English:
theorem cauchySeq_finset_iff_prod_vanishing
  proof: by
  classical
  simp only [CauchySeq, cauchy_map_iff, prod_atTop_atTop_eq,
    uniformity_eq_comap_nhds_one α, tendsto_comap_iff, Function.comp_def, atTop_neBot, true_and]
  rw [tendsto_atTop']
  constructor
  · intro h e he
    obtain ⟨⟨s₁, s₂⟩, h⟩ := h e he
    use s₁ union s₂
    intro t ht
    specialize h (s₁ union s₂, s₁ union s₂ union t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
    simpa only [Finset.prod_union ht.symm, mul_div_cancel_left] using h
  · rintro h e he
    rcases exists_nhds_split_inv he with ⟨d, hd, hde⟩
    rcases h d hd with ⟨s, h⟩
    use (s, s)
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
    have : ((∏ b in t₂, f b) / ∏ b in t₁, f b) = (∏ b in t₂ \ s, f b) / ∏ b in t₁ \ s, f b := by
      rw [← Finset.prod_sdiff ht₁]; rw [← Finset.prod_sdiff ht₂]; rw [mul_div_mul_right_eq_div]
    simp only [this]
    exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)

@[to_additive]

中文:
定理 cauchySeq_finset_iff_prod_vanishing
  证明: by
  classical
  simp only [CauchySeq, cauchy_map_iff, prod_atTop_atTop_eq,
    uniformity_eq_comap_nhds_one α, tendsto_comap_iff, Function.comp_def, atTop_neBot, true_and]
  rw [tendsto_atTop']
  constructor
  · intro h e he
    obtain ⟨⟨s₁, s₂⟩, h⟩ := h e he
    use s₁ union s₂
    intro t ht
    specialize h (s₁ union s₂, s₁ union s₂ union t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
    simpa only [Finset.prod_union ht.symm, mul_div_cancel_left] using h
  · rintro h e he
    rcases exists_nhds_split_inv he with ⟨d, hd, hde⟩
    rcases h d hd with ⟨s, h⟩
    use (s, s)
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
    have : ((∏ b in t₂, f b) / ∏ b in t₁, f b) = (∏ b in t₂ \ s, f b) / ∏ b in t₁ \ s, f b := by
      rw [← Finset.prod_sdiff ht₁]; rw [← Finset.prod_sdiff ht₂]; rw [mul_div_mul_right_eq_div]
    simp only [this]
    exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)

@[to_additive]

Depends on / 依赖: CauchySeq, Finset, Finset.prod_union, Function, Function.comp_def, atTop_neBot, cauchy_map_iff, classical, comp_def, exists_nhds_split_inv, ht.symm, le_sup_left, le_sup_of_le_left, le_sup_right, mul_div_cancel_left, prod_atTop_atTop_eq, prod_union, specialize, tendsto_atTop, tendsto_comap_iff
-/
theorem cauchySeq_finset_iff_prod_vanishing :
    (CauchySeq fun s : Finset β => ∏ b in s, f b) ↔
      forall e in 𝓝 (1 : α), exists s : Finset β, forall t, Disjoint t s -> (∏ b in t, f b) in e := by
  classical
  simp only [CauchySeq, cauchy_map_iff, prod_atTop_atTop_eq,
    uniformity_eq_comap_nhds_one α, tendsto_comap_iff, Function.comp_def, atTop_neBot, true_and]
  rw [tendsto_atTop']
  constructor
  · intro h e he
    obtain ⟨⟨s₁, s₂⟩, h⟩ := h e he
    use s₁ union s₂
    intro t ht
    specialize h (s₁ union s₂, s₁ union s₂ union t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
    simpa only [Finset.prod_union ht.symm, mul_div_cancel_left] using h
  · rintro h e he
    rcases exists_nhds_split_inv he with ⟨d, hd, hde⟩
    rcases h d hd with ⟨s, h⟩
    use (s, s)
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
    have : ((∏ b in t₂, f b) / ∏ b in t₁, f b) = (∏ b in t₂ \ s, f b) / ∏ b in t₁ \ s, f b := by
      rw [← Finset.prod_sdiff ht₁]; rw [← Finset.prod_sdiff ht₂]; rw [mul_div_mul_right_eq_div]
    simp only [this]
    exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)

@[to_additive]
/--
theorem `cauchySeq_finset_iff_tprod_vanishing` / 定理 `cauchySeq_finset_iff_tprod_vanishing`

English:
theorem cauchySeq_finset_iff_tprod_vanishing
  proof: by
  simp_rw [cauchySeq_finset_iff_prod_vanishing, Set.disjoint_left, disjoint_left]
  refine ⟨fun vanish e he => ?_, fun vanish e he => ?_⟩
  · obtain ⟨o, ho, o_closed, oe⟩ := exists_mem_nhds_isClosed_subset he
    obtain ⟨s, hs⟩ := vanish o ho
    refine ⟨s, fun t hts => oe ?_⟩
    by_cases ht : Multipliable fun a : t => f a
    · classical
      refine o_closed.mem_of_tendsto ht.hasProd (Eventually.of_forall fun t' => ?_)
      rw [← prod_subtype_map_embedding fun _ _ => by rfl]
      apply hs
      simp_rw [Finset.mem_map]
      rintro _ ⟨b, -, rfl⟩
      exact hts b.prop
    · exact tprod_eq_one_of_not_multipliable ht ▸ mem_of_mem_nhds ho
  · obtain ⟨s, hs⟩ := vanish _ he
    exact ⟨s, fun t hts => (t.tprod_subtype f).symm ▸ hs _ hts⟩

中文:
定理 cauchySeq_finset_iff_tprod_vanishing
  证明: by
  simp_rw [cauchySeq_finset_iff_prod_vanishing, Set.disjoint_left, disjoint_left]
  refine ⟨fun vanish e he => ?_, fun vanish e he => ?_⟩
  · obtain ⟨o, ho, o_closed, oe⟩ := exists_mem_nhds_isClosed_subset he
    obtain ⟨s, hs⟩ := vanish o ho
    refine ⟨s, fun t hts => oe ?_⟩
    by_cases ht : Multipliable fun a : t => f a
    · classical
      refine o_closed.mem_of_tendsto ht.hasProd (Eventually.of_forall fun t' => ?_)
      rw [← prod_subtype_map_embedding fun _ _ => by rfl]
      apply hs
      simp_rw [Finset.mem_map]
      rintro _ ⟨b, -, rfl⟩
      exact hts b.prop
    · exact tprod_eq_one_of_not_multipliable ht ▸ mem_of_mem_nhds ho
  · obtain ⟨s, hs⟩ := vanish _ he
    exact ⟨s, fun t hts => (t.tprod_subtype f).symm ▸ hs _ hts⟩

Depends on / 依赖: Eventually, Eventually.of_forall, Finset, Finset.mem_map, Multipliable, Set.disjoint_left, cauchySeq_finset_iff_prod_vanishing, classical, disjoint_left, exists_mem_nhds_isClosed_subset, hasProd, ht.hasProd, mem_map, mem_of_tendsto, o_closed, o_closed.mem_of_tendsto, of_forall, prod_subtype_map_embedding, simp_rw, vanish
-/
theorem cauchySeq_finset_iff_tprod_vanishing :
    (CauchySeq fun s : Finset β => ∏ b in s, f b) ↔
      forall e in 𝓝 (1 : α), exists s : Finset β, forall t : Set β, Disjoint t s -> (∏' b : t, f b) in e := by
  simp_rw [cauchySeq_finset_iff_prod_vanishing, Set.disjoint_left, disjoint_left]
  refine ⟨fun vanish e he => ?_, fun vanish e he => ?_⟩
  · obtain ⟨o, ho, o_closed, oe⟩ := exists_mem_nhds_isClosed_subset he
    obtain ⟨s, hs⟩ := vanish o ho
    refine ⟨s, fun t hts => oe ?_⟩
    by_cases ht : Multipliable fun a : t => f a
    · classical
      refine o_closed.mem_of_tendsto ht.hasProd (Eventually.of_forall fun t' => ?_)
      rw [← prod_subtype_map_embedding fun _ _ => by rfl]
      apply hs
      simp_rw [Finset.mem_map]
      rintro _ ⟨b, -, rfl⟩
      exact hts b.prop
    · exact tprod_eq_one_of_not_multipliable ht ▸ mem_of_mem_nhds ho
  · obtain ⟨s, hs⟩ := vanish _ he
    exact ⟨s, fun t hts => (t.tprod_subtype f).symm ▸ hs _ hts⟩

variable [CompleteSpace α]

@[to_additive]
/--
theorem `multipliable_iff_vanishing` / 定理 `multipliable_iff_vanishing`

English:
theorem multipliable_iff_vanishing
  proof: by
  rw [multipliable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_prod_vanishing]

@[to_additive]

中文:
定理 multipliable_iff_vanishing
  证明: by
  rw [multipliable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_prod_vanishing]

@[to_additive]

Depends on / 依赖: cauchySeq_finset_iff_prod_vanishing, multipliable_iff_cauchySeq_finset
-/
theorem multipliable_iff_vanishing :
    Multipliable f ↔
    forall e in 𝓝 (1 : α), exists s : Finset β, forall t, Disjoint t s -> (∏ b in t, f b) in e := by
  rw [multipliable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_prod_vanishing]

@[to_additive]
/--
theorem `multipliable_iff_tprod_vanishing` / 定理 `multipliable_iff_tprod_vanishing`

English:
theorem multipliable_iff_tprod_vanishing
  statement: Multipliable f ↔
  proof: by
  rw [multipliable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_tprod_vanishing]

中文:
定理 multipliable_iff_tprod_vanishing
  结论: Multipliable f ↔
  证明: by
  rw [multipliable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_tprod_vanishing]

Depends on / 依赖: cauchySeq_finset_iff_tprod_vanishing, multipliable_iff_cauchySeq_finset
-/
theorem multipliable_iff_tprod_vanishing : Multipliable f ↔
    forall e in 𝓝 (1 : α), exists s : Finset β, forall t : Set β, Disjoint t s -> (∏' b : t, f b) in e := by
  rw [multipliable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_tprod_vanishing]

-- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a`
@[to_additive]
/--
theorem `Multipliable.multipliable_of_eq_one_or_self` / 定理 `Multipliable.multipliable_of_eq_one_or_self`

English:
theorem Multipliable.multipliable_of_eq_one_or_self
  statement: (hf : Multipliable f)
  proof: by
  classical
  exact multipliable_iff_vanishing.2 fun e he =>
    let ⟨s, hs⟩ := multipliable_iff_vanishing.1 hf e he
    ⟨s, fun t ht =>
      have eq : ∏ b in t with g b = f b, f b = ∏ b in t, g b :=
        calc
          ∏ b in t with g b = f b, f b = ∏ b in t with g b = f b, g b :=
            Finset.prod_congr rfl fun b hb => (Finset.mem_filter.1 hb).2.symm
          _ = ∏ b in t, g b := by
           {refine Finset.prod_subset (Finset.filter_subset _ _) ?_
            intro b hbt hb
            simp only [Finset.mem_filter, and_iff_right hbt] at hb
            exact (h b).resolve_right hb}
eq ▸ hs _ Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩

@[to_additive]

中文:
定理 Multipliable.multipliable_of_eq_one_or_self
  结论: (hf : Multipliable f)
  证明: by
  classical
  exact multipliable_iff_vanishing.2 fun e he =>
    let ⟨s, hs⟩ := multipliable_iff_vanishing.1 hf e he
    ⟨s, fun t ht =>
      have eq : ∏ b in t with g b = f b, f b = ∏ b in t, g b :=
        calc
          ∏ b in t with g b = f b, f b = ∏ b in t with g b = f b, g b :=
            Finset.prod_congr rfl fun b hb => (Finset.mem_filter.1 hb).2.symm
          _ = ∏ b in t, g b := by
           {refine Finset.prod_subset (Finset.filter_subset _ _) ?_
            intro b hbt hb
            simp only [Finset.mem_filter, and_iff_right hbt] at hb
            exact (h b).resolve_right hb}
eq ▸ hs _ Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩

@[to_additive]

Depends on / 依赖: Finset, Finset.filter_subset, Finset.mem_filter, Finset.prod_congr, Finset.prod_subset, and_iff_right, classical, filter_subset, mem_filter, multipliable_iff_vanishing, prod_congr, prod_subset, resolve_right
-/
theorem Multipliable.multipliable_of_eq_one_or_self (hf : Multipliable f)
    (h : forall b, g b = 1 ∨ g b = f b) : Multipliable g := by
  classical
  exact multipliable_iff_vanishing.2 fun e he =>
    let ⟨s, hs⟩ := multipliable_iff_vanishing.1 hf e he
    ⟨s, fun t ht =>
      have eq : ∏ b in t with g b = f b, f b = ∏ b in t, g b :=
        calc
          ∏ b in t with g b = f b, f b = ∏ b in t with g b = f b, g b :=
            Finset.prod_congr rfl fun b hb => (Finset.mem_filter.1 hb).2.symm
          _ = ∏ b in t, g b := by
           {refine Finset.prod_subset (Finset.filter_subset _ _) ?_
            intro b hbt hb
            simp only [Finset.mem_filter, and_iff_right hbt] at hb
            exact (h b).resolve_right hb}
eq ▸ hs _ Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩

@[to_additive]
/--
theorem `Multipliable.mulIndicator` / 定理 `Multipliable.mulIndicator`

English:
theorem Multipliable.mulIndicator
  given: (hf : Multipliable f) (s : Set β)
  proof: hf.multipliable_of_eq_one_or_self Set.mulIndicator_eq_one_or_self _ _

@[to_additive]

中文:
定理 Multipliable.mulIndicator
  条件: (hf : Multipliable f) (s : 集合 β)
  证明: hf.multipliable_of_eq_one_or_self Set.mulIndicator_eq_one_or_self _ _

@[to_additive]
-/
protected theorem Multipliable.mulIndicator (hf : Multipliable f) (s : Set β) :
    Multipliable (s.mulIndicator f) :=
hf.multipliable_of_eq_one_or_self Set.mulIndicator_eq_one_or_self _ _

@[to_additive]
/--
theorem `Multipliable.comp_injective` / 定理 `Multipliable.comp_injective`

English:
theorem Multipliable.comp_injective
  given: {i : γ -> β} (hf : Multipliable f) (hi : Injective i)
  proof: by
  simpa only [Set.mulIndicator_range_comp] using
    (hi.multipliable_iff (fun x hx => Set.mulIndicator_of_notMem hx _)).2
    (hf.mulIndicator (Set.range i))

@[to_additive]

中文:
定理 Multipliable.comp_injective
  条件: {i : γ -> β} (hf : Multipliable f) (hi : 单射 i)
  证明: by
  simpa only [Set.mulIndicator_range_comp] using
    (hi.multipliable_iff (fun x hx => Set.mulIndicator_of_notMem hx _)).2
    (hf.mulIndicator (Set.range i))

@[to_additive]

Depends on / 依赖: Set.mulIndicator_of_notMem, Set.mulIndicator_range_comp, Set.range, hf.mulIndicator, hi.multipliable_iff, mulIndicator, mulIndicator_of_notMem, mulIndicator_range_comp, multipliable_iff
-/
theorem Multipliable.comp_injective {i : γ -> β} (hf : Multipliable f) (hi : Injective i) :
    Multipliable (f ∘ i) := by
  simpa only [Set.mulIndicator_range_comp] using
    (hi.multipliable_iff (fun x hx => Set.mulIndicator_of_notMem hx _)).2
    (hf.mulIndicator (Set.range i))

@[to_additive]
/--
theorem `Multipliable.subtype` / 定理 `Multipliable.subtype`

English:
theorem Multipliable.subtype
  given: (hf : Multipliable f) (p : β -> Prop)
  proof: hf.comp_injective Subtype.coe_injective

@[to_additive]

中文:
定理 Multipliable.subtype
  条件: (hf : Multipliable f) (p : β -> 命题)
  证明: hf.comp_injective Subtype.coe_injective

@[to_additive]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, comp_injective, hf.comp_injective
-/
theorem Multipliable.subtype (hf : Multipliable f) (p : β -> Prop) :
    Multipliable (f ∘ (↑) : Subtype p -> α) :=
  hf.comp_injective Subtype.coe_injective

@[to_additive]
/--
theorem `multipliable_subtype_and_compl` / 定理 `multipliable_subtype_and_compl`

English:
theorem multipliable_subtype_and_compl
  given: {s : Set β}
  proof: ⟨and_imp.2 Multipliable.mul_compl, fun h => ⟨h.subtype (· in s), h.subtype (· in sᶜ)⟩⟩

@[to_additive]

中文:
定理 multipliable_subtype_and_compl
  条件: {s : 集合 β}
  证明: ⟨and_imp.2 Multipliable.mul_compl, fun h => ⟨h.subtype (· in s), h.subtype (· in sᶜ)⟩⟩

@[to_additive]

Depends on / 依赖: Multipliable, Multipliable.mul_compl, and_imp, h.subtype, mul_compl, subtype
-/
theorem multipliable_subtype_and_compl {s : Set β} :
    ((Multipliable fun x : s => f x) ∧ Multipliable fun x : ↑sᶜ => f x) ↔ Multipliable f :=
  ⟨and_imp.2 Multipliable.mul_compl, fun h => ⟨h.subtype (· in s), h.subtype (· in sᶜ)⟩⟩

@[to_additive]
/--
theorem `Multipliable.tprod_subtype_mul_tprod_subtype_compl` / 定理 `Multipliable.tprod_subtype_mul_tprod_subtype_compl`

English:
theorem Multipliable.tprod_subtype_mul_tprod_subtype_compl
  statement: [T2Space α] {f : β -> α}
  proof: ((hf.subtype _).hasProd.mul_compl (hf.subtype _).hasProd).unique hf.hasProd

@[to_additive]

中文:
定理 Multipliable.tprod_subtype_mul_tprod_subtype_compl
  结论: [T2空间 α] {f : β -> α}
  证明: ((hf.subtype _).hasProd.mul_compl (hf.subtype _).hasProd).unique hf.hasProd

@[to_additive]
-/
protected theorem Multipliable.tprod_subtype_mul_tprod_subtype_compl [T2Space α] {f : β -> α}
    (hf : Multipliable f) (s : Set β) : (∏' x : s, f x) * ∏' x : ↑sᶜ, f x = ∏' x, f x :=
  ((hf.subtype _).hasProd.mul_compl (hf.subtype _).hasProd).unique hf.hasProd

@[to_additive]
/--
theorem `Multipliable.prod_mul_tprod_subtype_compl` / 定理 `Multipliable.prod_mul_tprod_subtype_compl`

English:
theorem Multipliable.prod_mul_tprod_subtype_compl
  statement: [T2Space α] {f : β -> α}
  proof: by
  rw [← hf.tprod_subtype_mul_tprod_subtype_compl s]
  simp only [Finset.tprod_subtype', mul_right_inj]
  rfl

中文:
定理 Multipliable.prod_mul_tprod_subtype_compl
  结论: [T2空间 α] {f : β -> α}
  证明: by
  rw [← hf.tprod_subtype_mul_tprod_subtype_compl s]
  simp only [Finset.tprod_subtype', mul_right_inj]
  rfl
-/
protected theorem Multipliable.prod_mul_tprod_subtype_compl [T2Space α] {f : β -> α}
    (hf : Multipliable f) (s : Finset β) :
    (∏ x in s, f x) * ∏' x : { x // x ∉ s }, f x = ∏' x, f x := by
  rw [← hf.tprod_subtype_mul_tprod_subtype_compl s]
  simp only [Finset.tprod_subtype', mul_right_inj]
  rfl

end IsUniformGroup

section IsTopologicalGroup

variable {G : Type*} [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] {f : α -> G}

@[to_additive]
/--
theorem `Multipliable.vanishing` / 定理 `Multipliable.vanishing`

English:
theorem Multipliable.vanishing
  given: (hf : Multipliable f) ⦃e
  statement: Set G⦄ (he : e in 𝓝 (1 : G)) :
  proof: by
  classical
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  exact cauchySeq_finset_iff_prod_vanishing.1 hf.hasProd.cauchySeq e he

@[to_additive]

中文:
定理 Multipliable.vanishing
  条件: (hf : Multipliable f) ⦃e
  结论: 集合 G⦄ (he : e in 𝓝 (1 : G)) :
  证明: by
  classical
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  exact cauchySeq_finset_iff_prod_vanishing.1 hf.hasProd.cauchySeq e he

@[to_additive]

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.rightUniformSpace, IsUniformGroup, UniformSpace, cauchySeq, cauchySeq_finset_iff_prod_vanishing, classical, hasProd, hf.hasProd.cauchySeq, isUniformGroup_of_commGroup, rightUniformSpace
-/
theorem Multipliable.vanishing (hf : Multipliable f) ⦃e : Set G⦄ (he : e in 𝓝 (1 : G)) :
    exists s : Finset α, forall t, Disjoint t s -> (∏ k in t, f k) in e := by
  classical
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  exact cauchySeq_finset_iff_prod_vanishing.1 hf.hasProd.cauchySeq e he

@[to_additive]
/--
theorem `Multipliable.tprod_vanishing` / 定理 `Multipliable.tprod_vanishing`

English:
theorem Multipliable.tprod_vanishing
  given: (hf : Multipliable f) ⦃e
  statement: Set G⦄ (he : e in 𝓝 1) :
  proof: by
  classical
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  exact cauchySeq_finset_iff_tprod_vanishing.1 hf.hasProd.cauchySeq e he

中文:
定理 Multipliable.tprod_vanishing
  条件: (hf : Multipliable f) ⦃e
  结论: 集合 G⦄ (he : e in 𝓝 1) :
  证明: by
  classical
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  exact cauchySeq_finset_iff_tprod_vanishing.1 hf.hasProd.cauchySeq e he

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.rightUniformSpace, IsUniformGroup, UniformSpace, cauchySeq, cauchySeq_finset_iff_tprod_vanishing, classical, hasProd, hf.hasProd.cauchySeq, isUniformGroup_of_commGroup, rightUniformSpace
-/
theorem Multipliable.tprod_vanishing (hf : Multipliable f) ⦃e : Set G⦄ (he : e in 𝓝 1) :
    exists s : Finset α, forall t : Set α, Disjoint t s -> (∏' b : t, f b) in e := by
  classical
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  exact cauchySeq_finset_iff_tprod_vanishing.1 hf.hasProd.cauchySeq e he

/-- The product over the complement of a finset tends to `1` when the finset grows to cover the
whole space. This does not need a multipliability assumption, as otherwise all such products are
one. -/
@[to_additive /-- The sum over the complement of a finset tends to `0` when the finset grows to
cover the whole space. This does not need a summability assumption, as otherwise all such sums are
zero. -/]
/--
theorem `tendsto_tprod_compl_atTop_one` / 定理 `tendsto_tprod_compl_atTop_one`

English:
theorem tendsto_tprod_compl_atTop_one
  given: (f : α -> G)
  proof: by
  by_cases H : Multipliable f
  · intro e he
    obtain ⟨s, hs⟩ := H.tprod_vanishing he
    simp only [Filter.mem_map, mem_atTop_sets, Set.mem_preimage]
exact ⟨s, fun t hts => hs tᶜ Set.disjoint_left.mpr fun a ha has => ha (hts has)⟩
  · refine tendsto_const_nhds.congr fun _ => (tprod_eq_one_of_not_multipliable ?_).symm
    rwa [Finset.multipliable_compl_iff]

中文:
定理 tendsto_tprod_compl_atTop_one
  条件: (f : α -> G)
  证明: by
  by_cases H : Multipliable f
  · intro e he
    obtain ⟨s, hs⟩ := H.tprod_vanishing he
    simp only [Filter.mem_map, mem_atTop_sets, Set.mem_preimage]
exact ⟨s, fun t hts => hs tᶜ Set.disjoint_left.mpr fun a ha has => ha (hts has)⟩
  · refine tendsto_const_nhds.congr fun _ => (tprod_eq_one_of_not_multipliable ?_).symm
    rwa [Finset.multipliable_compl_iff]

Depends on / 依赖: Filter, Filter.mem_map, Finset, Finset.multipliable_compl_iff, H.tprod_vanishing, Multipliable, Set.disjoint_left.mpr, Set.mem_preimage, disjoint_left, mem_atTop_sets, mem_map, mem_preimage, multipliable_compl_iff, tendsto_const_nhds, tendsto_const_nhds.congr, tprod_eq_one_of_not_multipliable, tprod_vanishing
-/
theorem tendsto_tprod_compl_atTop_one (f : α -> G) :
    Tendsto (fun s : Finset α => ∏' a : { x // x ∉ s }, f a) atTop (𝓝 1) := by
  by_cases H : Multipliable f
  · intro e he
    obtain ⟨s, hs⟩ := H.tprod_vanishing he
    simp only [Filter.mem_map, mem_atTop_sets, Set.mem_preimage]
exact ⟨s, fun t hts => hs tᶜ Set.disjoint_left.mpr fun a ha has => ha (hts has)⟩
  · refine tendsto_const_nhds.congr fun _ => (tprod_eq_one_of_not_multipliable ?_).symm
    rwa [Finset.multipliable_compl_iff]

/-- Product divergence test: if `f` is unconditionally multipliable, then `f x` tends to one along
`cofinite`. -/
@[to_additive /-- Series divergence test: if `f` is unconditionally summable, then `f x` tends to
zero along `cofinite`. -/]
/--
theorem `Multipliable.tendsto_cofinite_one` / 定理 `Multipliable.tendsto_cofinite_one`

English:
theorem Multipliable.tendsto_cofinite_one
  given: (hf : Multipliable f)
  statement: Tendsto f cofinite (𝓝 1)
  proof: by
  intro e he
  rw [Filter.mem_map]
  rcases hf.vanishing he with ⟨s, hs⟩
  refine s.eventually_cofinite_notMem.mono fun x hx => ?_
  · simpa using hs {x} (disjoint_singleton_left.2 hx)

@[to_additive]

中文:
定理 Multipliable.tendsto_cofinite_one
  条件: (hf : Multipliable f)
  结论: 收敛 f cofinite (𝓝 1)
  证明: by
  intro e he
  rw [Filter.mem_map]
  rcases hf.vanishing he with ⟨s, hs⟩
  refine s.eventually_cofinite_notMem.mono fun x hx => ?_
  · simpa using hs {x} (disjoint_singleton_left.2 hx)

@[to_additive]

Depends on / 依赖: Filter, Filter.mem_map, disjoint_singleton_left, eventually_cofinite_notMem, hf.vanishing, mem_map, s.eventually_cofinite_notMem.mono, vanishing
-/
theorem Multipliable.tendsto_cofinite_one (hf : Multipliable f) : Tendsto f cofinite (𝓝 1) := by
  intro e he
  rw [Filter.mem_map]
  rcases hf.vanishing he with ⟨s, hs⟩
  refine s.eventually_cofinite_notMem.mono fun x hx => ?_
  · simpa using hs {x} (disjoint_singleton_left.2 hx)

@[to_additive]
/--
theorem `Multipliable.hasFiniteMulSupport_of_discreteTopology` / 定理 `Multipliable.hasFiniteMulSupport_of_discreteTopology`

English:
theorem Multipliable.hasFiniteMulSupport_of_discreteTopology
  proof: haveI : IsTopologicalGroup α := ⟨⟩
  h.tendsto_cofinite_one (discreteTopology_iff_singleton_mem_nhds.mp ‹_› 1)

@[deprecated (since := "2026-03-03")] alias
  Multipliable.finite_mulSupport_of_discreteTopology :=
    Multipliable.hasFiniteMulSupport_of_discreteTopology

@[deprecated (since := "2026-03-03")] alias
  Summable.finite_support_of_discreteTopology :=
    Summable.hasFiniteSupport_of_discreteTopology

@[to_additive]

中文:
定理 Multipliable.hasFiniteMulSupport_of_discreteTopology
  证明: haveI : IsTopologicalGroup α := ⟨⟩
  h.tendsto_cofinite_one (discreteTopology_iff_singleton_mem_nhds.mp ‹_› 1)

@[deprecated (since := "2026-03-03")] alias
  Multipliable.finite_mulSupport_of_discreteTopology :=
    Multipliable.hasFiniteMulSupport_of_discreteTopology

@[deprecated (since := "2026-03-03")] alias
  Summable.finite_support_of_discreteTopology :=
    Summable.hasFiniteSupport_of_discreteTopology

@[to_additive]

Depends on / 依赖: IsTopologicalGroup, discreteTopology_iff_singleton_mem_nhds, discreteTopology_iff_singleton_mem_nhds.mp, h.tendsto_cofinite_one, tendsto_cofinite_one
-/
theorem Multipliable.hasFiniteMulSupport_of_discreteTopology
    {α : Type*} [CommGroup α] [TopologicalSpace α] [DiscreteTopology α]
    {β : Type*} (f : β -> α) (h : Multipliable f) : HasFiniteMulSupport f :=
  haveI : IsTopologicalGroup α := ⟨⟩
  h.tendsto_cofinite_one (discreteTopology_iff_singleton_mem_nhds.mp ‹_› 1)

@[deprecated (since := "2026-03-03")] alias
  Multipliable.finite_mulSupport_of_discreteTopology :=
    Multipliable.hasFiniteMulSupport_of_discreteTopology

@[deprecated (since := "2026-03-03")] alias
  Summable.finite_support_of_discreteTopology :=
    Summable.hasFiniteSupport_of_discreteTopology

@[to_additive]
/--
theorem `Multipliable.countable_mulSupport` / 定理 `Multipliable.countable_mulSupport`

English:
theorem Multipliable.countable_mulSupport
  statement: [FirstCountableTopology G] [T1Space G]
  proof: by
  simpa only [ker_nhds] using! hf.tendsto_cofinite_one.countable_compl_preimage_ker

@[to_additive]

中文:
定理 Multipliable.countable_mulSupport
  结论: [第一可数拓扑 G] [T1空间 G]
  证明: by
  simpa only [ker_nhds] using! hf.tendsto_cofinite_one.countable_compl_preimage_ker

@[to_additive]

Depends on / 依赖: countable_compl_preimage_ker, hf.tendsto_cofinite_one.countable_compl_preimage_ker, ker_nhds, tendsto_cofinite_one
-/
theorem Multipliable.countable_mulSupport [FirstCountableTopology G] [T1Space G]
    (hf : Multipliable f) : f.mulSupport.Countable := by
  simpa only [ker_nhds] using! hf.tendsto_cofinite_one.countable_compl_preimage_ker

@[to_additive]
/--
theorem `multipliable_const_iff` / 定理 `multipliable_const_iff`

English:
theorem multipliable_const_iff
  given: [Infinite β] [T2Space G] (a : G)
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra ha
    have : {a}ᶜ in 𝓝 1 := compl_singleton_mem_nhds (Ne.symm ha)
    have : Finite β := by
      simpa [← Set.finite_univ_iff] using h.tendsto_cofinite_one this
    exact not_finite β
  · rintro rfl
    exact multipliable_one

@[to_additive (attr := simp)]

中文:
定理 multipliable_const_iff
  条件: [无限 β] [T2空间 G] (a : G)
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra ha
    have : {a}ᶜ in 𝓝 1 := compl_singleton_mem_nhds (Ne.symm ha)
    have : Finite β := by
      simpa [← Set.finite_univ_iff] using h.tendsto_cofinite_one this
    exact not_finite β
  · rintro rfl
    exact multipliable_one

@[to_additive (attr := simp)]

Depends on / 依赖: Finite, Ne.symm, Set.finite_univ_iff, compl_singleton_mem_nhds, finite_univ_iff, h.tendsto_cofinite_one, multipliable_one, not_finite, tendsto_cofinite_one
-/
theorem multipliable_const_iff [Infinite β] [T2Space G] (a : G) :
    Multipliable (fun _ : β => a) ↔ a = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra ha
    have : {a}ᶜ in 𝓝 1 := compl_singleton_mem_nhds (Ne.symm ha)
    have : Finite β := by
      simpa [← Set.finite_univ_iff] using h.tendsto_cofinite_one this
    exact not_finite β
  · rintro rfl
    exact multipliable_one

@[to_additive (attr := simp)]
/--
theorem `tprod_const` / 定理 `tprod_const`

English:
theorem tprod_const
  given: [T2Space G] (a : G)
  statement: ∏' _ : β, a = a ^ (Nat.card β)
  proof: by
  rcases finite_or_infinite β with hβ | hβ
  · let : Fintype β := Fintype.ofFinite β
    rw [tprod_eq_prod (s := univ) (fun x hx => (hx (mem_univ x)).elim)]
    simp only [prod_const, Nat.card_eq_fintype_card, Fintype.card]
  · simp only [Nat.card_eq_zero_of_infinite, pow_zero]
    rcases eq_or_ne a 1 with rfl | ha
    · simp
    · apply tprod_eq_one_of_not_multipliable
      simpa [multipliable_const_iff] using ha

中文:
定理 tprod_const
  条件: [T2空间 G] (a : G)
  结论: ∏' _ : β, a = a ^ (自然数.card β)
  证明: by
  rcases finite_or_infinite β with hβ | hβ
  · let : Fintype β := Fintype.ofFinite β
    rw [tprod_eq_prod (s := univ) (fun x hx => (hx (mem_univ x)).elim)]
    simp only [prod_const, Nat.card_eq_fintype_card, Fintype.card]
  · simp only [Nat.card_eq_zero_of_infinite, pow_zero]
    rcases eq_or_ne a 1 with rfl | ha
    · simp
    · apply tprod_eq_one_of_not_multipliable
      simpa [multipliable_const_iff] using ha

Depends on / 依赖: Fintype, Fintype.card, Fintype.ofFinite, Nat.card_eq_fintype_card, Nat.card_eq_zero_of_infinite, card_eq_fintype_card, card_eq_zero_of_infinite, eq_or_ne, finite_or_infinite, mem_univ, multipliable_const_iff, ofFinite, pow_zero, prod_const, tprod_eq_one_of_not_multipliable, tprod_eq_prod
-/
theorem tprod_const [T2Space G] (a : G) : ∏' _ : β, a = a ^ (Nat.card β) := by
  rcases finite_or_infinite β with hβ | hβ
  · let : Fintype β := Fintype.ofFinite β
    rw [tprod_eq_prod (s := univ) (fun x hx => (hx (mem_univ x)).elim)]
    simp only [prod_const, Nat.card_eq_fintype_card, Fintype.card]
  · simp only [Nat.card_eq_zero_of_infinite, pow_zero]
    rcases eq_or_ne a 1 with rfl | ha
    · simp
    · apply tprod_eq_one_of_not_multipliable
      simpa [multipliable_const_iff] using ha

end IsTopologicalGroup

section CommGroupWithZero

variable {K : Type*} [CommGroupWithZero K] [TopologicalSpace K]
  {f g : α -> K} {L : SummationFilter α}

/-!
## Groups with a zero

These lemmas apply to a `CommGroupWithZero`; the most familiar case is when `K` is a field. These
are specific to the product setting and do not have a sensible additive analogue.
-/

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul K]

open Finset in
/--
lemma `HasProd.congr_cofinite₀` / 引理 `HasProd.congr_cofinite₀`

English:
lemma HasProd.congr_cofinite₀
  statement: {c : K} (hc : HasProd f c) {s : Finset α}
  proof: by
  classical
  refine (Tendsto.mul_const ((∏ i in s, g i) / ∏ i in s, f i) hc).congr' ?_
  filter_upwards [eventually_ge_atTop s] with t ht
  calc (∏ i in t, f i) * ((∏ i in s, g i) / ∏ i in s, f i)
  _ = ((∏ i in s, f i) * ∏ i in t \ s, g i) * _ := by
    conv_lhs => rw [← union_sdiff_of_subset ht, prod_union disjoint_sdiff,
      prod_congr rfl fun i hi => hs' i (mem_sdiff.mp hi).2]
  _ = (∏ i in s, g i) * ∏ i in t \ s, g i := by
    rw [← mul_div_assoc]; rw [← div_mul_eq_mul_div]; rw [← div_mul_eq_mul_div]; rw [div_self]; rw [one_mul]; rw [mul_comm]
    exact prod_ne_zero_iff.mpr hs
  _ = ∏ i in t, g i := by
    rw [← prod_union disjoint_sdiff]; rw [union_sdiff_of_subset ht]

中文:
引理 有积类型.congr_cofinite₀
  结论: {c : K} (hc : 有积类型 f c) {s : 有限集 α}
  证明: by
  classical
  refine (Tendsto.mul_const ((∏ i in s, g i) / ∏ i in s, f i) hc).congr' ?_
  filter_upwards [eventually_ge_atTop s] with t ht
  calc (∏ i in t, f i) * ((∏ i in s, g i) / ∏ i in s, f i)
  _ = ((∏ i in s, f i) * ∏ i in t \ s, g i) * _ := by
    conv_lhs => rw [← union_sdiff_of_subset ht, prod_union disjoint_sdiff,
      prod_congr rfl fun i hi => hs' i (mem_sdiff.mp hi).2]
  _ = (∏ i in s, g i) * ∏ i in t \ s, g i := by
    rw [← mul_div_assoc]; rw [← div_mul_eq_mul_div]; rw [← div_mul_eq_mul_div]; rw [div_self]; rw [one_mul]; rw [mul_comm]
    exact prod_ne_zero_iff.mpr hs
  _ = ∏ i in t, g i := by
    rw [← prod_union disjoint_sdiff]; rw [union_sdiff_of_subset ht]

Depends on / 依赖: Tendsto, Tendsto.mul_const, classical, conv_lhs, disjoint_sdiff, div_, div_mul_eq_mul_div, eventually_ge_atTop, filter_upwards, mem_sdiff, mem_sdiff.mp, mul_const, mul_div_assoc, prod_congr, prod_union, union_sdiff_of_subset
-/
lemma HasProd.congr_cofinite₀ {c : K} (hc : HasProd f c) {s : Finset α}
    (hs : forall a in s, f a != 0) (hs' : forall a ∉ s, f a = g a) :
    HasProd g (c * ((∏ i in s, g i) / ∏ i in s, f i)) := by
  classical
  refine (Tendsto.mul_const ((∏ i in s, g i) / ∏ i in s, f i) hc).congr' ?_
  filter_upwards [eventually_ge_atTop s] with t ht
  calc (∏ i in t, f i) * ((∏ i in s, g i) / ∏ i in s, f i)
  _ = ((∏ i in s, f i) * ∏ i in t \ s, g i) * _ := by
    conv_lhs => rw [← union_sdiff_of_subset ht, prod_union disjoint_sdiff,
      prod_congr rfl fun i hi => hs' i (mem_sdiff.mp hi).2]
  _ = (∏ i in s, g i) * ∏ i in t \ s, g i := by
    rw [← mul_div_assoc]; rw [← div_mul_eq_mul_div]; rw [← div_mul_eq_mul_div]; rw [div_self]; rw [one_mul]; rw [mul_comm]
    exact prod_ne_zero_iff.mpr hs
  _ = ∏ i in t, g i := by
    rw [← prod_union disjoint_sdiff]; rw [union_sdiff_of_subset ht]

/--
lemma `Multipliable.tsum_congr_cofinite₀` / 引理 `Multipliable.tsum_congr_cofinite₀`

English:
lemma Multipliable.tsum_congr_cofinite₀
  statement: [T2Space K] (hc : Multipliable f) {s : Finset α}
  proof: (hc.hasProd.congr_cofinite₀ hs hs').tprod_eq

中文:
引理 Multipliable.tsum_congr_cofinite₀
  结论: [T2空间 K] (hc : Multipliable f) {s : 有限集 α}
  证明: (hc.hasProd.congr_cofinite₀ hs hs').tprod_eq
-/
protected lemma Multipliable.tsum_congr_cofinite₀ [T2Space K] (hc : Multipliable f) {s : Finset α}
    (hs : forall a in s, f a != 0) (hs' : forall a ∉ s, f a = g a) :
    ∏' i, g i = ((∏' i, f i) * ((∏ i in s, g i) / ∏ i in s, f i)) :=
  (hc.hasProd.congr_cofinite₀ hs hs').tprod_eq

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Multipliable.congr_cofinite₀` / 引理 `Multipliable.congr_cofinite₀`

English:
lemma Multipliable.congr_cofinite₀
  statement: (hf : Multipliable f) (hf' : forall a, f a != 0)
  proof: by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨s, hs⟩ : exists s : Finset α, forall i ∉ s, f i = g i := ⟨hfg.toFinset, by simp⟩
  exact (hc.congr_cofinite₀ (fun a _ => hf' a) hs).multipliable

中文:
引理 Multipliable.congr_cofinite₀
  结论: (hf : Multipliable f) (hf' : 对任意 a, f a != 0)
  证明: by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨s, hs⟩ : exists s : Finset α, forall i ∉ s, f i = g i := ⟨hfg.toFinset, by simp⟩
  exact (hc.congr_cofinite₀ (fun a _ => hf' a) hs).multipliable

Depends on / 依赖: Finset, hc.congr_cofinite, hfg.toFinset, multipliable, toFinset
-/
lemma Multipliable.congr_cofinite₀ (hf : Multipliable f) (hf' : forall a, f a != 0)
    (hfg : forallᶠ a in cofinite, f a = g a) :
    Multipliable g := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨s, hs⟩ : exists s : Finset α, forall i ∉ s, f i = g i := ⟨hfg.toFinset, by simp⟩
  exact (hc.congr_cofinite₀ (fun a _ => hf' a) hs).multipliable

end SeparatelyContinuousMul

/--
theorem `HasProd.inv₀` / 定理 `HasProd.inv₀`

English:
theorem HasProd.inv₀
  given: {a : K} [ContinuousInv₀ K] (h : HasProd f a L) (ha : a != 0)
  proof: by
  simp_rw [HasProd, Finset.prod_inv_distrib]
  exact Tendsto.inv₀ h ha

中文:
定理 有积类型.inv₀
  条件: {a : K} [余ntinuousInv₀ K] (h : 有积类型 f a L) (ha : a != 0)
  证明: by
  simp_rw [HasProd, Finset.prod_inv_distrib]
  exact Tendsto.inv₀ h ha

Depends on / 依赖: Finset, Finset.prod_inv_distrib, HasProd, Tendsto, Tendsto.inv, prod_inv_distrib, simp_rw
-/
theorem HasProd.inv₀ {a : K} [ContinuousInv₀ K] (h : HasProd f a L) (ha : a != 0) :
    HasProd (fun x => (f x)⁻¹) a⁻¹ L := by
  simp_rw [HasProd, Finset.prod_inv_distrib]
  exact Tendsto.inv₀ h ha

/--
theorem `Multipliable.inv₀` / 定理 `Multipliable.inv₀`

English:
theorem Multipliable.inv₀
  given: [ContinuousInv₀ K] (h : Multipliable f L) (ne_zero : ∏'[L] x, f x != 0)
  proof: .multipliable h.hasProd.inv₀ ne_zero

中文:
定理 Multipliable.inv₀
  条件: [余ntinuousInv₀ K] (h : Multipliable f L) (ne_zero : ∏'[L] x, f x != 0)
  证明: .multipliable h.hasProd.inv₀ ne_zero

Depends on / 依赖: h.hasProd.inv, hasProd, multipliable, ne_zero
-/
theorem Multipliable.inv₀ [ContinuousInv₀ K] (h : Multipliable f L) (ne_zero : ∏'[L] x, f x != 0) :
    Multipliable (fun x => (f x)⁻¹) L :=
.multipliable h.hasProd.inv₀ ne_zero

/--
theorem `Multipliable.tprod_inv₀` / 定理 `Multipliable.tprod_inv₀`

English:
theorem Multipliable.tprod_inv₀
  statement: [ContinuousInv₀ K] [T2Space K] [L.NeBot]
  proof: .tprod_eq h.hasProd.inv₀ ne_zero

中文:
定理 Multipliable.tprod_inv₀
  结论: [余ntinuousInv₀ K] [T2空间 K] [L.NeBot]
  证明: .tprod_eq h.hasProd.inv₀ ne_zero

Depends on / 依赖: h.hasProd.inv, hasProd, ne_zero, tprod_eq
-/
theorem Multipliable.tprod_inv₀ [ContinuousInv₀ K] [T2Space K] [L.NeBot]
    (h : Multipliable f L) (ne_zero : ∏'[L] x, f x != 0) :
    ∏'[L] x, (f x)⁻¹ = (∏'[L] x, f x )⁻¹ :=
.tprod_eq h.hasProd.inv₀ ne_zero

/--
theorem `HasProd.div₀` / 定理 `HasProd.div₀`

English:
theorem HasProd.div₀
  statement: [ContinuousInv₀ K] [ContinuousMul K] {a b : K}
  proof: by
  simp only [div_eq_mul_inv]
exact hf.mul hg.inv₀ hb

中文:
定理 有积类型.div₀
  结论: [余ntinuousInv₀ K] [连续乘法 K] {a b : K}
  证明: by
  simp only [div_eq_mul_inv]
exact hf.mul hg.inv₀ hb

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
theorem HasProd.div₀ [ContinuousInv₀ K] [ContinuousMul K] {a b : K}
    (hf : HasProd f a L) (hg : HasProd g b L) (hb : b != 0) :
    HasProd (fun x => f x / g x) (a / b) L := by
  simp only [div_eq_mul_inv]
exact hf.mul hg.inv₀ hb

/--
theorem `Multipliable.div₀` / 定理 `Multipliable.div₀`

English:
theorem Multipliable.div₀
  statement: [ContinuousInv₀ K] [ContinuousMul K]
  proof: .multipliable hf.hasProd.div₀ hg.hasProd ne_zero

中文:
定理 Multipliable.div₀
  结论: [余ntinuousInv₀ K] [连续乘法 K]
  证明: .multipliable hf.hasProd.div₀ hg.hasProd ne_zero

Depends on / 依赖: hasProd, hf.hasProd.div, hg.hasProd, multipliable, ne_zero
-/
theorem Multipliable.div₀ [ContinuousInv₀ K] [ContinuousMul K]
    (hf : Multipliable f L) (hg : Multipliable g L) (ne_zero : ∏'[L] x, g x != 0) :
    Multipliable (fun x => f x / g x) L :=
.multipliable hf.hasProd.div₀ hg.hasProd ne_zero

/--
theorem `Multipliable.tprod_div₀` / 定理 `Multipliable.tprod_div₀`

English:
theorem Multipliable.tprod_div₀
  statement: [ContinuousInv₀ K] [ContinuousMul K] [T2Space K] [L.NeBot]
  proof: .tprod_eq hf.hasProd.div₀ hg.hasProd ne_zero

中文:
定理 Multipliable.tprod_div₀
  结论: [余ntinuousInv₀ K] [连续乘法 K] [T2空间 K] [L.NeBot]
  证明: .tprod_eq hf.hasProd.div₀ hg.hasProd ne_zero

Depends on / 依赖: hasProd, hf.hasProd.div, hg.hasProd, ne_zero, tprod_eq
-/
theorem Multipliable.tprod_div₀ [ContinuousInv₀ K] [ContinuousMul K] [T2Space K] [L.NeBot]
    (hf : Multipliable f L) (hg : Multipliable g L) (ne_zero : ∏'[L] x, g x != 0) :
    (∏'[L] x, f x / g x) = (∏'[L] x, f x) / (∏'[L] x, g x) :=
.tprod_eq hf.hasProd.div₀ hg.hasProd ne_zero

end CommGroupWithZero
