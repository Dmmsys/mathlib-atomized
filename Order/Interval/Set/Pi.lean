/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Piecewise
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Intervals in `pi`-space

In this we prove various simple lemmas about intervals in `Π i, α i`. Closed intervals (`Ici x`,
`Iic x`, `Icc x y`) are equal to products of their projections to `α i`, while (semi-)open intervals
usually include the corresponding products as proper subsets.
-/

public section

-- Porting note: Added, since dot notation no longer works on `Function.update`
open Function

variable {ι : Type*} {α : ι -> Type*}

namespace Set

section PiPreorder

variable [forall i, Preorder (α i)] (x y : forall i, α i)

@[to_dual (attr := simp)]
/--
theorem `pi_univ_Ici` / 定理 `pi_univ_Ici`

English:
theorem pi_univ_Ici
  statement: (pi univ fun i => Ici (x i)) = Ici x
  proof: ext fun y => by simp [Pi.le_def]

@[to_dual self, simp]

中文:
定理 pi_univ_Ici
  结论: (pi univ fun i => Ici (x i)) = Ici x
  证明: ext fun y => by simp [Pi.le_def]

@[to_dual self, simp]

Depends on / 依赖: Pi.le_def, le_def
-/
theorem pi_univ_Ici : (pi univ fun i => Ici (x i)) = Ici x :=
  ext fun y => by simp [Pi.le_def]

@[to_dual self, simp]
/--
theorem `pi_univ_Icc` / 定理 `pi_univ_Icc`

English:
theorem pi_univ_Icc
  statement: (pi univ fun i => Icc (x i) (y i)) = Icc x y
  proof: ext fun y => by simp [Pi.le_def, forall_and]

@[to_dual self]

中文:
定理 pi_univ_Icc
  结论: (pi univ fun i => Icc (x i) (y i)) = Icc x y
  证明: ext fun y => by simp [Pi.le_def, forall_and]

@[to_dual self]

Depends on / 依赖: Pi.le_def, forall_and, le_def
-/
theorem pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc x y :=
  ext fun y => by simp [Pi.le_def, forall_and]

@[to_dual self]
/--
theorem `piecewise_mem_Icc` / 定理 `piecewise_mem_Icc`

English:
theorem piecewise_mem_Icc
  statement: {s : Set ι} [forall j, Decidable (j in s)] {f₁ f₂ g₁ g₂ : forall i, α i}
  proof: ⟨le_piecewise (fun i hi => (h₁ i hi).1) fun i hi => (h₂ i hi).1,
    piecewise_le (fun i hi => (h₁ i hi).2) fun i hi => (h₂ i hi).2⟩

@[to_dual self]

中文:
定理 piecewise_mem_Icc
  结论: {s : Set ι} [对任意 j, Decidable (j in s)] {f₁ f₂ g₁ g₂ : 对任意 i, α i}
  证明: ⟨le_piecewise (fun i hi => (h₁ i hi).1) fun i hi => (h₂ i hi).1,
    piecewise_le (fun i hi => (h₁ i hi).2) fun i hi => (h₂ i hi).2⟩

@[to_dual self]

Depends on / 依赖: le_piecewise, piecewise_le
-/
theorem piecewise_mem_Icc {s : Set ι} [forall j, Decidable (j in s)] {f₁ f₂ g₁ g₂ : forall i, α i}
    (h₁ : forall i in s, f₁ i in Icc (g₁ i) (g₂ i)) (h₂ : forall i ∉ s, f₂ i in Icc (g₁ i) (g₂ i)) :
    s.piecewise f₁ f₂ in Icc g₁ g₂ :=
  ⟨le_piecewise (fun i hi => (h₁ i hi).1) fun i hi => (h₂ i hi).1,
    piecewise_le (fun i hi => (h₁ i hi).2) fun i hi => (h₂ i hi).2⟩

@[to_dual self]
/--
theorem `piecewise_mem_Icc'` / 定理 `piecewise_mem_Icc'`

English:
theorem piecewise_mem_Icc'
  statement: {s : Set ι} [forall j, Decidable (j in s)] {f₁ f₂ g₁ g₂ : forall i, α i}
  proof: piecewise_mem_Icc (fun _ _ => ⟨h₁.1 _, h₁.2 _⟩) fun _ _ => ⟨h₂.1 _, h₂.2 _⟩

中文:
定理 piecewise_mem_Icc'
  结论: {s : Set ι} [对任意 j, Decidable (j in s)] {f₁ f₂ g₁ g₂ : 对任意 i, α i}
  证明: piecewise_mem_Icc (fun _ _ => ⟨h₁.1 _, h₁.2 _⟩) fun _ _ => ⟨h₂.1 _, h₂.2 _⟩

Depends on / 依赖: piecewise_mem_Icc
-/
theorem piecewise_mem_Icc' {s : Set ι} [forall j, Decidable (j in s)] {f₁ f₂ g₁ g₂ : forall i, α i}
    (h₁ : f₁ in Icc g₁ g₂) (h₂ : f₂ in Icc g₁ g₂) : s.piecewise f₁ f₂ in Icc g₁ g₂ :=
  piecewise_mem_Icc (fun _ _ => ⟨h₁.1 _, h₁.2 _⟩) fun _ _ => ⟨h₂.1 _, h₂.2 _⟩

section Nonempty

@[to_dual]
/--
theorem `pi_univ_Ioi_subset` / 定理 `pi_univ_Ioi_subset`

English:
theorem pi_univ_Ioi_subset
  given: [Nonempty ι]
  statement: (pi univ fun i => Ioi (x i)) subseteq Ioi x
  proof: fun _ hz =>
⟨fun i => le_of_lt hz i trivial, fun h =>
    (‹Nonempty ι›.elim) fun i => not_lt_of_ge (h i) (hz i trivial)⟩

@[to_dual self]

中文:
定理 pi_univ_Ioi_subset
  条件: [Nonempty ι]
  结论: (pi univ fun i => Ioi (x i)) subseteq Ioi x
  证明: fun _ hz =>
⟨fun i => le_of_lt hz i trivial, fun h =>
    (‹Nonempty ι›.elim) fun i => not_lt_of_ge (h i) (hz i trivial)⟩

@[to_dual self]
-/
theorem pi_univ_Ioi_subset [Nonempty ι] : (pi univ fun i => Ioi (x i)) subseteq Ioi x := fun _ hz =>
⟨fun i => le_of_lt hz i trivial, fun h =>
    (‹Nonempty ι›.elim) fun i => not_lt_of_ge (h i) (hz i trivial)⟩

@[to_dual self]
/--
theorem `pi_univ_Ioo_subset` / 定理 `pi_univ_Ioo_subset`

English:
theorem pi_univ_Ioo_subset
  given: [Nonempty ι]
  statement: (pi univ fun i => Ioo (x i) (y i)) subseteq Ioo x y
  proof: fun _ hx =>
  ⟨(pi_univ_Ioi_subset _) fun i hi => (hx i hi).1, (pi_univ_Iio_subset _) fun i hi => (hx i hi).2⟩

@[to_dual]

中文:
定理 pi_univ_Ioo_subset
  条件: [Nonempty ι]
  结论: (pi univ fun i => Ioo (x i) (y i)) subseteq Ioo x y
  证明: fun _ hx =>
  ⟨(pi_univ_Ioi_subset _) fun i hi => (hx i hi).1, (pi_univ_Iio_subset _) fun i hi => (hx i hi).2⟩

@[to_dual]
-/
theorem pi_univ_Ioo_subset [Nonempty ι] : (pi univ fun i => Ioo (x i) (y i)) subseteq Ioo x y := fun _ hx =>
  ⟨(pi_univ_Ioi_subset _) fun i hi => (hx i hi).1, (pi_univ_Iio_subset _) fun i hi => (hx i hi).2⟩

@[to_dual]
/--
theorem `pi_univ_Ioc_subset` / 定理 `pi_univ_Ioc_subset`

English:
theorem pi_univ_Ioc_subset
  given: [Nonempty ι]
  statement: (pi univ fun i => Ioc (x i) (y i)) subseteq Ioc x y
  proof: fun _ hx =>
  ⟨(pi_univ_Ioi_subset _) fun i hi => (hx i hi).1, fun i => (hx i trivial).2⟩

中文:
定理 pi_univ_Ioc_subset
  条件: [Nonempty ι]
  结论: (pi univ fun i => Ioc (x i) (y i)) subseteq Ioc x y
  证明: fun _ hx =>
  ⟨(pi_univ_Ioi_subset _) fun i hi => (hx i hi).1, fun i => (hx i trivial).2⟩
-/
theorem pi_univ_Ioc_subset [Nonempty ι] : (pi univ fun i => Ioc (x i) (y i)) subseteq Ioc x y := fun _ hx =>
  ⟨(pi_univ_Ioi_subset _) fun i hi => (hx i hi).1, fun i => (hx i trivial).2⟩

end Nonempty

variable [DecidableEq ι]

open Function (update)

/--
theorem `pi_univ_Ioc_update_left` / 定理 `pi_univ_Ioc_update_left`

English:
theorem pi_univ_Ioc_update_left
  given: {x y : forall i, α i} {i₀ : ι} {m : α i₀} (hm : x i₀ <= m)
  proof: by
  have : Ioc m (y i₀) = Ioi m inter Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]; rw [← inter_assoc]; rw [inter_eq_self_of_subset_left (Ioi_subset_Ioi hm)]
  simp_rw [univ_pi_update i₀ _ _ fun i z => Ioc z (y i), ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← inte

中文:
定理 pi_univ_Ioc_update_left
  条件: {x y : 对任意 i, α i} {i₀ : ι} {m : α i₀} (hm : x i₀ <= m)
  证明: by
  have : Ioc m (y i₀) = Ioi m inter Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]; rw [← inter_assoc]; rw [inter_eq_self_of_subset_left (Ioi_subset_Ioi hm)]
  simp_rw [univ_pi_update i₀ _ _ fun i z => Ioc z (y i), ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← inte

Depends on / 依赖: Ioi_inter_Iic, Ioi_subset_Ioi, inter_assoc, inter_eq_self_of_subset_left, pi_inter_compl, simp_rw, singleton_pi, univ_pi_update
-/
theorem pi_univ_Ioc_update_left {x y : forall i, α i} {i₀ : ι} {m : α i₀} (hm : x i₀ <= m) :
    (pi univ fun i => Ioc (update x i₀ m i) (y i)) =
      { z | m < z i₀ } inter pi univ fun i => Ioc (x i) (y i) := by
  have : Ioc m (y i₀) = Ioi m inter Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]; rw [← inter_assoc]; rw [inter_eq_self_of_subset_left (Ioi_subset_Ioi hm)]
  simp_rw [univ_pi_update i₀ _ _ fun i z => Ioc z (y i), ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← inter_assoc, this]
  rfl

/--
theorem `pi_univ_Ioc_update_right` / 定理 `pi_univ_Ioc_update_right`

English:
theorem pi_univ_Ioc_update_right
  given: {x y : forall i, α i} {i₀ : ι} {m : α i₀} (hm : m <= y i₀)
  proof: by
  have : Ioc (x i₀) m = Iic m inter Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]; rw [inter_left_comm]; rw [inter_eq_self_of_subset_left (Iic_subset_Iic.2 hm)]
  simp_rw [univ_pi_update i₀ y m fun i z => Ioc (x i) z, ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← 

中文:
定理 pi_univ_Ioc_update_right
  条件: {x y : 对任意 i, α i} {i₀ : ι} {m : α i₀} (hm : m <= y i₀)
  证明: by
  have : Ioc (x i₀) m = Iic m inter Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]; rw [inter_left_comm]; rw [inter_eq_self_of_subset_left (Iic_subset_Iic.2 hm)]
  simp_rw [univ_pi_update i₀ y m fun i z => Ioc (x i) z, ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← 

Depends on / 依赖: Iic_subset_Iic, Ioi_inter_Iic, inter_assoc, inter_eq_self_of_subset_left, inter_left_comm, pi_inter_compl, simp_rw, singleton_pi, univ_pi_update
-/
theorem pi_univ_Ioc_update_right {x y : forall i, α i} {i₀ : ι} {m : α i₀} (hm : m <= y i₀) :
    (pi univ fun i => Ioc (x i) (update y i₀ m i)) =
      { z | z i₀ <= m } inter pi univ fun i => Ioc (x i) (y i) := by
  have : Ioc (x i₀) m = Iic m inter Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic]; rw [← Ioi_inter_Iic]; rw [inter_left_comm]; rw [inter_eq_self_of_subset_left (Iic_subset_Iic.2 hm)]
  simp_rw [univ_pi_update i₀ y m fun i z => Ioc (x i) z, ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← inter_assoc, this]
  rfl

/--
theorem `disjoint_pi_univ_Ioc_update_left_right` / 定理 `disjoint_pi_univ_Ioc_update_left_right`

English:
theorem disjoint_pi_univ_Ioc_update_left_right
  given: {x y : forall i, α i} {i₀ : ι} {m : α i₀}
  proof: by
  rw [disjoint_left]
  rintro z h₁ h₂
  refine (h₁ i₀ (mem_univ _)).2.not_gt ?_
  simpa only [Function.update_self] using (h₂ i₀ (mem_univ _)).1

中文:
定理 disjoint_pi_univ_Ioc_update_left_right
  条件: {x y : 对任意 i, α i} {i₀ : ι} {m : α i₀}
  证明: by
  rw [disjoint_left]
  rintro z h₁ h₂
  refine (h₁ i₀ (mem_univ _)).2.not_gt ?_
  simpa only [Function.update_self] using (h₂ i₀ (mem_univ _)).1

Depends on / 依赖: Function, Function.update_self, disjoint_left, mem_univ, not_gt, update_self
-/
theorem disjoint_pi_univ_Ioc_update_left_right {x y : forall i, α i} {i₀ : ι} {m : α i₀} :
    Disjoint (pi univ fun i => Ioc (x i) (update y i₀ m i))
    (pi univ fun i => Ioc (update x i₀ m i) (y i)) := by
  rw [disjoint_left]
  rintro z h₁ h₂
  refine (h₁ i₀ (mem_univ _)).2.not_gt ?_
  simpa only [Function.update_self] using (h₂ i₀ (mem_univ _)).1

end PiPreorder

section PiPartialOrder

variable [DecidableEq ι] [forall i, PartialOrder (α i)]

-- Porting note: Dot notation on `Function.update` broke
/--
theorem `image_update_Icc` / 定理 `image_update_Icc`

English:
theorem image_update_Icc
  given: (f : forall i, α i) (i : ι) (a b : α i)
  proof: by
  ext x
  rw [← Set.pi_univ_Icc]
  refine ⟨?_, fun h => ⟨x i, ?_, ?_⟩⟩
  · rintro ⟨c, hc, rfl⟩
    simpa [update_le_update_iff]
  · simpa only [Function.update_self] using! h i (mem_univ i)
  · ext j
    obtain rfl | hij := eq_or_ne i j
    · exact Function.update_self ..
    · simpa only [Functi

中文:
定理 image_update_Icc
  条件: (f : 对任意 i, α i) (i : ι) (a b : α i)
  证明: by
  ext x
  rw [← Set.pi_univ_Icc]
  refine ⟨?_, fun h => ⟨x i, ?_, ?_⟩⟩
  · rintro ⟨c, hc, rfl⟩
    simpa [update_le_update_iff]
  · simpa only [Function.update_self] using! h i (mem_univ i)
  · ext j
    obtain rfl | hij := eq_or_ne i j
    · exact Function.update_self ..
    · simpa only [Functi

Depends on / 依赖: Function, Function.update_of_ne, Function.update_self, Set.pi_univ_Icc, eq_or_ne, hij.symm, le_antisymm_iff, mem_univ, pi_univ_Icc, update_le_update_iff, update_of_ne, update_self
-/
theorem image_update_Icc (f : forall i, α i) (i : ι) (a b : α i) :
    update f i '' Icc a b = Icc (update f i a) (update f i b) := by
  ext x
  rw [← Set.pi_univ_Icc]
  refine ⟨?_, fun h => ⟨x i, ?_, ?_⟩⟩
  · rintro ⟨c, hc, rfl⟩
    simpa [update_le_update_iff]
  · simpa only [Function.update_self] using! h i (mem_univ i)
  · ext j
    obtain rfl | hij := eq_or_ne i j
    · exact Function.update_self ..
    · simpa only [Function.update_of_ne hij.symm, le_antisymm_iff] using! h j (mem_univ j)

/--
theorem `image_update_Ico` / 定理 `image_update_Ico`

English:
theorem image_update_Ico
  given: (f : forall i, α i) (i : ι) (a b : α i)
  proof: by
  rw [← Icc_sdiff_right]; rw [← Icc_sdiff_right]; rw [image_sdiff (update_injective _ _)]; rw [image_singleton]; rw [image_update_Icc]

中文:
定理 image_update_Ico
  条件: (f : 对任意 i, α i) (i : ι) (a b : α i)
  证明: by
  rw [← Icc_sdiff_right]; rw [← Icc_sdiff_right]; rw [image_sdiff (update_injective _ _)]; rw [image_singleton]; rw [image_update_Icc]

Depends on / 依赖: Icc_sdiff_right, image_sdiff, image_singleton, image_update_Icc, update_injective
-/
theorem image_update_Ico (f : forall i, α i) (i : ι) (a b : α i) :
    update f i '' Ico a b = Ico (update f i a) (update f i b) := by
  rw [← Icc_sdiff_right]; rw [← Icc_sdiff_right]; rw [image_sdiff (update_injective _ _)]; rw [image_singleton]; rw [image_update_Icc]

/--
theorem `image_update_Ioc` / 定理 `image_update_Ioc`

English:
theorem image_update_Ioc
  given: (f : forall i, α i) (i : ι) (a b : α i)
  proof: by
  rw [← Icc_sdiff_left]; rw [← Icc_sdiff_left]; rw [image_sdiff (update_injective _ _)]; rw [image_singleton]; rw [image_update_Icc]

中文:
定理 image_update_Ioc
  条件: (f : 对任意 i, α i) (i : ι) (a b : α i)
  证明: by
  rw [← Icc_sdiff_left]; rw [← Icc_sdiff_left]; rw [image_sdiff (update_injective _ _)]; rw [image_singleton]; rw [image_update_Icc]

Depends on / 依赖: Icc_sdiff_left, image_sdiff, image_singleton, image_update_Icc, update_injective
-/
theorem image_update_Ioc (f : forall i, α i) (i : ι) (a b : α i) :
    update f i '' Ioc a b = Ioc (update f i a) (update f i b) := by
  rw [← Icc_sdiff_left]; rw [← Icc_sdiff_left]; rw [image_sdiff (update_injective _ _)]; rw [image_singleton]; rw [image_update_Icc]

/--
theorem `image_update_Ioo` / 定理 `image_update_Ioo`

English:
theorem image_update_Ioo
  given: (f : forall i, α i) (i : ι) (a b : α i)
  proof: by
  rw [← Ico_sdiff_left]; rw [← Ico_sdiff_left]; rw [image_sdiff (update_injective _ _)]; rw [image_singleton]; rw [image_update_Ico]

中文:
定理 image_update_Ioo
  条件: (f : 对任意 i, α i) (i : ι) (a b : α i)
  证明: by
  rw [← Ico_sdiff_left]; rw [← Ico_sdiff_left]; rw [image_sdiff (update_injective _ _)]; rw [image_singleton]; rw [image_update_Ico]

Depends on / 依赖: Ico_sdiff_left, image_sdiff, image_singleton, image_update_Ico, update_injective
-/
theorem image_update_Ioo (f : forall i, α i) (i : ι) (a b : α i) :
    update f i '' Ioo a b = Ioo (update f i a) (update f i b) := by
  rw [← Ico_sdiff_left]; rw [← Ico_sdiff_left]; rw [image_sdiff (update_injective _ _)]; rw [image_singleton]; rw [image_update_Ico]

/--
theorem `image_update_Icc_left` / 定理 `image_update_Icc_left`

English:
theorem image_update_Icc_left
  given: (f : forall i, α i) (i : ι) (a : α i)
  proof: by simpa using image_update_Icc f i a (f i)

中文:
定理 image_update_Icc_left
  条件: (f : 对任意 i, α i) (i : ι) (a : α i)
  证明: by simpa using image_update_Icc f i a (f i)

Depends on / 依赖: image_update_Icc
-/
theorem image_update_Icc_left (f : forall i, α i) (i : ι) (a : α i) :
    update f i '' Icc a (f i) = Icc (update f i a) f := by simpa using image_update_Icc f i a (f i)

/--
theorem `image_update_Ico_left` / 定理 `image_update_Ico_left`

English:
theorem image_update_Ico_left
  given: (f : forall i, α i) (i : ι) (a : α i)
  proof: by simpa using image_update_Ico f i a (f i)

中文:
定理 image_update_Ico_left
  条件: (f : 对任意 i, α i) (i : ι) (a : α i)
  证明: by simpa using image_update_Ico f i a (f i)

Depends on / 依赖: image_update_Ico
-/
theorem image_update_Ico_left (f : forall i, α i) (i : ι) (a : α i) :
    update f i '' Ico a (f i) = Ico (update f i a) f := by simpa using image_update_Ico f i a (f i)

/--
theorem `image_update_Ioc_left` / 定理 `image_update_Ioc_left`

English:
theorem image_update_Ioc_left
  given: (f : forall i, α i) (i : ι) (a : α i)
  proof: by simpa using image_update_Ioc f i a (f i)

中文:
定理 image_update_Ioc_left
  条件: (f : 对任意 i, α i) (i : ι) (a : α i)
  证明: by simpa using image_update_Ioc f i a (f i)

Depends on / 依赖: image_update_Ioc
-/
theorem image_update_Ioc_left (f : forall i, α i) (i : ι) (a : α i) :
    update f i '' Ioc a (f i) = Ioc (update f i a) f := by simpa using image_update_Ioc f i a (f i)

/--
theorem `image_update_Ioo_left` / 定理 `image_update_Ioo_left`

English:
theorem image_update_Ioo_left
  given: (f : forall i, α i) (i : ι) (a : α i)
  proof: by simpa using image_update_Ioo f i a (f i)

中文:
定理 image_update_Ioo_left
  条件: (f : 对任意 i, α i) (i : ι) (a : α i)
  证明: by simpa using image_update_Ioo f i a (f i)

Depends on / 依赖: image_update_Ioo
-/
theorem image_update_Ioo_left (f : forall i, α i) (i : ι) (a : α i) :
    update f i '' Ioo a (f i) = Ioo (update f i a) f := by simpa using image_update_Ioo f i a (f i)

/--
theorem `image_update_Icc_right` / 定理 `image_update_Icc_right`

English:
theorem image_update_Icc_right
  given: (f : forall i, α i) (i : ι) (b : α i)
  proof: by simpa using image_update_Icc f i (f i) b

中文:
定理 image_update_Icc_right
  条件: (f : 对任意 i, α i) (i : ι) (b : α i)
  证明: by simpa using image_update_Icc f i (f i) b

Depends on / 依赖: image_update_Icc
-/
theorem image_update_Icc_right (f : forall i, α i) (i : ι) (b : α i) :
    update f i '' Icc (f i) b = Icc f (update f i b) := by simpa using image_update_Icc f i (f i) b

/--
theorem `image_update_Ico_right` / 定理 `image_update_Ico_right`

English:
theorem image_update_Ico_right
  given: (f : forall i, α i) (i : ι) (b : α i)
  proof: by simpa using image_update_Ico f i (f i) b

中文:
定理 image_update_Ico_right
  条件: (f : 对任意 i, α i) (i : ι) (b : α i)
  证明: by simpa using image_update_Ico f i (f i) b

Depends on / 依赖: image_update_Ico
-/
theorem image_update_Ico_right (f : forall i, α i) (i : ι) (b : α i) :
    update f i '' Ico (f i) b = Ico f (update f i b) := by simpa using image_update_Ico f i (f i) b

/--
theorem `image_update_Ioc_right` / 定理 `image_update_Ioc_right`

English:
theorem image_update_Ioc_right
  given: (f : forall i, α i) (i : ι) (b : α i)
  proof: by simpa using image_update_Ioc f i (f i) b

中文:
定理 image_update_Ioc_right
  条件: (f : 对任意 i, α i) (i : ι) (b : α i)
  证明: by simpa using image_update_Ioc f i (f i) b

Depends on / 依赖: image_update_Ioc
-/
theorem image_update_Ioc_right (f : forall i, α i) (i : ι) (b : α i) :
    update f i '' Ioc (f i) b = Ioc f (update f i b) := by simpa using image_update_Ioc f i (f i) b

/--
theorem `image_update_Ioo_right` / 定理 `image_update_Ioo_right`

English:
theorem image_update_Ioo_right
  given: (f : forall i, α i) (i : ι) (b : α i)
  proof: by simpa using image_update_Ioo f i (f i) b

中文:
定理 image_update_Ioo_right
  条件: (f : 对任意 i, α i) (i : ι) (b : α i)
  证明: by simpa using image_update_Ioo f i (f i) b

Depends on / 依赖: image_update_Ioo
-/
theorem image_update_Ioo_right (f : forall i, α i) (i : ι) (b : α i) :
    update f i '' Ioo (f i) b = Ioo f (update f i b) := by simpa using image_update_Ioo f i (f i) b

variable [forall i, One (α i)]

@[to_additive]
/--
theorem `image_mulSingle_Icc` / 定理 `image_mulSingle_Icc`

English:
theorem image_mulSingle_Icc
  given: (i : ι) (a b : α i)
  proof: image_update_Icc _ _ _ _

@[to_additive]

中文:
定理 image_mulSingle_Icc
  条件: (i : ι) (a b : α i)
  证明: image_update_Icc _ _ _ _

@[to_additive]

Depends on / 依赖: image_update_Icc
-/
theorem image_mulSingle_Icc (i : ι) (a b : α i) :
    Pi.mulSingle i '' Icc a b = Icc (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Icc _ _ _ _

@[to_additive]
/--
theorem `image_mulSingle_Ico` / 定理 `image_mulSingle_Ico`

English:
theorem image_mulSingle_Ico
  given: (i : ι) (a b : α i)
  proof: image_update_Ico _ _ _ _

@[to_additive]

中文:
定理 image_mulSingle_Ico
  条件: (i : ι) (a b : α i)
  证明: image_update_Ico _ _ _ _

@[to_additive]

Depends on / 依赖: image_update_Ico
-/
theorem image_mulSingle_Ico (i : ι) (a b : α i) :
    Pi.mulSingle i '' Ico a b = Ico (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Ico _ _ _ _

@[to_additive]
/--
theorem `image_mulSingle_Ioc` / 定理 `image_mulSingle_Ioc`

English:
theorem image_mulSingle_Ioc
  given: (i : ι) (a b : α i)
  proof: image_update_Ioc _ _ _ _

@[to_additive]

中文:
定理 image_mulSingle_Ioc
  条件: (i : ι) (a b : α i)
  证明: image_update_Ioc _ _ _ _

@[to_additive]

Depends on / 依赖: image_update_Ioc
-/
theorem image_mulSingle_Ioc (i : ι) (a b : α i) :
    Pi.mulSingle i '' Ioc a b = Ioc (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Ioc _ _ _ _

@[to_additive]
/--
theorem `image_mulSingle_Ioo` / 定理 `image_mulSingle_Ioo`

English:
theorem image_mulSingle_Ioo
  given: (i : ι) (a b : α i)
  proof: image_update_Ioo _ _ _ _

@[to_additive]

中文:
定理 image_mulSingle_Ioo
  条件: (i : ι) (a b : α i)
  证明: image_update_Ioo _ _ _ _

@[to_additive]

Depends on / 依赖: image_update_Ioo
-/
theorem image_mulSingle_Ioo (i : ι) (a b : α i) :
    Pi.mulSingle i '' Ioo a b = Ioo (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Ioo _ _ _ _

@[to_additive]
/--
theorem `image_mulSingle_Icc_left` / 定理 `image_mulSingle_Icc_left`

English:
theorem image_mulSingle_Icc_left
  given: (i : ι) (a : α i)
  proof: image_update_Icc_left _ _ _

@[to_additive]

中文:
定理 image_mulSingle_Icc_left
  条件: (i : ι) (a : α i)
  证明: image_update_Icc_left _ _ _

@[to_additive]

Depends on / 依赖: image_update_Icc_left
-/
theorem image_mulSingle_Icc_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Icc a 1 = Icc (Pi.mulSingle i a) 1 :=
  image_update_Icc_left _ _ _

@[to_additive]
/--
theorem `image_mulSingle_Ico_left` / 定理 `image_mulSingle_Ico_left`

English:
theorem image_mulSingle_Ico_left
  given: (i : ι) (a : α i)
  proof: image_update_Ico_left _ _ _

@[to_additive]

中文:
定理 image_mulSingle_Ico_left
  条件: (i : ι) (a : α i)
  证明: image_update_Ico_left _ _ _

@[to_additive]

Depends on / 依赖: image_update_Ico_left
-/
theorem image_mulSingle_Ico_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Ico a 1 = Ico (Pi.mulSingle i a) 1 :=
  image_update_Ico_left _ _ _

@[to_additive]
/--
theorem `image_mulSingle_Ioc_left` / 定理 `image_mulSingle_Ioc_left`

English:
theorem image_mulSingle_Ioc_left
  given: (i : ι) (a : α i)
  proof: image_update_Ioc_left _ _ _

@[to_additive]

中文:
定理 image_mulSingle_Ioc_left
  条件: (i : ι) (a : α i)
  证明: image_update_Ioc_left _ _ _

@[to_additive]

Depends on / 依赖: Ideal.mul_mem_mul, Ideal.toCotangent_eq_zero, Ideal.toCotangent_surjective, image_update_Ioc_left, map_smul, mul_mem_mul, pow_two, toCotangent_eq_zero, toCotangent_surjective
-/
theorem image_mulSingle_Ioc_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Ioc a 1 = Ioc (Pi.mulSingle i a) 1 :=
  image_update_Ioc_left _ _ _

@[to_additive]
/--
theorem `image_mulSingle_Ioo_left` / 定理 `image_mulSingle_Ioo_left`

English:
theorem image_mulSingle_Ioo_left
  given: (i : ι) (a : α i)
  proof: image_update_Ioo_left _ _ _

@[to_additive]

中文:
定理 image_mulSingle_Ioo_left
  条件: (i : ι) (a : α i)
  证明: image_update_Ioo_left _ _ _

@[to_additive]

Depends on / 依赖: image_update_Ioo_left
-/
theorem image_mulSingle_Ioo_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Ioo a 1 = Ioo (Pi.mulSingle i a) 1 :=
  image_update_Ioo_left _ _ _

@[to_additive]
/--
theorem `image_mulSingle_Icc_right` / 定理 `image_mulSingle_Icc_right`

English:
theorem image_mulSingle_Icc_right
  given: (i : ι) (b : α i)
  proof: image_update_Icc_right _ _ _

@[to_additive]

中文:
定理 image_mulSingle_Icc_right
  条件: (i : ι) (b : α i)
  证明: image_update_Icc_right _ _ _

@[to_additive]

Depends on / 依赖: image_update_Icc_right
-/
theorem image_mulSingle_Icc_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Icc 1 b = Icc 1 (Pi.mulSingle i b) :=
  image_update_Icc_right _ _ _

@[to_additive]
/--
theorem `image_mulSingle_Ico_right` / 定理 `image_mulSingle_Ico_right`

English:
theorem image_mulSingle_Ico_right
  given: (i : ι) (b : α i)
  proof: image_update_Ico_right _ _ _

@[to_additive]

中文:
定理 image_mulSingle_Ico_right
  条件: (i : ι) (b : α i)
  证明: image_update_Ico_right _ _ _

@[to_additive]

Depends on / 依赖: image_update_Ico_right
-/
theorem image_mulSingle_Ico_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Ico 1 b = Ico 1 (Pi.mulSingle i b) :=
  image_update_Ico_right _ _ _

@[to_additive]
/--
theorem `image_mulSingle_Ioc_right` / 定理 `image_mulSingle_Ioc_right`

English:
theorem image_mulSingle_Ioc_right
  given: (i : ι) (b : α i)
  proof: image_update_Ioc_right _ _ _

@[to_additive]

中文:
定理 image_mulSingle_Ioc_right
  条件: (i : ι) (b : α i)
  证明: image_update_Ioc_right _ _ _

@[to_additive]

Depends on / 依赖: image_update_Ioc_right
-/
theorem image_mulSingle_Ioc_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Ioc 1 b = Ioc 1 (Pi.mulSingle i b) :=
  image_update_Ioc_right _ _ _

@[to_additive]
/--
theorem `image_mulSingle_Ioo_right` / 定理 `image_mulSingle_Ioo_right`

English:
theorem image_mulSingle_Ioo_right
  given: (i : ι) (b : α i)
  proof: image_update_Ioo_right _ _ _

中文:
定理 image_mulSingle_Ioo_right
  条件: (i : ι) (b : α i)
  证明: image_update_Ioo_right _ _ _

Depends on / 依赖: image_update_Ioo_right
-/
theorem image_mulSingle_Ioo_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Ioo 1 b = Ioo 1 (Pi.mulSingle i b) :=
  image_update_Ioo_right _ _ _

end PiPartialOrder

section PiLattice

variable [forall i, Lattice (α i)]

@[simp]
/--
theorem `pi_univ_uIcc` / 定理 `pi_univ_uIcc`

English:
theorem pi_univ_uIcc
  given: (a b : forall i, α i)
  statement: (pi univ fun i => uIcc (a i) (b i)) = uIcc a b
  proof: pi_univ_Icc _ _

中文:
定理 pi_univ_uIcc
  条件: (a b : 对任意 i, α i)
  结论: (pi univ fun i => uIcc (a i) (b i)) = uIcc a b
  证明: pi_univ_Icc _ _

Depends on / 依赖: pi_univ_Icc
-/
theorem pi_univ_uIcc (a b : forall i, α i) : (pi univ fun i => uIcc (a i) (b i)) = uIcc a b :=
  pi_univ_Icc _ _

variable [DecidableEq ι]

/--
theorem `image_update_uIcc` / 定理 `image_update_uIcc`

English:
theorem image_update_uIcc
  given: (f : forall i, α i) (i : ι) (a b : α i)
  proof: (image_update_Icc _ _ _ _).trans by simp_rw [uIcc, update_sup, update_inf]

中文:
定理 image_update_uIcc
  条件: (f : 对任意 i, α i) (i : ι) (a b : α i)
  证明: (image_update_Icc _ _ _ _).trans by simp_rw [uIcc, update_sup, update_inf]

Depends on / 依赖: image_update_Icc, simp_rw, update_inf, update_sup
-/
theorem image_update_uIcc (f : forall i, α i) (i : ι) (a b : α i) :
    update f i '' uIcc a b = uIcc (update f i a) (update f i b) :=
(image_update_Icc _ _ _ _).trans by simp_rw [uIcc, update_sup, update_inf]

/--
theorem `image_update_uIcc_left` / 定理 `image_update_uIcc_left`

English:
theorem image_update_uIcc_left
  given: (f : forall i, α i) (i : ι) (a : α i)
  proof: by
  simpa using image_update_uIcc f i a (f i)

中文:
定理 image_update_uIcc_left
  条件: (f : 对任意 i, α i) (i : ι) (a : α i)
  证明: by
  simpa using image_update_uIcc f i a (f i)

Depends on / 依赖: image_update_uIcc
-/
theorem image_update_uIcc_left (f : forall i, α i) (i : ι) (a : α i) :
    update f i '' uIcc a (f i) = uIcc (update f i a) f := by
  simpa using image_update_uIcc f i a (f i)

/--
theorem `image_update_uIcc_right` / 定理 `image_update_uIcc_right`

English:
theorem image_update_uIcc_right
  given: (f : forall i, α i) (i : ι) (b : α i)
  proof: by
  simpa using image_update_uIcc f i (f i) b

中文:
定理 image_update_uIcc_right
  条件: (f : 对任意 i, α i) (i : ι) (b : α i)
  证明: by
  simpa using image_update_uIcc f i (f i) b

Depends on / 依赖: image_update_uIcc
-/
theorem image_update_uIcc_right (f : forall i, α i) (i : ι) (b : α i) :
    update f i '' uIcc (f i) b = uIcc f (update f i b) := by
  simpa using image_update_uIcc f i (f i) b

variable [forall i, One (α i)]

@[to_additive]
/--
theorem `image_mulSingle_uIcc` / 定理 `image_mulSingle_uIcc`

English:
theorem image_mulSingle_uIcc
  given: (i : ι) (a b : α i)
  proof: image_update_uIcc _ _ _ _

@[to_additive]

中文:
定理 image_mulSingle_uIcc
  条件: (i : ι) (a b : α i)
  证明: image_update_uIcc _ _ _ _

@[to_additive]

Depends on / 依赖: image_update_uIcc
-/
theorem image_mulSingle_uIcc (i : ι) (a b : α i) :
    Pi.mulSingle i '' uIcc a b = uIcc (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_uIcc _ _ _ _

@[to_additive]
/--
theorem `image_mulSingle_uIcc_left` / 定理 `image_mulSingle_uIcc_left`

English:
theorem image_mulSingle_uIcc_left
  given: (i : ι) (a : α i)
  proof: image_update_uIcc_left _ _ _

@[to_additive]

中文:
定理 image_mulSingle_uIcc_left
  条件: (i : ι) (a : α i)
  证明: image_update_uIcc_left _ _ _

@[to_additive]

Depends on / 依赖: image_update_uIcc_left
-/
theorem image_mulSingle_uIcc_left (i : ι) (a : α i) :
    Pi.mulSingle i '' uIcc a 1 = uIcc (Pi.mulSingle i a) 1 :=
  image_update_uIcc_left _ _ _

@[to_additive]
/--
theorem `image_mulSingle_uIcc_right` / 定理 `image_mulSingle_uIcc_right`

English:
theorem image_mulSingle_uIcc_right
  given: (i : ι) (b : α i)
  proof: image_update_uIcc_right _ _ _

中文:
定理 image_mulSingle_uIcc_right
  条件: (i : ι) (b : α i)
  证明: image_update_uIcc_right _ _ _

Depends on / 依赖: image_update_uIcc_right
-/
theorem image_mulSingle_uIcc_right (i : ι) (b : α i) :
    Pi.mulSingle i '' uIcc 1 b = uIcc 1 (Pi.mulSingle i b) :=
  image_update_uIcc_right _ _ _

end PiLattice

variable [DecidableEq ι] [forall i, LinearOrder (α i)]

open Function (update)

/--
theorem `pi_univ_Ioc_update_union` / 定理 `pi_univ_Ioc_update_union`

English:
theorem pi_univ_Ioc_update_union
  given: (x y : forall i, α i) (i₀ : ι) (m : α i₀) (hm : m in Icc (x i₀) (y i₀))
  proof: by
  simp_rw [pi_univ_Ioc_update_left hm.1, pi_univ_Ioc_update_right hm.2, ← union_inter_distrib_right,
    ← ofPred_or, le_or_gt, ofPred_true, univ_inter]

中文:
定理 pi_univ_Ioc_update_union
  条件: (x y : 对任意 i, α i) (i₀ : ι) (m : α i₀) (hm : m in Icc (x i₀) (y i₀))
  证明: by
  simp_rw [pi_univ_Ioc_update_left hm.1, pi_univ_Ioc_update_right hm.2, ← union_inter_distrib_right,
    ← ofPred_or, le_or_gt, ofPred_true, univ_inter]

Depends on / 依赖: le_or_gt, ofPred_or, ofPred_true, pi_univ_Ioc_update_left, pi_univ_Ioc_update_right, simp_rw, union_inter_distrib_right, univ_inter
-/
theorem pi_univ_Ioc_update_union (x y : forall i, α i) (i₀ : ι) (m : α i₀) (hm : m in Icc (x i₀) (y i₀)) :
    ((pi univ fun i => Ioc (x i) (update y i₀ m i)) union
        pi univ fun i => Ioc (update x i₀ m i) (y i)) =
      pi univ fun i => Ioc (x i) (y i) := by
  simp_rw [pi_univ_Ioc_update_left hm.1, pi_univ_Ioc_update_right hm.2, ← union_inter_distrib_right,
    ← ofPred_or, le_or_gt, ofPred_true, univ_inter]

/--
theorem `Icc_sdiff_pi_univ_Ioo_subset` / 定理 `Icc_sdiff_pi_univ_Ioo_subset`

English:
theorem Icc_sdiff_pi_univ_Ioo_subset
  given: (x y x' y' : forall i, α i)
  proof: by
  rintro a ⟨⟨hxa, hay⟩, ha'⟩
  simp only [mem_pi, mem_univ, mem_Ioo, true_implies, not_forall] at ha'
  simp only [le_update_iff, update_le_iff, mem_union, mem_iUnion, mem_Icc,
    hxa, hay _, hxa _, hay, ← exists_or]
  rcases ha' with ⟨w, hw⟩
  apply Exists.intro w
  cases lt_or_ge (x' w) (a w) 

中文:
定理 Icc_sdiff_pi_univ_Ioo_subset
  条件: (x y x' y' : 对任意 i, α i)
  证明: by
  rintro a ⟨⟨hxa, hay⟩, ha'⟩
  simp only [mem_pi, mem_univ, mem_Ioo, true_implies, not_forall] at ha'
  simp only [le_update_iff, update_le_iff, mem_union, mem_iUnion, mem_Icc,
    hxa, hay _, hxa _, hay, ← exists_or]
  rcases ha' with ⟨w, hw⟩
  apply Exists.intro w
  cases lt_or_ge (x' w) (a w) 

Depends on / 依赖: Exists, Exists.intro, exists_or, le_update_iff, lt_or_ge, mem_Icc, mem_Ioo, mem_iUnion, mem_pi, mem_union, mem_univ, not_forall, true_implies, update_le_iff
-/
theorem Icc_sdiff_pi_univ_Ioo_subset (x y x' y' : forall i, α i) :
    (Icc x y \ pi univ fun i => Ioo (x' i) (y' i)) subseteq
    (⋃ i : ι, Icc x (update y i (x' i))) union ⋃ i : ι, Icc (update x i (y' i)) y := by
  rintro a ⟨⟨hxa, hay⟩, ha'⟩
  simp only [mem_pi, mem_univ, mem_Ioo, true_implies, not_forall] at ha'
  simp only [le_update_iff, update_le_iff, mem_union, mem_iUnion, mem_Icc,
    hxa, hay _, hxa _, hay, ← exists_or]
  rcases ha' with ⟨w, hw⟩
  apply Exists.intro w
  cases lt_or_ge (x' w) (a w) <;> simp_all

@[deprecated (since := "2026-06-03")]
alias Icc_diff_pi_univ_Ioo_subset := Icc_sdiff_pi_univ_Ioo_subset

/--
theorem `Icc_sdiff_pi_univ_Ioc_subset` / 定理 `Icc_sdiff_pi_univ_Ioc_subset`

English:
theorem Icc_sdiff_pi_univ_Ioc_subset
  given: (x y z : forall i, α i)
  proof: by
  rintro a ⟨⟨hax, haz⟩, hay⟩
  simpa [not_and_or, hax, le_update_iff, haz _] using hay

@[deprecated (since := "2026-06-03")]
alias Icc_diff_pi_univ_Ioc_subset := Icc_sdiff_pi_univ_Ioc_subset

中文:
定理 Icc_sdiff_pi_univ_Ioc_subset
  条件: (x y z : 对任意 i, α i)
  证明: by
  rintro a ⟨⟨hax, haz⟩, hay⟩
  simpa [not_and_or, hax, le_update_iff, haz _] using hay

@[deprecated (since := "2026-06-03")]
alias Icc_diff_pi_univ_Ioc_subset := Icc_sdiff_pi_univ_Ioc_subset

Depends on / 依赖: le_update_iff, not_and_or
-/
theorem Icc_sdiff_pi_univ_Ioc_subset (x y z : forall i, α i) :
    (Icc x z \ pi univ fun i => Ioc (y i) (z i)) subseteq ⋃ i : ι, Icc x (update z i (y i)) := by
  rintro a ⟨⟨hax, haz⟩, hay⟩
  simpa [not_and_or, hax, le_update_iff, haz _] using hay

@[deprecated (since := "2026-06-03")]
alias Icc_diff_pi_univ_Ioc_subset := Icc_sdiff_pi_univ_Ioc_subset

end Set
