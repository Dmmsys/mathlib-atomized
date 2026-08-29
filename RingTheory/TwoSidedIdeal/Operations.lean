/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Jireh Loreaux, Yunzhou Xie
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Congruence.Opposite
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TwoSidedIdeal.Lattice
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Operations on two-sided ideals

This file defines operations on two-sided ideals of a ring `R`.

## Main definitions and results

- `TwoSidedIdeal.span`: the span of `s ⊆ R` is the smallest two-sided ideal containing the set.
- `TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure_nonunital`: in an associative but non-unital
  ring, an element `x` is in the two-sided ideal spanned by `s` if and only if `x` is in the closure
  of `s ∪ {y * a | y ∈ s, a ∈ R} ∪ {a * y | y ∈ s, a ∈ R} ∪ {a * y * b | y ∈ s, a, b ∈ R}` as an
  additive subgroup.
- `TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure`: in a unital and associative ring, an
  element `x` is in the two-sided ideal spanned by `s` if and only if `x` is in the closure of
  `{a*y*b | a, b ∈ R, y ∈ s}` as an additive subgroup.


- `TwoSidedIdeal.comap`: pullback of a two-sided ideal; defined as the preimage of a
  two-sided ideal.
- `TwoSidedIdeal.map`: pushforward of a two-sided ideal; defined as the span of the image of a
  two-sided ideal.
- `TwoSidedIdeal.ker`: the kernel of a ring homomorphism as a two-sided ideal.

- `TwoSidedIdeal.gc`: `fromIdeal` and `asIdeal` form a Galois connection where
  `fromIdeal : Ideal R → TwoSidedIdeal R` is defined as the smallest two-sided ideal containing an
  ideal and `asIdeal : TwoSidedIdeal R → Ideal R` the inclusion map.
-/

@[expose] public section

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
variable {F : Type*} [FunLike F R S]
variable (f : F)

/--
Definition of `span` / `span` 的定义

English:
abbreviation span
  signature: (s : Set R)
  body: { ringCon := ringConGen (fun a b => a - b in s) }

中文:
缩写 span
  签名: (s : 集合 R)
  定义体: { ringCon := ringConGen (fun a b => a - b in s) }

Depends on / 依赖: ringCon, ringConGen
-/
abbrev span (s : Set R) : TwoSidedIdeal R :=
  { ringCon := ringConGen (fun a b => a - b in s) }

/--
lemma `subset_span` / 引理 `subset_span`

English:
lemma subset_span
  given: {s : Set R}
  statement: s subseteq (span s : Set R)
  proof: by
  intro x hx
  rw [SetLike.mem_coe]; rw [mem_iff]
  exact RingConGen.Rel.of _ _ (by simpa using hx)

中文:
引理 subset_span
  条件: {s : 集合 R}
  结论: s subseteq (span s : 集合 R)
  证明: by
  intro x hx
  rw [SetLike.mem_coe]; rw [mem_iff]
  exact RingConGen.Rel.of _ _ (by simpa using hx)

Depends on / 依赖: RingConGen, RingConGen.Rel.of, SetLike, SetLike.mem_coe, mem_coe, mem_iff
-/
lemma subset_span {s : Set R} : s subseteq (span s : Set R) := by
  intro x hx
  rw [SetLike.mem_coe]; rw [mem_iff]
  exact RingConGen.Rel.of _ _ (by simpa using hx)

/--
lemma `mem_span_iff` / 引理 `mem_span_iff`

English:
lemma mem_span_iff
  given: {s : Set R} {x}
  proof: by
  refine ⟨?_, fun h => h _ subset_span⟩
  delta span
  rw [RingCon.ringConGen_eq]
  intro h I hI
  refine sInf_le (α := RingCon R) ?_ h
  intro x y hxy
  specialize hI hxy
  rwa [SetLike.mem_coe, ← rel_iff] at hI

中文:
引理 mem_span_iff
  条件: {s : 集合 R} {x}
  证明: by
  refine ⟨?_, fun h => h _ subset_span⟩
  delta span
  rw [RingCon.ringConGen_eq]
  intro h I hI
  refine sInf_le (α := RingCon R) ?_ h
  intro x y hxy
  specialize hI hxy
  rwa [SetLike.mem_coe, ← rel_iff] at hI

Depends on / 依赖: RingCon, RingCon.ringConGen_eq, SetLike, SetLike.mem_coe, mem_coe, rel_iff, ringConGen_eq, sInf_le, specialize, subset_span
-/
lemma mem_span_iff {s : Set R} {x} :
    x in span s ↔ forall (I : TwoSidedIdeal R), s subseteq I -> x in I := by
  refine ⟨?_, fun h => h _ subset_span⟩
  delta span
  rw [RingCon.ringConGen_eq]
  intro h I hI
  refine sInf_le (α := RingCon R) ?_ h
  intro x y hxy
  specialize hI hxy
  rwa [SetLike.mem_coe, ← rel_iff] at hI

/--
lemma `span_mono` / 引理 `span_mono`

English:
lemma span_mono
  given: {s t : Set R} (h : s subseteq t)
  statement: span s <= span t
  proof: by
  intro x hx
  rw [mem_span_iff] at hx ⊢
exact fun I hI => hx I h.trans hI

中文:
引理 span_mono
  条件: {s t : 集合 R} (h : s subseteq t)
  结论: span s <= span t
  证明: by
  intro x hx
  rw [mem_span_iff] at hx ⊢
exact fun I hI => hx I h.trans hI

Depends on / 依赖: h.trans, mem_span_iff
-/
lemma span_mono {s t : Set R} (h : s subseteq t) : span s <= span t := by
  intro x hx
  rw [mem_span_iff] at hx ⊢
exact fun I hI => hx I h.trans hI

/--
lemma `span_le` / 引理 `span_le`

English:
lemma span_le
  given: {s : Set R} {I : TwoSidedIdeal R}
  statement: span s <= I ↔ s subseteq I
  proof: by
  rw [TwoSidedIdeal.ringCon_le_iff]; rw [RingCon.gi _ |>.gc]
  exact ⟨fun h x hx => by aesop, fun h x y hxy => (rel_iff I x y).mpr (h hxy)⟩

中文:
引理 span_le
  条件: {s : 集合 R} {I : TwoSided理想 R}
  结论: span s <= I ↔ s subseteq I
  证明: by
  rw [TwoSidedIdeal.ringCon_le_iff]; rw [RingCon.gi _ |>.gc]
  exact ⟨fun h x hx => by aesop, fun h x y hxy => (rel_iff I x y).mpr (h hxy)⟩

Depends on / 依赖: RingCon, RingCon.gi, TwoSidedIdeal, TwoSidedIdeal.ringCon_le_iff, rel_iff, ringCon_le_iff
-/
lemma span_le {s : Set R} {I : TwoSidedIdeal R} : span s <= I ↔ s subseteq I := by
  rw [TwoSidedIdeal.ringCon_le_iff]; rw [RingCon.gi _ |>.gc]
  exact ⟨fun h x hx => by aesop, fun h x y hxy => (rel_iff I x y).mpr (h hxy)⟩

/-- An induction principle for span membership.

If `p` holds for 0 and all elements of `s`,
and is preserved under addition and left and right multiplication,
then `p` holds for all elements of the span of `s`. -/
@[elab_as_elim]
/--
theorem `span_induction` / 定理 `span_induction`

English:
theorem span_induction
  statement: {s : Set R}
  proof: let J : TwoSidedIdeal R := .mk'
    {x | exists hx, p x hx}
    ⟨zero_mem _, zero⟩
    (fun ⟨hx1, hx2⟩ ⟨hy1, hy2⟩ => ⟨add_mem _ hx1 hy1, add _ _ hx1 hy1 hx2 hy2⟩)
    (fun ⟨hx1, hx2⟩ => ⟨neg_mem _ hx1, neg _ hx1 hx2⟩)
    (fun {x' y'} ⟨hy1, hy2⟩ => ⟨mul_mem_left _ _ _ hy1, left_absorb _ _ _ hy2⟩)
    (fun {x' y'} ⟨hx1, hx2⟩ => ⟨mul_mem_right _ _ _ hx1, right_absorb _ _ _ hx2⟩)
.2 span_le (s := s) (I := J)
    (fun x hx => ⟨by simpa using (mem_span_iff.2 fun I a => a hx), by simp_all⟩) hx
.elim fun _ => by simp

中文:
定理 span_induction
  结论: {s : 集合 R}
  证明: let J : TwoSidedIdeal R := .mk'
    {x | exists hx, p x hx}
    ⟨zero_mem _, zero⟩
    (fun ⟨hx1, hx2⟩ ⟨hy1, hy2⟩ => ⟨add_mem _ hx1 hy1, add _ _ hx1 hy1 hx2 hy2⟩)
    (fun ⟨hx1, hx2⟩ => ⟨neg_mem _ hx1, neg _ hx1 hx2⟩)
    (fun {x' y'} ⟨hy1, hy2⟩ => ⟨mul_mem_left _ _ _ hy1, left_absorb _ _ _ hy2⟩)
    (fun {x' y'} ⟨hx1, hx2⟩ => ⟨mul_mem_right _ _ _ hx1, right_absorb _ _ _ hx2⟩)
.2 span_le (s := s) (I := J)
    (fun x hx => ⟨by simpa using (mem_span_iff.2 fun I a => a hx), by simp_all⟩) hx
.elim fun _ => by simp

Depends on / 依赖: TwoSidedIdeal, add_mem, left_absorb, mem_span_iff, mul_mem_left, mul_mem_right, neg_mem, right_absorb, span_le, zero_mem
-/
theorem span_induction {s : Set R}
    {p : (x : R) -> x in TwoSidedIdeal.span s -> Prop}
    (mem : forall (x) (h : x in s), p x (subset_span h))
    (zero : p 0 (zero_mem _))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem _ hx hy))
    (neg : forall x hx, p x hx -> p (-x) (neg_mem _ hx))
    (left_absorb : forall a x hx, p x hx -> p (a * x) (mul_mem_left _ _ _ hx))
    (right_absorb : forall b x hx, p x hx -> p (x * b) (mul_mem_right _ _ _ hx))
    {x : R} (hx : x in span s) : p x hx :=
  let J : TwoSidedIdeal R := .mk'
    {x | exists hx, p x hx}
    ⟨zero_mem _, zero⟩
    (fun ⟨hx1, hx2⟩ ⟨hy1, hy2⟩ => ⟨add_mem _ hx1 hy1, add _ _ hx1 hy1 hx2 hy2⟩)
    (fun ⟨hx1, hx2⟩ => ⟨neg_mem _ hx1, neg _ hx1 hx2⟩)
    (fun {x' y'} ⟨hy1, hy2⟩ => ⟨mul_mem_left _ _ _ hy1, left_absorb _ _ _ hy2⟩)
    (fun {x' y'} ⟨hx1, hx2⟩ => ⟨mul_mem_right _ _ _ hx1, right_absorb _ _ _ hx2⟩)
.2 span_le (s := s) (I := J)
    (fun x hx => ⟨by simpa using (mem_span_iff.2 fun I a => a hx), by simp_all⟩) hx
.elim fun _ => by simp

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (I : TwoSidedIdeal R)
  body: span (f '' I)

中文:
定义 map
  签名: (I : TwoSided理想 R)
  定义体: span (f '' I)
-/
def map (I : TwoSidedIdeal R) : TwoSidedIdeal S :=
  span (f '' I)

/--
lemma `map_mono` / 引理 `map_mono`

English:
lemma map_mono
  given: {I J : TwoSidedIdeal R} (h : I <= J)
  proof: span_mono Set.image_mono h

中文:
引理 map_mono
  条件: {I J : TwoSided理想 R} (h : I <= J)
  证明: span_mono Set.image_mono h

Depends on / 依赖: Set.image_mono, image_mono, span_mono
-/
lemma map_mono {I J : TwoSidedIdeal R} (h : I <= J) :
    map f I <= map f J :=
span_mono Set.image_mono h

variable [NonUnitalRingHomClass F R S]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: : TwoSidedIdeal S ->o TwoSidedIdeal R where
  body: ⟨I.ringCon.comap f⟩
  monotone' := by
    intro I J h
    rw [le_iff] at h
    intro x
    specialize @h (f x)
    simpa [mem_iff, RingCon.comap]

中文:
定义 comap
  签名: : TwoSided理想 S ->o TwoSided理想 R where
  定义体: ⟨I.ringCon.comap f⟩
  monotone' := by
    intro I J h
    rw [le_iff] at h
    intro x
    specialize @h (f x)
    simpa [mem_iff, RingCon.comap]

Depends on / 依赖: I.ringCon.comap, ringCon
-/
def comap : TwoSidedIdeal S ->o TwoSidedIdeal R where
  toFun I := ⟨I.ringCon.comap f⟩
  monotone' := by
    intro I J h
    rw [le_iff] at h
    intro x
    specialize @h (f x)
    simpa [mem_iff, RingCon.comap]

/--
lemma `comap_le_comap` / 引理 `comap_le_comap`

English:
lemma comap_le_comap
  given: {I J : TwoSidedIdeal S} (h : I <= J)
  proof: (comap f).monotone h

中文:
引理 comap_le_comap
  条件: {I J : TwoSided理想 S} (h : I <= J)
  证明: (comap f).monotone h

Depends on / 依赖: monotone
-/
lemma comap_le_comap {I J : TwoSidedIdeal S} (h : I <= J) :
    comap f I <= comap f J :=
  (comap f).monotone h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_comap` / 引理 `mem_comap`

English:
lemma mem_comap
  given: {I : TwoSidedIdeal S} {x : R}
  proof: by
  simp [comap, RingCon.comap, mem_iff]

中文:
引理 mem_comap
  条件: {I : TwoSided理想 S} {x : R}
  证明: by
  simp [comap, RingCon.comap, mem_iff]

Depends on / 依赖: RingCon, RingCon.comap, mem_iff
-/
lemma mem_comap {I : TwoSidedIdeal S} {x : R} :
    x in I.comap f ↔ f x in I := by
  simp [comap, RingCon.comap, mem_iff]

/--
Definition of `_root_.RingEquiv.mapTwoSidedIdeal` / `_root_.RingEquiv.mapTwoSidedIdeal` 的定义

English:
definition _root_.RingEquiv.mapTwoSidedIdeal
  signature: (e : R ≃+* S)
  body: OrderIso.ofHomInv (comap e.symm) (comap e) (by ext; simp [mem_comap])
    (by ext; simp [mem_comap])

中文:
定义 _root_.环等价.mapTwoSidedIdeal
  签名: (e : R ≃+* S)
  定义体: OrderIso.ofHomInv (comap e.symm) (comap e) (by ext; simp [mem_comap])
    (by ext; simp [mem_comap])

Depends on / 依赖: OrderIso, OrderIso.ofHomInv, e.symm, mem_comap, ofHomInv
-/
def _root_.RingEquiv.mapTwoSidedIdeal (e : R ≃+* S) : TwoSidedIdeal R ≃o TwoSidedIdeal S :=
  OrderIso.ofHomInv (comap e.symm) (comap e) (by ext; simp [mem_comap])
    (by ext; simp [mem_comap])

/--
lemma `_root_.RingEquiv.mapTwoSidedIdeal_apply` / 引理 `_root_.RingEquiv.mapTwoSidedIdeal_apply`

English:
lemma _root_.RingEquiv.mapTwoSidedIdeal_apply
  given: (e : R ≃+* S) (I : TwoSidedIdeal R)
  proof: rfl

中文:
引理 _root_.环等价.mapTwoSidedIdeal_apply
  条件: (e : R ≃+* S) (I : TwoSided理想 R)
  证明: rfl
-/
lemma _root_.RingEquiv.mapTwoSidedIdeal_apply (e : R ≃+* S) (I : TwoSidedIdeal R) :
    e.mapTwoSidedIdeal I = I.comap e.symm := rfl

/--
lemma `_root_.RingEquiv.mapTwoSidedIdeal_symm` / 引理 `_root_.RingEquiv.mapTwoSidedIdeal_symm`

English:
lemma _root_.RingEquiv.mapTwoSidedIdeal_symm
  given: (e : R ≃+* S)
  proof: rfl

中文:
引理 _root_.环等价.mapTwoSidedIdeal_symm
  条件: (e : R ≃+* S)
  证明: rfl
-/
lemma _root_.RingEquiv.mapTwoSidedIdeal_symm (e : R ≃+* S) :
    e.mapTwoSidedIdeal.symm = e.symm.mapTwoSidedIdeal := rfl

end NonUnitalNonAssocRing

section NonAssocRing

variable {R S T : Type*}
variable [NonAssocRing R] [NonAssocRing S] [NonAssocRing T]

/--
lemma `comap_comap` / 引理 `comap_comap`

English:
lemma comap_comap
  given: (I : TwoSidedIdeal T) (f : R ->+* S) (g : S ->+* T)
  proof: by
  ext; simp [mem_comap]

中文:
引理 comap_comap
  条件: (I : TwoSided理想 T) (f : R ->+* S) (g : S ->+* T)
  证明: by
  ext; simp [mem_comap]

Depends on / 依赖: mem_comap
-/
lemma comap_comap (I : TwoSidedIdeal T) (f : R ->+* S) (g : S ->+* T) :
    (I.comap g).comap f = I.comap (g.comp f) := by
  ext; simp [mem_comap]

end NonAssocRing

section NonUnitalRing

variable {R : Type*} [NonUnitalRing R]

open AddSubgroup in
/--
lemma `mem_span_iff_mem_addSubgroup_closure_absorbing` / 引理 `mem_span_iff_mem_addSubgroup_closure_absorbing`

English:
lemma mem_span_iff_mem_addSubgroup_closure_absorbing
  statement: {s : Set R}
  proof: by
  have h_left' {x y} (hy : y in closure s) : x * y in closure s := by
    have := (AddMonoidHom.mulLeft x).map_closure s ▸ mem_map_of_mem _ hy
    refine closure_mono ?_ this
    rintro - ⟨y, hy, rfl⟩
    exact h_left x y hy
  have h_right' {y x} (hy : y in closure s) : y * x in closure s := by
    have := (AddMonoidHom.mulRight x).map_closure s ▸ mem_map_of_mem _ hy
    refine closure_mono ?_ this
    rintro - ⟨y, hy, rfl⟩
    exact h_right y x hy
  let I : TwoSidedIdeal R := .mk' (closure s) (AddSubgroup.zero_mem _)
    (AddSubgroup.add_mem _) (AddSubgroup.neg_mem _) h_left' h_right'
  suffices z in span s ↔ z in I by simpa only [I, mem_mk', SetLike.mem_coe]
  rw [mem_span_iff]
  -- Suppose that for every ideal `J` with `s ⊆ J`, then `z ∈ J`. Apply this to `I` to get `z ∈ I`.
  refine ⟨fun h => h I fun x hx => ?mem_closure_of_forall, fun hz J hJ => ?mem_ideal_of_subset⟩
  case mem_closure_of_forall => simpa only [I, SetLike.mem_coe, mem_mk'] using subset_closure hx
  /- Conversely, suppose that `z ∈ I` and that `J` is any ideal containing `s`. Then by the
  induction principle for `AddSubgroup`, we must also have `z ∈ J`. -/
  case mem_ideal_of_subset =>
    simp only [I, SetLike.mem_coe, mem_mk'] at hz
    induction hz using closure_induction with
    | mem x hx => exact hJ hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact J.add_mem hx hy
    | neg x _ hx => exact J.neg_mem hx

中文:
引理 mem_span_iff_mem_addSubgroup_closure_absorbing
  结论: {s : 集合 R}
  证明: by
  have h_left' {x y} (hy : y in closure s) : x * y in closure s := by
    have := (AddMonoidHom.mulLeft x).map_closure s ▸ mem_map_of_mem _ hy
    refine closure_mono ?_ this
    rintro - ⟨y, hy, rfl⟩
    exact h_left x y hy
  have h_right' {y x} (hy : y in closure s) : y * x in closure s := by
    have := (AddMonoidHom.mulRight x).map_closure s ▸ mem_map_of_mem _ hy
    refine closure_mono ?_ this
    rintro - ⟨y, hy, rfl⟩
    exact h_right y x hy
  let I : TwoSidedIdeal R := .mk' (closure s) (AddSubgroup.zero_mem _)
    (AddSubgroup.add_mem _) (AddSubgroup.neg_mem _) h_left' h_right'
  suffices z in span s ↔ z in I by simpa only [I, mem_mk', SetLike.mem_coe]
  rw [mem_span_iff]
  -- Suppose that for every ideal `J` with `s ⊆ J`, then `z ∈ J`. Apply this to `I` to get `z ∈ I`.
  refine ⟨fun h => h I fun x hx => ?mem_closure_of_forall, fun hz J hJ => ?mem_ideal_of_subset⟩
  case mem_closure_of_forall => simpa only [I, SetLike.mem_coe, mem_mk'] using subset_closure hx
  /- Conversely, suppose that `z ∈ I` and that `J` is any ideal containing `s`. Then by the
  induction principle for `AddSubgroup`, we must also have `z ∈ J`. -/
  case mem_ideal_of_subset =>
    simp only [I, SetLike.mem_coe, mem_mk'] at hz
    induction hz using closure_induction with
    | mem x hx => exact hJ hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact J.add_mem hx hy
    | neg x _ hx => exact J.neg_mem hx

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, AddMonoidHom.mulRight, AddSubgrou, AddSubgroup, AddSubgroup.zero_mem, TwoSidedIdeal, closure, closure_mono, h_left, h_right, map_closure, mem_map_of_mem, mulLeft, mulRight, zero_mem
-/
lemma mem_span_iff_mem_addSubgroup_closure_absorbing {s : Set R}
    (h_left : forall x y, y in s -> x * y in s) (h_right : forall y x, y in s -> y * x in s) {z : R} :
    z in span s ↔ z in closure s := by
  have h_left' {x y} (hy : y in closure s) : x * y in closure s := by
    have := (AddMonoidHom.mulLeft x).map_closure s ▸ mem_map_of_mem _ hy
    refine closure_mono ?_ this
    rintro - ⟨y, hy, rfl⟩
    exact h_left x y hy
  have h_right' {y x} (hy : y in closure s) : y * x in closure s := by
    have := (AddMonoidHom.mulRight x).map_closure s ▸ mem_map_of_mem _ hy
    refine closure_mono ?_ this
    rintro - ⟨y, hy, rfl⟩
    exact h_right y x hy
  let I : TwoSidedIdeal R := .mk' (closure s) (AddSubgroup.zero_mem _)
    (AddSubgroup.add_mem _) (AddSubgroup.neg_mem _) h_left' h_right'
  suffices z in span s ↔ z in I by simpa only [I, mem_mk', SetLike.mem_coe]
  rw [mem_span_iff]
  -- Suppose that for every ideal `J` with `s ⊆ J`, then `z ∈ J`. Apply this to `I` to get `z ∈ I`.
  refine ⟨fun h => h I fun x hx => ?mem_closure_of_forall, fun hz J hJ => ?mem_ideal_of_subset⟩
  case mem_closure_of_forall => simpa only [I, SetLike.mem_coe, mem_mk'] using subset_closure hx
  /- Conversely, suppose that `z ∈ I` and that `J` is any ideal containing `s`. Then by the
  induction principle for `AddSubgroup`, we must also have `z ∈ J`. -/
  case mem_ideal_of_subset =>
    simp only [I, SetLike.mem_coe, mem_mk'] at hz
    induction hz using closure_induction with
    | mem x hx => exact hJ hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact J.add_mem hx hy
    | neg x _ hx => exact J.neg_mem hx

open scoped Pointwise
open Set

/--
lemma `set_mul_subset` / 引理 `set_mul_subset`

English:
lemma set_mul_subset
  given: {s : Set R} {I : TwoSidedIdeal R} (h : s subseteq I) (t : Set R)
  proof: by
  rintro - ⟨r, -, x, hx, rfl⟩
  exact mul_mem_left _ _ _ (h hx)

中文:
引理 set_mul_subset
  条件: {s : 集合 R} {I : TwoSided理想 R} (h : s subseteq I) (t : 集合 R)
  证明: by
  rintro - ⟨r, -, x, hx, rfl⟩
  exact mul_mem_left _ _ _ (h hx)

Depends on / 依赖: mul_mem_left
-/
lemma set_mul_subset {s : Set R} {I : TwoSidedIdeal R} (h : s subseteq I) (t : Set R) :
    t * s subseteq I := by
  rintro - ⟨r, -, x, hx, rfl⟩
  exact mul_mem_left _ _ _ (h hx)

/--
lemma `subset_mul_set` / 引理 `subset_mul_set`

English:
lemma subset_mul_set
  given: {s : Set R} {I : TwoSidedIdeal R} (h : s subseteq I) (t : Set R)
  proof: by
  rintro - ⟨x, hx, r, -, rfl⟩
  exact mul_mem_right _ _ _ (h hx)

中文:
引理 subset_mul_set
  条件: {s : 集合 R} {I : TwoSided理想 R} (h : s subseteq I) (t : 集合 R)
  证明: by
  rintro - ⟨x, hx, r, -, rfl⟩
  exact mul_mem_right _ _ _ (h hx)

Depends on / 依赖: mul_mem_right
-/
lemma subset_mul_set {s : Set R} {I : TwoSidedIdeal R} (h : s subseteq I) (t : Set R) :
    s * t subseteq I := by
  rintro - ⟨x, hx, r, -, rfl⟩
  exact mul_mem_right _ _ _ (h hx)

/--
lemma `mem_span_iff_mem_addSubgroup_closure_nonunital` / 引理 `mem_span_iff_mem_addSubgroup_closure_nonunital`

English:
lemma mem_span_iff_mem_addSubgroup_closure_nonunital
  given: {s : Set R} {z : R}
  proof: by
  trans z in span (s union s * univ union univ * s union univ * s * univ)
  · refine ⟨(span_mono (by simp only [Set.union_assoc, Set.subset_union_left]) ·), fun h => ?_⟩
    refine mem_span_iff.mp h (span s) ?_
    simp only [union_subset_iff, union_assoc]
    exact ⟨subset_span, subset_mul_set subset_span _, set_mul_subset subset_span _,
      subset_mul_set (set_mul_subset subset_span _) _⟩
  · refine mem_span_iff_mem_addSubgroup_closure_absorbing ?_ ?_
    · rintro x y (((hy | ⟨y, hy, r, -, rfl⟩) | ⟨r, -, y, hy, rfl⟩) |
        ⟨-, ⟨r', -, y, hy, rfl⟩, r, -, rfl⟩)
· exact .inl .inr ⟨x, mem_univ _, y, hy, rfl⟩
· exact .inr ⟨x * y, ⟨x, mem_univ _, y, hy, rfl⟩, r, mem_univ _, mul_assoc ..⟩
· exact .inl .inr ⟨x * r, mem_univ _, y, hy, mul_assoc ..⟩
· refine .inr ⟨x * r' * y, ⟨x * r', mem_univ _, y, hy, ?_⟩, ⟨r, mem_univ _, ?_⟩⟩
        all_goals simp [mul_assoc]
    · rintro y x (((hy | ⟨y, hy, r, -, rfl⟩) | ⟨r, -, y, hy, rfl⟩) |
        ⟨-, ⟨r', -, y, hy, rfl⟩, r, -, rfl⟩)
· exact .inl .inl .inr ⟨y, hy, x, mem_univ _, rfl⟩
· exact .inl .inl .inr ⟨y, hy, r * x, mem_univ _, (mul_assoc ..).symm⟩
· exact .inr ⟨r * y, ⟨r, mem_univ _, y, hy, rfl⟩, x, mem_univ _, rfl⟩
· refine .inr ⟨r' * y, ⟨r', mem_univ _, y, hy, rfl⟩, r * x, mem_univ _, ?_⟩
        simp [mul_assoc]

中文:
引理 mem_span_iff_mem_addSubgroup_closure_nonunital
  条件: {s : 集合 R} {z : R}
  证明: by
  trans z in span (s union s * univ union univ * s union univ * s * univ)
  · refine ⟨(span_mono (by simp only [Set.union_assoc, Set.subset_union_left]) ·), fun h => ?_⟩
    refine mem_span_iff.mp h (span s) ?_
    simp only [union_subset_iff, union_assoc]
    exact ⟨subset_span, subset_mul_set subset_span _, set_mul_subset subset_span _,
      subset_mul_set (set_mul_subset subset_span _) _⟩
  · refine mem_span_iff_mem_addSubgroup_closure_absorbing ?_ ?_
    · rintro x y (((hy | ⟨y, hy, r, -, rfl⟩) | ⟨r, -, y, hy, rfl⟩) |
        ⟨-, ⟨r', -, y, hy, rfl⟩, r, -, rfl⟩)
· exact .inl .inr ⟨x, mem_univ _, y, hy, rfl⟩
· exact .inr ⟨x * y, ⟨x, mem_univ _, y, hy, rfl⟩, r, mem_univ _, mul_assoc ..⟩
· exact .inl .inr ⟨x * r, mem_univ _, y, hy, mul_assoc ..⟩
· refine .inr ⟨x * r' * y, ⟨x * r', mem_univ _, y, hy, ?_⟩, ⟨r, mem_univ _, ?_⟩⟩
        all_goals simp [mul_assoc]
    · rintro y x (((hy | ⟨y, hy, r, -, rfl⟩) | ⟨r, -, y, hy, rfl⟩) |
        ⟨-, ⟨r', -, y, hy, rfl⟩, r, -, rfl⟩)
· exact .inl .inl .inr ⟨y, hy, x, mem_univ _, rfl⟩
· exact .inl .inl .inr ⟨y, hy, r * x, mem_univ _, (mul_assoc ..).symm⟩
· exact .inr ⟨r * y, ⟨r, mem_univ _, y, hy, rfl⟩, x, mem_univ _, rfl⟩
· refine .inr ⟨r' * y, ⟨r', mem_univ _, y, hy, rfl⟩, r * x, mem_univ _, ?_⟩
        simp [mul_assoc]

Depends on / 依赖: Set.subset_union_left, Set.union_assoc, mem_span_iff, mem_span_iff.mp, mem_span_iff_mem_addSubgroup_closure_absorbing, set_mul_subset, span_mono, subset_mul_set, subset_span, subset_union_left, union_assoc, union_subset_iff
-/
lemma mem_span_iff_mem_addSubgroup_closure_nonunital {s : Set R} {z : R} :
    z in span s ↔ z in AddSubgroup.closure (s union s * univ union univ * s union univ * s * univ) := by
  trans z in span (s union s * univ union univ * s union univ * s * univ)
  · refine ⟨(span_mono (by simp only [Set.union_assoc, Set.subset_union_left]) ·), fun h => ?_⟩
    refine mem_span_iff.mp h (span s) ?_
    simp only [union_subset_iff, union_assoc]
    exact ⟨subset_span, subset_mul_set subset_span _, set_mul_subset subset_span _,
      subset_mul_set (set_mul_subset subset_span _) _⟩
  · refine mem_span_iff_mem_addSubgroup_closure_absorbing ?_ ?_
    · rintro x y (((hy | ⟨y, hy, r, -, rfl⟩) | ⟨r, -, y, hy, rfl⟩) |
        ⟨-, ⟨r', -, y, hy, rfl⟩, r, -, rfl⟩)
· exact .inl .inr ⟨x, mem_univ _, y, hy, rfl⟩
· exact .inr ⟨x * y, ⟨x, mem_univ _, y, hy, rfl⟩, r, mem_univ _, mul_assoc ..⟩
· exact .inl .inr ⟨x * r, mem_univ _, y, hy, mul_assoc ..⟩
· refine .inr ⟨x * r' * y, ⟨x * r', mem_univ _, y, hy, ?_⟩, ⟨r, mem_univ _, ?_⟩⟩
        all_goals simp [mul_assoc]
    · rintro y x (((hy | ⟨y, hy, r, -, rfl⟩) | ⟨r, -, y, hy, rfl⟩) |
        ⟨-, ⟨r', -, y, hy, rfl⟩, r, -, rfl⟩)
· exact .inl .inl .inr ⟨y, hy, x, mem_univ _, rfl⟩
· exact .inl .inl .inr ⟨y, hy, r * x, mem_univ _, (mul_assoc ..).symm⟩
· exact .inr ⟨r * y, ⟨r, mem_univ _, y, hy, rfl⟩, x, mem_univ _, rfl⟩
· refine .inr ⟨r' * y, ⟨r', mem_univ _, y, hy, rfl⟩, r * x, mem_univ _, ?_⟩
        simp [mul_assoc]

end NonUnitalRing

section Ring

variable {R : Type*} [Ring R]

open scoped Pointwise in
open Set in
/--
lemma `mem_span_iff_mem_addSubgroup_closure` / 引理 `mem_span_iff_mem_addSubgroup_closure`

English:
lemma mem_span_iff_mem_addSubgroup_closure
  given: {s : Set R} {z : R}
  proof: by
  trans z in span (univ * s * univ)
  · refine ⟨(span_mono (fun x hx => ?_) ·), fun hz => ?_⟩
    · exact ⟨1 * x, ⟨1, mem_univ _, x, hx, rfl⟩, 1, mem_univ _, by simp⟩
· exact mem_span_iff.mp hz (span s) subset_mul_set (set_mul_subset subset_span _) _
  · refine mem_span_iff_mem_addSubgroup_closure_absorbing ?_ ?_
    · intro x y hy
      rw [mul_assoc] at hy ⊢
      obtain ⟨r, -, y, hy, rfl⟩ := hy
      exact ⟨x * r, mem_univ _, y, hy, mul_assoc ..⟩
    · rintro - x ⟨y, hy, r, -, rfl⟩
      exact ⟨y, hy, r * x, mem_univ _, (mul_assoc ..).symm⟩

中文:
引理 mem_span_iff_mem_addSubgroup_closure
  条件: {s : 集合 R} {z : R}
  证明: by
  trans z in span (univ * s * univ)
  · refine ⟨(span_mono (fun x hx => ?_) ·), fun hz => ?_⟩
    · exact ⟨1 * x, ⟨1, mem_univ _, x, hx, rfl⟩, 1, mem_univ _, by simp⟩
· exact mem_span_iff.mp hz (span s) subset_mul_set (set_mul_subset subset_span _) _
  · refine mem_span_iff_mem_addSubgroup_closure_absorbing ?_ ?_
    · intro x y hy
      rw [mul_assoc] at hy ⊢
      obtain ⟨r, -, y, hy, rfl⟩ := hy
      exact ⟨x * r, mem_univ _, y, hy, mul_assoc ..⟩
    · rintro - x ⟨y, hy, r, -, rfl⟩
      exact ⟨y, hy, r * x, mem_univ _, (mul_assoc ..).symm⟩

Depends on / 依赖: mem_span_iff, mem_span_iff.mp, mem_span_iff_mem_addSubgroup_closure_absorbing, mem_univ, mul_assoc, set_mul_subset, span_mono, subset_mul_set, subset_span
-/
lemma mem_span_iff_mem_addSubgroup_closure {s : Set R} {z : R} :
    z in span s ↔ z in AddSubgroup.closure (univ * s * univ) := by
  trans z in span (univ * s * univ)
  · refine ⟨(span_mono (fun x hx => ?_) ·), fun hz => ?_⟩
    · exact ⟨1 * x, ⟨1, mem_univ _, x, hx, rfl⟩, 1, mem_univ _, by simp⟩
· exact mem_span_iff.mp hz (span s) subset_mul_set (set_mul_subset subset_span _) _
  · refine mem_span_iff_mem_addSubgroup_closure_absorbing ?_ ?_
    · intro x y hy
      rw [mul_assoc] at hy ⊢
      obtain ⟨r, -, y, hy, rfl⟩ := hy
      exact ⟨x * r, mem_univ _, y, hy, mul_assoc ..⟩
    · rintro - x ⟨y, hy, r, -, rfl⟩
      exact ⟨y, hy, r * x, mem_univ _, (mul_assoc ..).symm⟩

variable (I : TwoSidedIdeal R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R I
  body: ⟨r • x.1, I.mul_mem_left _ _ x.2⟩

中文:
实例 :
  签名: 标量乘法 R I
  定义体: ⟨r • x.1, I.mul_mem_left _ _ x.2⟩

Depends on / 依赖: I.mul_mem_left, mul_mem_left
-/
instance : SMul R I where smul r x := ⟨r • x.1, I.mul_mem_left _ _ x.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Rᵐᵒᵖ I
  body: ⟨r • x.1, I.mul_mem_right _ _ x.2⟩

中文:
实例 :
  签名: 标量乘法 Rᵐᵒᵖ I
  定义体: ⟨r • x.1, I.mul_mem_right _ _ x.2⟩

Depends on / 依赖: I.mul_mem_right, mul_mem_right
-/
instance : SMul Rᵐᵒᵖ I where smul r x := ⟨r • x.1, I.mul_mem_right _ _ x.2⟩

/--
Instance `leftModule` / 实例 `leftModule`

English:
instance leftModule
  signature: : Module R I
  body: Function.Injective.module _ (coeAddMonoidHom I) Subtype.coe_injective fun _ _ => rfl

@[simp]

中文:
实例 leftModule
  签名: : 模 R I
  定义体: Function.Injective.module _ (coeAddMonoidHom I) Subtype.coe_injective fun _ _ => rfl

@[simp]

Depends on / 依赖: Function, Function.Injective.module, Injective, Subtype, Subtype.coe_injective, coeAddMonoidHom, coe_injective, module
-/
instance leftModule : Module R I :=
  Function.Injective.module _ (coeAddMonoidHom I) Subtype.coe_injective fun _ _ => rfl

@[simp]
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: {r : R} {x : I}
  statement: (r • x : R) = r * (x : R)
  proof: rfl

中文:
引理 coe_smul
  条件: {r : R} {x : I}
  结论: (r • x : R) = r * (x : R)
  证明: rfl
-/
lemma coe_smul {r : R} {x : I} : (r • x : R) = r * (x : R) := rfl

/--
Instance `rightModule` / 实例 `rightModule`

English:
instance rightModule
  signature: : Module Rᵐᵒᵖ I
  body: Function.Injective.module _ (coeAddMonoidHom I) Subtype.coe_injective fun _ _ => rfl

@[simp]

中文:
实例 rightModule
  签名: : 模 Rᵐᵒᵖ I
  定义体: Function.Injective.module _ (coeAddMonoidHom I) Subtype.coe_injective fun _ _ => rfl

@[simp]

Depends on / 依赖: Function, Function.Injective.module, Injective, Subtype, Subtype.coe_injective, coeAddMonoidHom, coe_injective, module
-/
instance rightModule : Module Rᵐᵒᵖ I :=
  Function.Injective.module _ (coeAddMonoidHom I) Subtype.coe_injective fun _ _ => rfl

@[simp]
/--
lemma `coe_mop_smul` / 引理 `coe_mop_smul`

English:
lemma coe_mop_smul
  given: {r : Rᵐᵒᵖ} {x : I}
  statement: (r • x : R) = (x : R) * r.unop
  proof: rfl

中文:
引理 coe_mop_smul
  条件: {r : Rᵐᵒᵖ} {x : I}
  结论: (r • x : R) = (x : R) * r.unop
  证明: rfl
-/
lemma coe_mop_smul {r : Rᵐᵒᵖ} {x : I} : (r • x : R) = (x : R) * r.unop := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass R Rᵐᵒᵖ I
  body: Subtype.ext smul_comm r s x.1

中文:
实例 :
  签名: 标量交换类 R Rᵐᵒᵖ I
  定义体: Subtype.ext smul_comm r s x.1

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance : SMulCommClass R Rᵐᵒᵖ I where
smul_comm r s x := Subtype.ext smul_comm r s x.1

/--
For any `I : RingCon R`, when we view it as an ideal, `I.subtype` is the injective `R`-linear map
`I → R`.
-/
@[simps]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : I ->ₗ[R] R where
  body: x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 subtype
  签名: : I ->ₗ[R] R where
  定义体: x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def subtype : I ->ₗ[R] R where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
theorem `subtype_injective` / 定理 `subtype_injective`

English:
theorem subtype_injective
  statement: Function.Injective (subtype I)
  proof: Subtype.coe_injective

@[simp]

中文:
定理 subtype_injective
  结论: 函数.单射 (subtype I)
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem subtype_injective : Function.Injective (subtype I) :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: ⇑(subtype I) = Subtype.val
  proof: rfl

中文:
定理 coe_subtype
  结论: ⇑(subtype I) = 子类型.val
  证明: rfl
-/
theorem coe_subtype : ⇑(subtype I) = Subtype.val :=
  rfl

/--
For any `RingCon R`, when we view it as an ideal in `Rᵒᵖ`, `subtype` is the injective `Rᵐᵒᵖ`-linear
map `I → Rᵐᵒᵖ`.
-/
@[simps]
/--
Definition of `subtypeMop` / `subtypeMop` 的定义

English:
definition subtypeMop
  signature: : I ->ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ where
  body: MulOpposite.op x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 subtypeMop
  签名: : I ->ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ where
  定义体: MulOpposite.op x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: MulOpposite, MulOpposite.op
-/
def subtypeMop : I ->ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ where
  toFun x := MulOpposite.op x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
theorem `subtypeMop_injective` / 定理 `subtypeMop_injective`

English:
theorem subtypeMop_injective
  statement: Function.Injective (subtypeMop I)
  proof: MulOpposite.op_injective.comp Subtype.coe_injective

中文:
定理 subtypeMop_injective
  结论: 函数.单射 (subtypeMop I)
  证明: MulOpposite.op_injective.comp Subtype.coe_injective

Depends on / 依赖: MulOpposite, MulOpposite.op_injective.comp, Subtype, Subtype.coe_injective, coe_injective, op_injective
-/
theorem subtypeMop_injective : Function.Injective (subtypeMop I) :=
  MulOpposite.op_injective.comp Subtype.coe_injective

/--
Definition of `fromIdeal` / `fromIdeal` 的定义

English:
definition fromIdeal
  signature: : Ideal R ->o TwoSidedIdeal R where
  body: span I
  monotone' _ _ := span_mono

中文:
定义 fromIdeal
  签名: : 理想 R ->o TwoSided理想 R where
  定义体: span I
  monotone' _ _ := span_mono
-/
def fromIdeal : Ideal R ->o TwoSidedIdeal R where
  toFun I := span I
  monotone' _ _ := span_mono

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_fromIdeal` / 引理 `mem_fromIdeal`

English:
lemma mem_fromIdeal
  given: {I : Ideal R} {x : R}
  proof: by simp [fromIdeal]

中文:
引理 mem_fromIdeal
  条件: {I : 理想 R} {x : R}
  证明: by simp [fromIdeal]

Depends on / 依赖: fromIdeal
-/
lemma mem_fromIdeal {I : Ideal R} {x : R} :
    x in fromIdeal I ↔ x in span I := by simp [fromIdeal]

/--
Definition of `asIdeal` / `asIdeal` 的定义

English:
definition asIdeal
  signature: : TwoSidedIdeal R ->o Ideal R where
  body: { carrier := I
    add_mem' := I.add_mem
    zero_mem' := I.zero_mem
    smul_mem' := fun r x hx => I.mul_mem_left r x hx }
  monotone' _ _ h _ h' := h h'

中文:
定义 asIdeal
  签名: : TwoSided理想 R ->o 理想 R where
  定义体: { carrier := I
    add_mem' := I.add_mem
    zero_mem' := I.zero_mem
    smul_mem' := fun r x hx => I.mul_mem_left r x hx }
  monotone' _ _ h _ h' := h h'

Depends on / 依赖: I.add_mem, I.mul_mem_left, I.zero_mem, add_mem, carrier, monotone, mul_mem_left, smul_mem, zero_mem
-/
def asIdeal : TwoSidedIdeal R ->o Ideal R where
  toFun I :=
  { carrier := I
    add_mem' := I.add_mem
    zero_mem' := I.zero_mem
    smul_mem' := fun r x hx => I.mul_mem_left r x hx }
  monotone' _ _ h _ h' := h h'

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `mem_asIdeal` / 引理 `mem_asIdeal`

English:
lemma mem_asIdeal
  given: {I : TwoSidedIdeal R} {x : R}
  proof: by simp [asIdeal]

中文:
引理 mem_asIdeal
  条件: {I : TwoSided理想 R} {x : R}
  证明: by simp [asIdeal]

Depends on / 依赖: asIdeal
-/
lemma mem_asIdeal {I : TwoSidedIdeal R} {x : R} :
    x in asIdeal I ↔ x in I := by simp [asIdeal]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `gc` / 引理 `gc`

English:
lemma gc
  statement: GaloisConnection fromIdeal (asIdeal (R := R))
  proof: fun I J => ⟨fun h x hx => h mem_span_iff.2 fun _ H => H hx, fun h x hx => by
    simp only [fromIdeal, OrderHom.coe_mk, mem_span_iff] at hx
    exact hx _ h⟩

@[simp]

中文:
引理 gc
  结论: GaloisConnection fromIdeal (asIdeal (R := R))
  证明: fun I J => ⟨fun h x hx => h mem_span_iff.2 fun _ H => H hx, fun h x hx => by
    simp only [fromIdeal, OrderHom.coe_mk, mem_span_iff] at hx
    exact hx _ h⟩

@[simp]
-/
lemma gc : GaloisConnection fromIdeal (asIdeal (R := R)) :=
fun I J => ⟨fun h x hx => h mem_span_iff.2 fun _ H => H hx, fun h x hx => by
    simp only [fromIdeal, OrderHom.coe_mk, mem_span_iff] at hx
    exact hx _ h⟩

@[simp]
/--
lemma `coe_asIdeal` / 引理 `coe_asIdeal`

English:
lemma coe_asIdeal
  given: {I : TwoSidedIdeal R}
  statement: (asIdeal I : Set R) = I
  proof: rfl

中文:
引理 coe_asIdeal
  条件: {I : TwoSided理想 R}
  结论: (asIdeal I : 集合 R) = I
  证明: rfl
-/
lemma coe_asIdeal {I : TwoSidedIdeal R} : (asIdeal I : Set R) = I := rfl

/--
lemma `bot_asIdeal` / 引理 `bot_asIdeal`

English:
lemma bot_asIdeal
  statement: (⊥ : TwoSidedIdeal R).asIdeal = ⊥
  proof: rfl

中文:
引理 bot_asIdeal
  结论: (⊥ : TwoSided理想 R).asIdeal = ⊥
  证明: rfl
-/
@[simp] lemma bot_asIdeal : (⊥ : TwoSidedIdeal R).asIdeal = ⊥ := rfl

/--
lemma `top_asIdeal` / 引理 `top_asIdeal`

English:
lemma top_asIdeal
  statement: (⊤ : TwoSidedIdeal R).asIdeal = ⊤
  proof: rfl

中文:
引理 top_asIdeal
  结论: (⊤ : TwoSided理想 R).asIdeal = ⊤
  证明: rfl

Depends on / 依赖: ContinuousMap, ContinuousMap.ext, StarAlgHom, StarAlgHom.ext
-/
@[simp] lemma top_asIdeal : (⊤ : TwoSidedIdeal R).asIdeal = ⊤ := rfl

instance (I : TwoSidedIdeal R) : I.asIdeal.IsTwoSided :=
  ⟨fun _ => by simpa using I.mul_mem_right _ _⟩

/--
Definition of `asIdealOpposite` / `asIdealOpposite` 的定义

English:
definition asIdealOpposite
  signature: : TwoSidedIdeal R ->o Ideal Rᵐᵒᵖ where
  body: asIdeal ⟨I.ringCon.op⟩
  monotone' I J h x h' := by
    simp only [mem_asIdeal, mem_iff, RingCon.op_iff, MulOpposite.unop_zero] at h' ⊢
.2 h .1 h' I.rel_iff 0 x.unop exact J.rel_iff _ _

中文:
定义 asIdealOpposite
  签名: : TwoSided理想 R ->o 理想 Rᵐᵒᵖ where
  定义体: asIdeal ⟨I.ringCon.op⟩
  monotone' I J h x h' := by
    simp only [mem_asIdeal, mem_iff, RingCon.op_iff, MulOpposite.unop_zero] at h' ⊢
.2 h .1 h' I.rel_iff 0 x.unop exact J.rel_iff _ _

Depends on / 依赖: ContinuousMap, ContinuousMap.ext, I.ringCon.op, StarAlgHom, StarAlgHom.ext, asIdeal, ringCon
-/
def asIdealOpposite : TwoSidedIdeal R ->o Ideal Rᵐᵒᵖ where
  toFun I := asIdeal ⟨I.ringCon.op⟩
  monotone' I J h x h' := by
    simp only [mem_asIdeal, mem_iff, RingCon.op_iff, MulOpposite.unop_zero] at h' ⊢
.2 h .1 h' I.rel_iff 0 x.unop exact J.rel_iff _ _

/--
lemma `mem_asIdealOpposite` / 引理 `mem_asIdealOpposite`

English:
lemma mem_asIdealOpposite
  given: {I : TwoSidedIdeal R} {x : Rᵐᵒᵖ}
  proof: by
  simpa [asIdealOpposite, asIdeal, TwoSidedIdeal.mem_iff, RingCon.op_iff] using
    ⟨I.ringCon.symm, I.ringCon.symm⟩

中文:
引理 mem_asIdealOpposite
  条件: {I : TwoSided理想 R} {x : Rᵐᵒᵖ}
  证明: by
  simpa [asIdealOpposite, asIdeal, TwoSidedIdeal.mem_iff, RingCon.op_iff] using
    ⟨I.ringCon.symm, I.ringCon.symm⟩

Depends on / 依赖: I.ringCon.symm, RingCon, RingCon.op_iff, TwoSidedIdeal, TwoSidedIdeal.mem_iff, asIdeal, asIdealOpposite, mem_iff, op_iff, ringCon
-/
lemma mem_asIdealOpposite {I : TwoSidedIdeal R} {x : Rᵐᵒᵖ} :
    x in asIdealOpposite I ↔ x.unop in I := by
  simpa [asIdealOpposite, asIdeal, TwoSidedIdeal.mem_iff, RingCon.op_iff] using
    ⟨I.ringCon.symm, I.ringCon.symm⟩

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/--
Definition of `orderIsoIdeal` / `orderIsoIdeal` 的定义

English:
definition orderIsoIdeal
  signature: : TwoSidedIdeal R ≃o Ideal R where
  body: asIdeal
  invFun := fromIdeal
  map_rel_iff' := ⟨fun h _ hx => h hx, fun h => asIdeal.monotone' h⟩
left_inv _ := SetLike.ext fun _ => mem_span_iff.trans by aesop
  right_inv J := SetLike.ext fun x => mem_span_iff.trans
.1 h (mk' ⟨fun h => mem_mk' _ _ _ _ _ _ _
      J J.zero_mem J.add_mem J.neg_mem (J.mul_mem_left _) (J.mul_mem_right _))
      (fun x => by simp), by aesop⟩

中文:
定义 orderIsoIdeal
  签名: : TwoSided理想 R ≃o 理想 R where
  定义体: asIdeal
  invFun := fromIdeal
  map_rel_iff' := ⟨fun h _ hx => h hx, fun h => asIdeal.monotone' h⟩
left_inv _ := SetLike.ext fun _ => mem_span_iff.trans by aesop
  right_inv J := SetLike.ext fun x => mem_span_iff.trans
.1 h (mk' ⟨fun h => mem_mk' _ _ _ _ _ _ _
      J J.zero_mem J.add_mem J.neg_mem (J.mul_mem_left _) (J.mul_mem_right _))
      (fun x => by simp), by aesop⟩

Depends on / 依赖: asIdeal
-/
def orderIsoIdeal : TwoSidedIdeal R ≃o Ideal R where
  toFun := asIdeal
  invFun := fromIdeal
  map_rel_iff' := ⟨fun h _ hx => h hx, fun h => asIdeal.monotone' h⟩
left_inv _ := SetLike.ext fun _ => mem_span_iff.trans by aesop
  right_inv J := SetLike.ext fun x => mem_span_iff.trans
.1 h (mk' ⟨fun h => mem_mk' _ _ _ _ _ _ _
      J J.zero_mem J.add_mem J.neg_mem (J.mul_mem_left _) (J.mul_mem_right _))
      (fun x => by simp), by aesop⟩

end CommRing

end TwoSidedIdeal

namespace Ideal
variable {R : Type*} [Ring R]

/--
Definition of `toTwoSided` / `toTwoSided` 的定义

English:
definition toTwoSided
  signature: (I : Ideal R) [I.IsTwoSided]
  body: TwoSidedIdeal.mk' I I.zero_mem I.add_mem I.neg_mem (I.smul_mem _) (I.mul_mem_right _)

@[simp]

中文:
定义 toTwoSided
  签名: (I : 理想 R) [I.是TwoSided]
  定义体: TwoSidedIdeal.mk' I I.zero_mem I.add_mem I.neg_mem (I.smul_mem _) (I.mul_mem_right _)

@[simp]

Depends on / 依赖: I.add_mem, I.mul_mem_right, I.neg_mem, I.smul_mem, I.zero_mem, TwoSidedIdeal, TwoSidedIdeal.mk, add_mem, mul_mem_right, neg_mem, smul_mem, zero_mem
-/
def toTwoSided (I : Ideal R) [I.IsTwoSided] : TwoSidedIdeal R :=
  TwoSidedIdeal.mk' I I.zero_mem I.add_mem I.neg_mem (I.smul_mem _) (I.mul_mem_right _)

@[simp]
/--
lemma `mem_toTwoSided` / 引理 `mem_toTwoSided`

English:
lemma mem_toTwoSided
  given: {I : Ideal R} [I.IsTwoSided] {x : R}
  proof: by
  simp [toTwoSided]

@[simp]

中文:
引理 mem_toTwoSided
  条件: {I : 理想 R} [I.是TwoSided] {x : R}
  证明: by
  simp [toTwoSided]

@[simp]

Depends on / 依赖: toTwoSided
-/
lemma mem_toTwoSided {I : Ideal R} [I.IsTwoSided] {x : R} :
    x in I.toTwoSided ↔ x in I := by
  simp [toTwoSided]

@[simp]
/--
lemma `coe_toTwoSided` / 引理 `coe_toTwoSided`

English:
lemma coe_toTwoSided
  given: (I : Ideal R) [I.IsTwoSided]
  statement: (I.toTwoSided : Set R) = I
  proof: by
  simp [toTwoSided]

@[simp]

中文:
引理 coe_toTwoSided
  条件: (I : 理想 R) [I.是TwoSided]
  结论: (I.toTwoSided : 集合 R) = I
  证明: by
  simp [toTwoSided]

@[simp]

Depends on / 依赖: toTwoSided
-/
lemma coe_toTwoSided (I : Ideal R) [I.IsTwoSided] : (I.toTwoSided : Set R) = I := by
  simp [toTwoSided]

@[simp]
/--
lemma `toTwoSided_asIdeal` / 引理 `toTwoSided_asIdeal`

English:
lemma toTwoSided_asIdeal
  given: (I : TwoSidedIdeal R)
  statement: I.asIdeal.toTwoSided = I
  proof: by ext; simp

@[simp]

中文:
引理 toTwoSided_asIdeal
  条件: (I : TwoSided理想 R)
  结论: I.asIdeal.toTwoSided = I
  证明: by ext; simp

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.le_def, ContinuousSqrt, ContinuousSqrt.continuousOn_sqrt.domRestrict, ContinuousSqrt.sqrt_mul_sqrt, ContinuousSqrt.sqrt_nonneg, IsSelfAdjoint, IsSelfAdjoint.star_eq, StarOrderedRing, StarOrderedRing.of_le_iff, codRestrict, continuousOn_sqrt, domRestrict, f.prodMk, le_add_of_nonneg_right, le_def, map_continuous, of_le_iff, of_nonneg, prodMk
-/
lemma toTwoSided_asIdeal (I : TwoSidedIdeal R) : I.asIdeal.toTwoSided = I := by ext; simp

@[simp]
/--
lemma `asIdeal_toTwoSided` / 引理 `asIdeal_toTwoSided`

English:
lemma asIdeal_toTwoSided
  given: (I : Ideal R) [I.IsTwoSided]
  statement: I.toTwoSided.asIdeal = I
  proof: by
  ext
  simp

中文:
引理 asIdeal_toTwoSided
  条件: (I : 理想 R) [I.是TwoSided]
  结论: I.toTwoSided.asIdeal = I
  证明: by
  ext
  simp
-/
lemma asIdeal_toTwoSided (I : Ideal R) [I.IsTwoSided] : I.toTwoSided.asIdeal = I := by
  ext
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (Ideal R) (TwoSidedIdeal R) TwoSidedIdeal.asIdeal (·.IsTwoSided)
  body: ⟨I.toTwoSided, asIdeal_toTwoSided ..⟩

中文:
实例 :
  签名: CanLift (理想 R) (TwoSided理想 R) TwoSided理想.asIdeal (·.是TwoSided)
  定义体: ⟨I.toTwoSided, asIdeal_toTwoSided ..⟩

Depends on / 依赖: I.toTwoSided, asIdeal_toTwoSided, toTwoSided
-/
instance : CanLift (Ideal R) (TwoSidedIdeal R) TwoSidedIdeal.asIdeal (·.IsTwoSided) where
  prf I _ := ⟨I.toTwoSided, asIdeal_toTwoSided ..⟩

end Ideal

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `TwoSidedIdeal.orderIsoIsTwoSided` / `TwoSidedIdeal.orderIsoIsTwoSided` 的定义

English:
definition TwoSidedIdeal.orderIsoIsTwoSided
  signature: {R : Type*} [Ring R]
  body: ⟨I.asIdeal, inferInstance⟩
  invFun I := have := I.2; I.1.toTwoSided
  left_inv _ := by simp
  right_inv I := by simp
  map_rel_iff' {I I'} := by simp [SetLike.le_def]

中文:
定义 TwoSided理想.orderIsoIsTwoSided
  签名: {R : 类型} [环 R]
  定义体: ⟨I.asIdeal, inferInstance⟩
  invFun I := have := I.2; I.1.toTwoSided
  left_inv _ := by simp
  right_inv I := by simp
  map_rel_iff' {I I'} := by simp [SetLike.le_def]
-/
@[simps] def TwoSidedIdeal.orderIsoIsTwoSided {R : Type*} [Ring R] :
    TwoSidedIdeal R ≃o {I : Ideal R // I.IsTwoSided} where
  toFun I := ⟨I.asIdeal, inferInstance⟩
  invFun I := have := I.2; I.1.toTwoSided
  left_inv _ := by simp
  right_inv I := by simp
  map_rel_iff' {I I'} := by simp [SetLike.le_def]
