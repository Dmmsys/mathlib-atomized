/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Upper/lower bounds in ordered monoids and groups

In this file we prove a few facts like “`-s` is bounded above iff `s` is bounded below”
(`bddAbove_neg`).
-/

public section

open Function Set
open scoped Pointwise

variable {ι G M : Type*}

section Mul
variable [Mul M] [Preorder M] [MulLeftMono M]
  [MulRightMono M] {f g : ι -> M} {s t : Set M} {a b : M}

@[to_additive]
/--
lemma `mul_mem_upperBounds_mul` / 引理 `mul_mem_upperBounds_mul`

English:
lemma mul_mem_upperBounds_mul
  given: (ha : a in upperBounds s) (hb : b in upperBounds t)
  proof: forall_mem_image2.2 fun _ hx _ hy => mul_le_mul' (ha hx) (hb hy)

@[to_additive]

中文:
引理 mul_mem_upperBounds_mul
  条件: (ha : a in upperBounds s) (hb : b in upperBounds t)
  证明: forall_mem_image2.2 fun _ hx _ hy => mul_le_mul' (ha hx) (hb hy)

@[to_additive]

Depends on / 依赖: PosSMulStrictMono, PosSMulStrictMono.toPosSMulReflectLE, forall_mem_image2, mul_le_mul, toPosSMulReflectLE
-/
lemma mul_mem_upperBounds_mul (ha : a in upperBounds s) (hb : b in upperBounds t) :
    a * b in upperBounds (s * t) := forall_mem_image2.2 fun _ hx _ hy => mul_le_mul' (ha hx) (hb hy)

@[to_additive]
/--
lemma `subset_upperBounds_mul` / 引理 `subset_upperBounds_mul`

English:
lemma subset_upperBounds_mul
  given: (s t : Set M)
  statement: upperBounds s * upperBounds t subseteq upperBounds (s * t)
  proof: image2_subset_iff.2 fun _ hx _ hy => mul_mem_upperBounds_mul hx hy

@[to_additive]

中文:
引理 subset_upperBounds_mul
  条件: (s t : 集合 M)
  结论: upperBounds s * upperBounds t subseteq upperBounds (s * t)
  证明: image2_subset_iff.2 fun _ hx _ hy => mul_mem_upperBounds_mul hx hy

@[to_additive]

Depends on / 依赖: image2_subset_iff, mul_mem_upperBounds_mul
-/
lemma subset_upperBounds_mul (s t : Set M) : upperBounds s * upperBounds t subseteq upperBounds (s * t) :=
  image2_subset_iff.2 fun _ hx _ hy => mul_mem_upperBounds_mul hx hy

@[to_additive]
/--
lemma `mul_mem_lowerBounds_mul` / 引理 `mul_mem_lowerBounds_mul`

English:
lemma mul_mem_lowerBounds_mul
  given: (ha : a in lowerBounds s) (hb : b in lowerBounds t)
  proof: mul_mem_upperBounds_mul (M := Mᵒᵈ) ha hb

@[to_additive]

中文:
引理 mul_mem_lowerBounds_mul
  条件: (ha : a in lowerBounds s) (hb : b in lowerBounds t)
  证明: mul_mem_upperBounds_mul (M := Mᵒᵈ) ha hb

@[to_additive]

Depends on / 依赖: mul_mem_upperBounds_mul
-/
lemma mul_mem_lowerBounds_mul (ha : a in lowerBounds s) (hb : b in lowerBounds t) :
    a * b in lowerBounds (s * t) := mul_mem_upperBounds_mul (M := Mᵒᵈ) ha hb

@[to_additive]
/--
lemma `subset_lowerBounds_mul` / 引理 `subset_lowerBounds_mul`

English:
lemma subset_lowerBounds_mul
  given: (s t : Set M)
  statement: lowerBounds s * lowerBounds t subseteq lowerBounds (s * t)
  proof: subset_upperBounds_mul (M := Mᵒᵈ) _ _

@[to_additive]

中文:
引理 subset_lowerBounds_mul
  条件: (s t : 集合 M)
  结论: lowerBounds s * lowerBounds t subseteq lowerBounds (s * t)
  证明: subset_upperBounds_mul (M := Mᵒᵈ) _ _

@[to_additive]

Depends on / 依赖: subset_upperBounds_mul
-/
lemma subset_lowerBounds_mul (s t : Set M) : lowerBounds s * lowerBounds t subseteq lowerBounds (s * t) :=
  subset_upperBounds_mul (M := Mᵒᵈ) _ _

@[to_additive]
/--
lemma `BddAbove.mul` / 引理 `BddAbove.mul`

English:
lemma BddAbove.mul
  given: (hs : BddAbove s) (ht : BddAbove t)
  statement: BddAbove (s * t)
  proof: (Nonempty.mul hs ht).mono (subset_upperBounds_mul s t)

@[to_additive]

中文:
引理 BddAbove.mul
  条件: (hs : BddAbove s) (ht : BddAbove t)
  结论: BddAbove (s * t)
  证明: (Nonempty.mul hs ht).mono (subset_upperBounds_mul s t)

@[to_additive]

Depends on / 依赖: Nonempty, Nonempty.mul, subset_upperBounds_mul
-/
lemma BddAbove.mul (hs : BddAbove s) (ht : BddAbove t) : BddAbove (s * t) :=
  (Nonempty.mul hs ht).mono (subset_upperBounds_mul s t)

@[to_additive]
/--
lemma `BddBelow.mul` / 引理 `BddBelow.mul`

English:
lemma BddBelow.mul
  given: (hs : BddBelow s) (ht : BddBelow t)
  statement: BddBelow (s * t)
  proof: (Nonempty.mul hs ht).mono (subset_lowerBounds_mul s t)

@[to_additive] alias Set.BddAbove.mul := BddAbove.mul

@[to_additive]

中文:
引理 BddBelow.mul
  条件: (hs : BddBelow s) (ht : BddBelow t)
  结论: BddBelow (s * t)
  证明: (Nonempty.mul hs ht).mono (subset_lowerBounds_mul s t)

@[to_additive] alias Set.BddAbove.mul := BddAbove.mul

@[to_additive]

Depends on / 依赖: Nonempty, Nonempty.mul, subset_lowerBounds_mul
-/
lemma BddBelow.mul (hs : BddBelow s) (ht : BddBelow t) : BddBelow (s * t) :=
  (Nonempty.mul hs ht).mono (subset_lowerBounds_mul s t)

@[to_additive] alias Set.BddAbove.mul := BddAbove.mul

@[to_additive]
/--
lemma `BddAbove.range_mul` / 引理 `BddAbove.range_mul`

English:
lemma BddAbove.range_mul
  given: (hf : BddAbove (range f)) (hg : BddAbove (range g))
  proof: .range_comp_left (f := fun i => (f i, g i)) (bddAbove_range_prod.2 ⟨hf, hg⟩)
    (monotone_fst.mul' monotone_snd)

@[to_additive]

中文:
引理 BddAbove.range_mul
  条件: (hf : BddAbove (range f)) (hg : BddAbove (range g))
  证明: .range_comp_left (f := fun i => (f i, g i)) (bddAbove_range_prod.2 ⟨hf, hg⟩)
    (monotone_fst.mul' monotone_snd)

@[to_additive]

Depends on / 依赖: bddAbove_range_prod, monotone_fst, monotone_fst.mul, monotone_snd, range_comp_left
-/
lemma BddAbove.range_mul (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    BddAbove (range fun i => f i * g i) :=
  .range_comp_left (f := fun i => (f i, g i)) (bddAbove_range_prod.2 ⟨hf, hg⟩)
    (monotone_fst.mul' monotone_snd)

@[to_additive]
/--
lemma `BddBelow.range_mul` / 引理 `BddBelow.range_mul`

English:
lemma BddBelow.range_mul
  given: (hf : BddBelow (range f)) (hg : BddBelow (range g))
  proof: BddAbove.range_mul (M := Mᵒᵈ) hf hg

中文:
引理 BddBelow.range_mul
  条件: (hf : BddBelow (range f)) (hg : BddBelow (range g))
  证明: BddAbove.range_mul (M := Mᵒᵈ) hf hg

Depends on / 依赖: BddAbove, BddAbove.range_mul, range_mul
-/
lemma BddBelow.range_mul (hf : BddBelow (range f)) (hg : BddBelow (range g)) :
    BddBelow (range fun i => f i * g i) := BddAbove.range_mul (M := Mᵒᵈ) hf hg

end Mul

section Group
variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

@[to_additive (attr := simp)]
/--
theorem `bddAbove_inv` / 定理 `bddAbove_inv`

English:
theorem bddAbove_inv
  statement: BddAbove s⁻¹ ↔ BddBelow s
  proof: (OrderIso.inv G).bddAbove_preimage

@[to_additive (attr := simp)]

中文:
定理 bddAbove_inv
  结论: BddAbove s⁻¹ ↔ BddBelow s
  证明: (OrderIso.inv G).bddAbove_preimage

@[to_additive (attr := simp)]

Depends on / 依赖: OrderIso, OrderIso.inv, bddAbove_preimage
-/
theorem bddAbove_inv : BddAbove s⁻¹ ↔ BddBelow s :=
  (OrderIso.inv G).bddAbove_preimage

@[to_additive (attr := simp)]
/--
theorem `bddBelow_inv` / 定理 `bddBelow_inv`

English:
theorem bddBelow_inv
  statement: BddBelow s⁻¹ ↔ BddAbove s
  proof: (OrderIso.inv G).bddBelow_preimage

@[to_additive]

中文:
定理 bddBelow_inv
  结论: BddBelow s⁻¹ ↔ BddAbove s
  证明: (OrderIso.inv G).bddBelow_preimage

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, bddBelow_preimage
-/
theorem bddBelow_inv : BddBelow s⁻¹ ↔ BddAbove s :=
  (OrderIso.inv G).bddBelow_preimage

@[to_additive]
/--
theorem `BddAbove.inv` / 定理 `BddAbove.inv`

English:
theorem BddAbove.inv
  given: (h : BddAbove s)
  statement: BddBelow s⁻¹
  proof: bddBelow_inv.2 h

@[to_additive]

中文:
定理 BddAbove.inv
  条件: (h : BddAbove s)
  结论: BddBelow s⁻¹
  证明: bddBelow_inv.2 h

@[to_additive]

Depends on / 依赖: SMulPosStrictMono, SMulPosStrictMono.toSMulPosReflectLE, bddBelow_inv, toSMulPosReflectLE
-/
theorem BddAbove.inv (h : BddAbove s) : BddBelow s⁻¹ :=
  bddBelow_inv.2 h

@[to_additive]
/--
theorem `BddBelow.inv` / 定理 `BddBelow.inv`

English:
theorem BddBelow.inv
  given: (h : BddBelow s)
  statement: BddAbove s⁻¹
  proof: bddAbove_inv.2 h

@[to_additive (attr := simp)]

中文:
定理 BddBelow.inv
  条件: (h : BddBelow s)
  结论: BddAbove s⁻¹
  证明: bddAbove_inv.2 h

@[to_additive (attr := simp)]

Depends on / 依赖: bddAbove_inv
-/
theorem BddBelow.inv (h : BddBelow s) : BddAbove s⁻¹ :=
  bddAbove_inv.2 h

@[to_additive (attr := simp)]
/--
theorem `isLUB_inv` / 定理 `isLUB_inv`

English:
theorem isLUB_inv
  statement: IsLUB s⁻¹ a ↔ IsGLB s a⁻¹
  proof: (OrderIso.inv G).isLUB_preimage

@[to_additive]

中文:
定理 isLUB_inv
  结论: IsLUB s⁻¹ a ↔ IsGLB s a⁻¹
  证明: (OrderIso.inv G).isLUB_preimage

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, isLUB_preimage
-/
theorem isLUB_inv : IsLUB s⁻¹ a ↔ IsGLB s a⁻¹ :=
  (OrderIso.inv G).isLUB_preimage

@[to_additive]
/--
theorem `isLUB_inv'` / 定理 `isLUB_inv'`

English:
theorem isLUB_inv'
  statement: IsLUB s⁻¹ a⁻¹ ↔ IsGLB s a
  proof: (OrderIso.inv G).isLUB_preimage'

@[to_additive]

中文:
定理 isLUB_inv'
  结论: IsLUB s⁻¹ a⁻¹ ↔ IsGLB s a
  证明: (OrderIso.inv G).isLUB_preimage'

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, isLUB_preimage
-/
theorem isLUB_inv' : IsLUB s⁻¹ a⁻¹ ↔ IsGLB s a :=
  (OrderIso.inv G).isLUB_preimage'

@[to_additive]
/--
theorem `IsGLB.inv` / 定理 `IsGLB.inv`

English:
theorem IsGLB.inv
  given: (h : IsGLB s a)
  statement: IsLUB s⁻¹ a⁻¹
  proof: isLUB_inv'.2 h

@[to_additive (attr := simp)]

中文:
定理 IsGLB.inv
  条件: (h : IsGLB s a)
  结论: IsLUB s⁻¹ a⁻¹
  证明: isLUB_inv'.2 h

@[to_additive (attr := simp)]

Depends on / 依赖: isLUB_inv
-/
theorem IsGLB.inv (h : IsGLB s a) : IsLUB s⁻¹ a⁻¹ :=
  isLUB_inv'.2 h

@[to_additive (attr := simp)]
/--
theorem `isGLB_inv` / 定理 `isGLB_inv`

English:
theorem isGLB_inv
  statement: IsGLB s⁻¹ a ↔ IsLUB s a⁻¹
  proof: (OrderIso.inv G).isGLB_preimage

@[to_additive]

中文:
定理 isGLB_inv
  结论: IsGLB s⁻¹ a ↔ IsLUB s a⁻¹
  证明: (OrderIso.inv G).isGLB_preimage

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, isGLB_preimage
-/
theorem isGLB_inv : IsGLB s⁻¹ a ↔ IsLUB s a⁻¹ :=
  (OrderIso.inv G).isGLB_preimage

@[to_additive]
/--
theorem `isGLB_inv'` / 定理 `isGLB_inv'`

English:
theorem isGLB_inv'
  statement: IsGLB s⁻¹ a⁻¹ ↔ IsLUB s a
  proof: (OrderIso.inv G).isGLB_preimage'

@[to_additive]

中文:
定理 isGLB_inv'
  结论: IsGLB s⁻¹ a⁻¹ ↔ IsLUB s a
  证明: (OrderIso.inv G).isGLB_preimage'

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, isGLB_preimage
-/
theorem isGLB_inv' : IsGLB s⁻¹ a⁻¹ ↔ IsLUB s a :=
  (OrderIso.inv G).isGLB_preimage'

@[to_additive]
/--
theorem `IsLUB.inv` / 定理 `IsLUB.inv`

English:
theorem IsLUB.inv
  given: (h : IsLUB s a)
  statement: IsGLB s⁻¹ a⁻¹
  proof: isGLB_inv'.2 h

@[to_additive]

中文:
定理 IsLUB.inv
  条件: (h : IsLUB s a)
  结论: IsGLB s⁻¹ a⁻¹
  证明: isGLB_inv'.2 h

@[to_additive]

Depends on / 依赖: isGLB_inv
-/
theorem IsLUB.inv (h : IsLUB s a) : IsGLB s⁻¹ a⁻¹ :=
  isGLB_inv'.2 h

@[to_additive]
/--
lemma `BddBelow.range_inv` / 引理 `BddBelow.range_inv`

English:
lemma BddBelow.range_inv
  given: {α : Type*} {f : α -> G} (hf : BddBelow (range f))
  proof: hf.range_comp_left (OrderIso.inv G).monotone

@[to_additive]

中文:
引理 BddBelow.range_inv
  条件: {α : 类型} {f : α -> G} (hf : BddBelow (range f))
  证明: hf.range_comp_left (OrderIso.inv G).monotone

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.inv, hf.range_comp_left, monotone, range_comp_left
-/
lemma BddBelow.range_inv {α : Type*} {f : α -> G} (hf : BddBelow (range f)) :
    BddAbove (range (fun x => (f x)⁻¹)) :=
  hf.range_comp_left (OrderIso.inv G).monotone

@[to_additive]
/--
lemma `BddAbove.range_inv` / 引理 `BddAbove.range_inv`

English:
lemma BddAbove.range_inv
  given: {α : Type*} {f : α -> G} (hf : BddAbove (range f))
  proof: BddBelow.range_inv (G := Gᵒᵈ) hf

@[to_additive]

中文:
引理 BddAbove.range_inv
  条件: {α : 类型} {f : α -> G} (hf : BddAbove (range f))
  证明: BddBelow.range_inv (G := Gᵒᵈ) hf

@[to_additive]

Depends on / 依赖: BddBelow, BddBelow.range_inv, range_inv
-/
lemma BddAbove.range_inv {α : Type*} {f : α -> G} (hf : BddAbove (range f)) :
    BddBelow (range (fun x => (f x)⁻¹)) :=
  BddBelow.range_inv (G := Gᵒᵈ) hf

@[to_additive]
/--
lemma `IsLUB.mul` / 引理 `IsLUB.mul`

English:
lemma IsLUB.mul
  given: (hs : IsLUB s a) (ht : IsLUB t b)
  proof: isLUB_image2_of_isLUB_isLUB (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs ht

@[to_additive]

中文:
引理 IsLUB.mul
  条件: (hs : IsLUB s a) (ht : IsLUB t b)
  证明: isLUB_image2_of_isLUB_isLUB (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs ht

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, OrderIso.mulRight, isLUB_image2_of_isLUB_isLUB, mulLeft, mulRight, to_galoisConnection
-/
lemma IsLUB.mul (hs : IsLUB s a) (ht : IsLUB t b) :
    IsLUB (s * t) (a * b) :=
  isLUB_image2_of_isLUB_isLUB (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs ht

@[to_additive]
/--
lemma `IsGLB.mul` / 引理 `IsGLB.mul`

English:
lemma IsGLB.mul
  given: (hs : IsGLB s a) (ht : IsGLB t b)
  proof: IsLUB.mul (G := Gᵒᵈ) hs ht

@[to_additive]

中文:
引理 IsGLB.mul
  条件: (hs : IsGLB s a) (ht : IsGLB t b)
  证明: IsLUB.mul (G := Gᵒᵈ) hs ht

@[to_additive]

Depends on / 依赖: IsLUB.mul
-/
lemma IsGLB.mul (hs : IsGLB s a) (ht : IsGLB t b) :
    IsGLB (s * t) (a * b) :=
  IsLUB.mul (G := Gᵒᵈ) hs ht

@[to_additive]
/--
lemma `IsLUB.div` / 引理 `IsLUB.div`

English:
lemma IsLUB.div
  given: (hs : IsLUB s a) (ht : IsGLB t b)
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact hs.mul ht.inv

@[to_additive]

中文:
引理 IsLUB.div
  条件: (hs : IsLUB s a) (ht : IsGLB t b)
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact hs.mul ht.inv

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hs.mul, ht.inv
-/
lemma IsLUB.div (hs : IsLUB s a) (ht : IsGLB t b) :
    IsLUB (s / t) (a / b) := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
  exact hs.mul ht.inv

@[to_additive]
/--
lemma `IsGLB.div` / 引理 `IsGLB.div`

English:
lemma IsGLB.div
  given: (hs : IsGLB s a) (ht : IsLUB t b)
  proof: IsLUB.div (G := Gᵒᵈ) hs ht

中文:
引理 IsGLB.div
  条件: (hs : IsGLB s a) (ht : IsLUB t b)
  证明: IsLUB.div (G := Gᵒᵈ) hs ht

Depends on / 依赖: IsLUB.div
-/
lemma IsGLB.div (hs : IsGLB s a) (ht : IsLUB t b) :
    IsGLB (s / t) (a / b) :=
  IsLUB.div (G := Gᵒᵈ) hs ht

end Group
