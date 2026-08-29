/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Divisibility.Hom
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Ring.Defs

/-!
# Lemmas about divisibility in rings

Note that this file is imported by basic tactics like `linarith` and so must have only minimal
imports. Further results about divisibility in rings may be found in
`Mathlib/Algebra/Ring/Divisibility/Lemmas.lean` which is not subject to this import constraint.
-/

@[expose] public section


variable {α β : Type*}

section Semigroup

variable [Semigroup α] [Semigroup β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β]

/--
theorem `map_dvd_iff` / 定理 `map_dvd_iff`

English:
theorem map_dvd_iff
  given: (f : F) {a b}
  statement: f a ∣ f b ↔ a ∣ b
  proof: let f := MulEquivClass.toMulEquiv f
  ⟨fun h => by rw [← f.left_inv a, ← f.left_inv b]; exact map_dvd f.symm h, map_dvd f⟩

中文:
定理 map_dvd_iff
  条件: (f : F) {a b}
  结论: f a ∣ f b ↔ a ∣ b
  证明: let f := MulEquivClass.toMulEquiv f
  ⟨fun h => by rw [← f.left_inv a, ← f.left_inv b]; exact map_dvd f.symm h, map_dvd f⟩

Depends on / 依赖: MulEquivClass, MulEquivClass.toMulEquiv, f.left_inv, f.symm, left_inv, map_dvd, toMulEquiv
-/
theorem map_dvd_iff (f : F) {a b} : f a ∣ f b ↔ a ∣ b :=
  let f := MulEquivClass.toMulEquiv f
  ⟨fun h => by rw [← f.left_inv a, ← f.left_inv b]; exact map_dvd f.symm h, map_dvd f⟩

/--
theorem `map_dvd_iff_dvd_symm` / 定理 `map_dvd_iff_dvd_symm`

English:
theorem map_dvd_iff_dvd_symm
  given: (f : F) {a : α} {b : β}
  proof: by
  obtain ⟨c, rfl⟩ : exists c, f c = b := EquivLike.surjective f b
  simp [map_dvd_iff]

中文:
定理 map_dvd_iff_dvd_symm
  条件: (f : F) {a : α} {b : β}
  证明: by
  obtain ⟨c, rfl⟩ : exists c, f c = b := EquivLike.surjective f b
  simp [map_dvd_iff]

Depends on / 依赖: EquivLike, EquivLike.surjective, map_dvd_iff, surjective
-/
theorem map_dvd_iff_dvd_symm (f : F) {a : α} {b : β} :
    f a ∣ b ↔ a ∣ (MulEquivClass.toMulEquiv f).symm b := by
  obtain ⟨c, rfl⟩ : exists c, f c = b := EquivLike.surjective f b
  simp [map_dvd_iff]

/--
theorem `MulEquiv.decompositionMonoid` / 定理 `MulEquiv.decompositionMonoid`

English:
theorem MulEquiv.decompositionMonoid
  given: (f : F) [DecompositionMonoid β]
  statement: DecompositionMonoid α where
  proof: by
    rw [← map_dvd_iff f]; rw [map_mul] at h
    obtain ⟨a₁, a₂, h⟩ := DecompositionMonoid.primal _ h
    refine ⟨EquivLike.inv f a₁, EquivLike.inv f a₂, ?_⟩
    simp_rw [← map_dvd_iff f, EquivLike.apply_inv_apply, h, true_and, ← EquivLike.apply_eq_iff_eq f,
      h.2.2, map_mul, EquivLike.apply_i

中文:
定理 MulEquiv.decompositionMonoid
  条件: (f : F) [DecompositionMonoid β]
  结论: DecompositionMonoid α where
  证明: by
    rw [← map_dvd_iff f]; rw [map_mul] at h
    obtain ⟨a₁, a₂, h⟩ := DecompositionMonoid.primal _ h
    refine ⟨EquivLike.inv f a₁, EquivLike.inv f a₂, ?_⟩
    simp_rw [← map_dvd_iff f, EquivLike.apply_inv_apply, h, true_and, ← EquivLike.apply_eq_iff_eq f,
      h.2.2, map_mul, EquivLike.apply_i

Depends on / 依赖: DecompositionMonoid, DecompositionMonoid.primal, EquivLike, EquivLike.apply_eq_iff_eq, EquivLike.apply_inv_apply, EquivLike.inv, apply_eq_iff_eq, apply_inv_apply, map_dvd_iff, map_mul, primal, simp_rw, true_and
-/
theorem MulEquiv.decompositionMonoid (f : F) [DecompositionMonoid β] : DecompositionMonoid α where
  primal a b c h := by
    rw [← map_dvd_iff f]; rw [map_mul] at h
    obtain ⟨a₁, a₂, h⟩ := DecompositionMonoid.primal _ h
    refine ⟨EquivLike.inv f a₁, EquivLike.inv f a₂, ?_⟩
    simp_rw [← map_dvd_iff f, EquivLike.apply_inv_apply, h, true_and, ← EquivLike.apply_eq_iff_eq f,
      h.2.2, map_mul, EquivLike.apply_inv_apply]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Equiv.dvd {G : Type*} [LeftCancelSemigroup G] (g : G)
  body: fun a => ⟨g * a, ⟨a, rfl⟩⟩
  invFun := fun ⟨_, h⟩ => h.choose
  left_inv := fun _ => by simp
  right_inv := by
    rintro ⟨_, ⟨_, rfl⟩⟩
    simp

@[simp]

中文:
定义 noncomputable
  签名: def Equiv.dvd {G : 类型} [LeftCancelSemigroup G] (g : G)
  定义体: fun a => ⟨g * a, ⟨a, rfl⟩⟩
  invFun := fun ⟨_, h⟩ => h.choose
  left_inv := fun _ => by simp
  right_inv := by
    rintro ⟨_, ⟨_, rfl⟩⟩
    simp

@[simp]
-/
protected noncomputable def Equiv.dvd {G : Type*} [LeftCancelSemigroup G] (g : G) :
    G ≃ {a : G // g ∣ a} where
  toFun := fun a => ⟨g * a, ⟨a, rfl⟩⟩
  invFun := fun ⟨_, h⟩ => h.choose
  left_inv := fun _ => by simp
  right_inv := by
    rintro ⟨_, ⟨_, rfl⟩⟩
    simp

@[simp]
/--
theorem `Equiv.dvd_apply` / 定理 `Equiv.dvd_apply`

English:
theorem Equiv.dvd_apply
  given: {G : Type*} [LeftCancelSemigroup G] (g a : G)
  proof: rfl

中文:
定理 Equiv.dvd_apply
  条件: {G : 类型} [LeftCancelSemigroup G] (g a : G)
  证明: rfl
-/
theorem Equiv.dvd_apply {G : Type*} [LeftCancelSemigroup G] (g a : G) :
    Equiv.dvd g a = g * a := rfl

end Semigroup

section DistribSemigroup

variable [Add α] [Semigroup α]

/--
theorem `dvd_add` / 定理 `dvd_add`

English:
theorem dvd_add
  given: [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c)
  statement: a ∣ b + c
  proof: Dvd.elim h₁ fun d hd => Dvd.elim h₂ fun e he => Dvd.intro (d + e) (by simp [left_distrib, hd, he])

alias Dvd.dvd.add := dvd_add

中文:
定理 dvd_add
  条件: [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c)
  结论: a ∣ b + c
  证明: Dvd.elim h₁ fun d hd => Dvd.elim h₂ fun e he => Dvd.intro (d + e) (by simp [left_distrib, hd, he])

alias Dvd.dvd.add := dvd_add

Depends on / 依赖: Dvd.elim, Dvd.intro, left_distrib
-/
theorem dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  Dvd.elim h₁ fun d hd => Dvd.elim h₂ fun e he => Dvd.intro (d + e) (by simp [left_distrib, hd, he])

alias Dvd.dvd.add := dvd_add

end DistribSemigroup

section Semiring
variable [Semiring α] {a b c : α} {m n : Nat}

/--
lemma `min_pow_dvd_add` / 引理 `min_pow_dvd_add`

English:
lemma min_pow_dvd_add
  given: (ha : c ^ m ∣ a) (hb : c ^ n ∣ b)
  statement: c ^ min m n ∣ a + b
  proof: ((pow_dvd_pow c (m.min_le_left n)).trans ha).add ((pow_dvd_pow c (m.min_le_right n)).trans hb)

中文:
引理 min_pow_dvd_add
  条件: (ha : c ^ m ∣ a) (hb : c ^ n ∣ b)
  结论: c ^ min m n ∣ a + b
  证明: ((pow_dvd_pow c (m.min_le_left n)).trans ha).add ((pow_dvd_pow c (m.min_le_right n)).trans hb)

Depends on / 依赖: m.min_le_left, m.min_le_right, min_le_left, min_le_right, pow_dvd_pow
-/
lemma min_pow_dvd_add (ha : c ^ m ∣ a) (hb : c ^ n ∣ b) : c ^ min m n ∣ a + b :=
  ((pow_dvd_pow c (m.min_le_left n)).trans ha).add ((pow_dvd_pow c (m.min_le_right n)).trans hb)

end Semiring

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α]

/--
theorem `Dvd.dvd.linear_comb` / 定理 `Dvd.dvd.linear_comb`

English:
theorem Dvd.dvd.linear_comb
  given: {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α)
  statement: d ∣ a * x + b * y
  proof: dvd_add (hdx.mul_left a) (hdy.mul_left b)

中文:
定理 Dvd.dvd.linear_comb
  条件: {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α)
  结论: d ∣ a * x + b * y
  证明: dvd_add (hdx.mul_left a) (hdy.mul_left b)

Depends on / 依赖: dvd_add, hdx.mul_left, hdy.mul_left, mul_left
-/
theorem Dvd.dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) : d ∣ a * x + b * y :=
  dvd_add (hdx.mul_left a) (hdy.mul_left b)

end NonUnitalCommSemiring

section Semigroup

variable [Semigroup α] [HasDistribNeg α] {a b : α}

/-- An element `a` of a semigroup with a distributive negation divides the negation of an element
`b` iff `a` divides `b`. -/
@[simp]
/--
theorem `dvd_neg` / 定理 `dvd_neg`

English:
theorem dvd_neg
  statement: a ∣ -b ↔ a ∣ b
  proof: (Equiv.neg _).exists_congr_left.trans by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_inj, Dvd.dvd]

中文:
定理 dvd_neg
  结论: a ∣ -b ↔ a ∣ b
  证明: (Equiv.neg _).exists_congr_left.trans by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_inj, Dvd.dvd]

Depends on / 依赖: Dvd.dvd, Equiv.neg, Equiv.neg_apply, Equiv.neg_symm, exists_congr_left, exists_congr_left.trans, mul_neg, neg_apply, neg_inj, neg_symm
-/
theorem dvd_neg : a ∣ -b ↔ a ∣ b :=
(Equiv.neg _).exists_congr_left.trans by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_inj, Dvd.dvd]

/-- The negation of an element `a` of a semigroup with a distributive negation divides another
element `b` iff `a` divides `b`. -/
@[simp]
/--
theorem `neg_dvd` / 定理 `neg_dvd`

English:
theorem neg_dvd
  statement: -a ∣ b ↔ a ∣ b
  proof: (Equiv.neg _).exists_congr_left.trans by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_mul, neg_neg, Dvd.dvd]

alias ⟨Dvd.dvd.of_neg_left, Dvd.dvd.neg_left⟩ := neg_dvd

alias ⟨Dvd.dvd.of_neg_right, Dvd.dvd.neg_right⟩ := dvd_neg

中文:
定理 neg_dvd
  结论: -a ∣ b ↔ a ∣ b
  证明: (Equiv.neg _).exists_congr_left.trans by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_mul, neg_neg, Dvd.dvd]

alias ⟨Dvd.dvd.of_neg_left, Dvd.dvd.neg_left⟩ := neg_dvd

alias ⟨Dvd.dvd.of_neg_right, Dvd.dvd.neg_right⟩ := dvd_neg

Depends on / 依赖: Dvd.dvd, Equiv.neg, Equiv.neg_apply, Equiv.neg_symm, exists_congr_left, exists_congr_left.trans, mul_neg, neg_apply, neg_mul, neg_neg, neg_symm
-/
theorem neg_dvd : -a ∣ b ↔ a ∣ b :=
(Equiv.neg _).exists_congr_left.trans by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_mul, neg_neg, Dvd.dvd]

alias ⟨Dvd.dvd.of_neg_left, Dvd.dvd.neg_left⟩ := neg_dvd

alias ⟨Dvd.dvd.of_neg_right, Dvd.dvd.neg_right⟩ := dvd_neg

end Semigroup

section NonUnitalRing

variable [NonUnitalRing α] {a b c : α}

/--
theorem `dvd_sub` / 定理 `dvd_sub`

English:
theorem dvd_sub
  given: (h₁ : a ∣ b) (h₂ : a ∣ c)
  statement: a ∣ b - c
  proof: by
  simpa only [← sub_eq_add_neg] using h₁.add h₂.neg_right

alias Dvd.dvd.sub := dvd_sub

中文:
定理 dvd_sub
  条件: (h₁ : a ∣ b) (h₂ : a ∣ c)
  结论: a ∣ b - c
  证明: by
  simpa only [← sub_eq_add_neg] using h₁.add h₂.neg_right

alias Dvd.dvd.sub := dvd_sub

Depends on / 依赖: neg_right, sub_eq_add_neg
-/
theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  simpa only [← sub_eq_add_neg] using h₁.add h₂.neg_right

alias Dvd.dvd.sub := dvd_sub

/--
theorem `dvd_add_left` / 定理 `dvd_add_left`

English:
theorem dvd_add_left
  given: (h : a ∣ c)
  statement: a ∣ b + c ↔ a ∣ b
  proof: ⟨fun H => by simpa only [add_sub_cancel_right] using dvd_sub H h, fun h₂ => dvd_add h₂ h⟩

中文:
定理 dvd_add_left
  条件: (h : a ∣ c)
  结论: a ∣ b + c ↔ a ∣ b
  证明: ⟨fun H => by simpa only [add_sub_cancel_right] using dvd_sub H h, fun h₂ => dvd_add h₂ h⟩

Depends on / 依赖: add_sub_cancel_right, dvd_add, dvd_sub
-/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  ⟨fun H => by simpa only [add_sub_cancel_right] using dvd_sub H h, fun h₂ => dvd_add h₂ h⟩

/--
theorem `dvd_add_right` / 定理 `dvd_add_right`

English:
theorem dvd_add_right
  given: (h : a ∣ b)
  statement: a ∣ b + c ↔ a ∣ c
  proof: by rw [add_comm]; exact dvd_add_left h

中文:
定理 dvd_add_right
  条件: (h : a ∣ b)
  结论: a ∣ b + c ↔ a ∣ c
  证明: by rw [add_comm]; exact dvd_add_left h

Depends on / 依赖: add_comm, dvd_add_left
-/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := by rw [add_comm]; exact dvd_add_left h

/--
theorem `dvd_sub_left` / 定理 `dvd_sub_left`

English:
theorem dvd_sub_left
  given: (h : a ∣ c)
  statement: a ∣ b - c ↔ a ∣ b
  proof: by
  simpa only [← sub_eq_add_neg] using dvd_add_left (dvd_neg.2 h)

中文:
定理 dvd_sub_left
  条件: (h : a ∣ c)
  结论: a ∣ b - c ↔ a ∣ b
  证明: by
  simpa only [← sub_eq_add_neg] using dvd_add_left (dvd_neg.2 h)

Depends on / 依赖: dvd_add_left, dvd_neg, sub_eq_add_neg
-/
theorem dvd_sub_left (h : a ∣ c) : a ∣ b - c ↔ a ∣ b := by
  simpa only [← sub_eq_add_neg] using dvd_add_left (dvd_neg.2 h)

/--
theorem `dvd_sub_right` / 定理 `dvd_sub_right`

English:
theorem dvd_sub_right
  given: (h : a ∣ b)
  statement: a ∣ b - c ↔ a ∣ c
  proof: by
  rw [sub_eq_add_neg]; rw [dvd_add_right h]; rw [dvd_neg]

中文:
定理 dvd_sub_right
  条件: (h : a ∣ b)
  结论: a ∣ b - c ↔ a ∣ c
  证明: by
  rw [sub_eq_add_neg]; rw [dvd_add_right h]; rw [dvd_neg]

Depends on / 依赖: dvd_add_right, dvd_neg, sub_eq_add_neg
-/
theorem dvd_sub_right (h : a ∣ b) : a ∣ b - c ↔ a ∣ c := by
  rw [sub_eq_add_neg]; rw [dvd_add_right h]; rw [dvd_neg]

/--
theorem `dvd_iff_dvd_of_dvd_sub` / 定理 `dvd_iff_dvd_of_dvd_sub`

English:
theorem dvd_iff_dvd_of_dvd_sub
  given: (h : a ∣ b - c)
  statement: a ∣ b ↔ a ∣ c
  proof: by
  rw [← sub_add_cancel b c]; rw [dvd_add_right h]

中文:
定理 dvd_iff_dvd_of_dvd_sub
  条件: (h : a ∣ b - c)
  结论: a ∣ b ↔ a ∣ c
  证明: by
  rw [← sub_add_cancel b c]; rw [dvd_add_right h]

Depends on / 依赖: dvd_add_right, sub_add_cancel
-/
theorem dvd_iff_dvd_of_dvd_sub (h : a ∣ b - c) : a ∣ b ↔ a ∣ c := by
  rw [← sub_add_cancel b c]; rw [dvd_add_right h]

/--
theorem `dvd_sub_comm` / 定理 `dvd_sub_comm`

English:
theorem dvd_sub_comm
  statement: a ∣ b - c ↔ a ∣ c - b
  proof: by rw [← dvd_neg, neg_sub]

中文:
定理 dvd_sub_comm
  结论: a ∣ b - c ↔ a ∣ c - b
  证明: by rw [← dvd_neg, neg_sub]

Depends on / 依赖: dvd_neg, neg_sub
-/
theorem dvd_sub_comm : a ∣ b - c ↔ a ∣ c - b := by rw [← dvd_neg, neg_sub]

end NonUnitalRing

section Ring

variable [Ring α] {a b : α}

/-- An element a divides the sum a + b if and only if a divides b. -/
@[simp]
/--
theorem `dvd_add_self_left` / 定理 `dvd_add_self_left`

English:
theorem dvd_add_self_left
  given: {a b : α}
  statement: a ∣ a + b ↔ a ∣ b
  proof: dvd_add_right (dvd_refl a)

中文:
定理 dvd_add_self_left
  条件: {a b : α}
  结论: a ∣ a + b ↔ a ∣ b
  证明: dvd_add_right (dvd_refl a)

Depends on / 依赖: dvd_add_right, dvd_refl
-/
theorem dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
  dvd_add_right (dvd_refl a)

/-- An element a divides the sum b + a if and only if a divides b. -/
@[simp]
/--
theorem `dvd_add_self_right` / 定理 `dvd_add_self_right`

English:
theorem dvd_add_self_right
  given: {a b : α}
  statement: a ∣ b + a ↔ a ∣ b
  proof: dvd_add_left (dvd_refl a)

中文:
定理 dvd_add_self_right
  条件: {a b : α}
  结论: a ∣ b + a ↔ a ∣ b
  证明: dvd_add_left (dvd_refl a)

Depends on / 依赖: dvd_add_left, dvd_refl
-/
theorem dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
  dvd_add_left (dvd_refl a)

/-- An element `a` divides the difference `a - b` if and only if `a` divides `b`. -/
@[simp]
/--
theorem `dvd_sub_self_left` / 定理 `dvd_sub_self_left`

English:
theorem dvd_sub_self_left
  statement: a ∣ a - b ↔ a ∣ b
  proof: dvd_sub_right dvd_rfl

中文:
定理 dvd_sub_self_left
  结论: a ∣ a - b ↔ a ∣ b
  证明: dvd_sub_right dvd_rfl

Depends on / 依赖: dvd_rfl, dvd_sub_right
-/
theorem dvd_sub_self_left : a ∣ a - b ↔ a ∣ b :=
  dvd_sub_right dvd_rfl

/-- An element `a` divides the difference `b - a` if and only if `a` divides `b`. -/
@[simp]
/--
theorem `dvd_sub_self_right` / 定理 `dvd_sub_self_right`

English:
theorem dvd_sub_self_right
  statement: a ∣ b - a ↔ a ∣ b
  proof: dvd_sub_left dvd_rfl

中文:
定理 dvd_sub_self_right
  结论: a ∣ b - a ↔ a ∣ b
  证明: dvd_sub_left dvd_rfl

Depends on / 依赖: dvd_rfl, dvd_sub_left
-/
theorem dvd_sub_self_right : a ∣ b - a ↔ a ∣ b :=
  dvd_sub_left dvd_rfl

end Ring

section NonUnitalCommRing

variable [NonUnitalCommRing α]

/--
theorem `dvd_mul_sub_mul` / 定理 `dvd_mul_sub_mul`

English:
theorem dvd_mul_sub_mul
  given: {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y)
  proof: by
  convert dvd_add (hxy.mul_left a) (hab.mul_right y)
  rw [mul_sub_left_distrib]; rw [mul_sub_right_distrib]
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left]

中文:
定理 dvd_mul_sub_mul
  条件: {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y)
  证明: by
  convert dvd_add (hxy.mul_left a) (hab.mul_right y)
  rw [mul_sub_left_distrib]; rw [mul_sub_right_distrib]
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left]

Depends on / 依赖: add_assoc, convert, dvd_add, hab.mul_right, hxy.mul_left, mul_left, mul_right, mul_sub_left_distrib, mul_sub_right_distrib, neg_add_cancel_left, sub_eq_add_neg
-/
theorem dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) :
    k ∣ a * x - b * y := by
  convert dvd_add (hxy.mul_left a) (hab.mul_right y)
  rw [mul_sub_left_distrib]; rw [mul_sub_right_distrib]
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left]

end NonUnitalCommRing
