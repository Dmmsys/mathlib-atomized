/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Module.Synonym
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Order.Monotone.Monovary

/-!
# Monovarying functions and algebraic operations

This file characterises the interaction of ordered algebraic structures with monovariance
of functions.

## See also

`Mathlib.Algebra.Order.Rearrangement` for the n-ary rearrangement inequality
-/

public section

variable {ι α β : Type*}

/-! ### Algebraic operations on monovarying functions -/

section OrderedCommGroup

section
variable [CommGroup α] [Preorder α] [IsOrderedMonoid α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι -> α} {g : ι -> β}

@[to_additive (attr := simp)]
/--
lemma `monovaryOn_inv_left` / 引理 `monovaryOn_inv_left`

English:
lemma monovaryOn_inv_left
  statement: MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s
  proof: by
  simp [MonovaryOn, AntivaryOn]

@[to_additive (attr := simp)]

中文:
引理 monovaryOn_inv_left
  结论: MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s
  证明: by
  simp [MonovaryOn, AntivaryOn]

@[to_additive (attr := simp)]

Depends on / 依赖: AntivaryOn, MonovaryOn
-/
lemma monovaryOn_inv_left : MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s := by
  simp [MonovaryOn, AntivaryOn]

@[to_additive (attr := simp)]
/--
lemma `antivaryOn_inv_left` / 引理 `antivaryOn_inv_left`

English:
lemma antivaryOn_inv_left
  statement: AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s
  proof: by
  simp [MonovaryOn, AntivaryOn]

中文:
引理 antivaryOn_inv_left
  结论: AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s
  证明: by
  simp [MonovaryOn, AntivaryOn]

Depends on / 依赖: AntivaryOn, IsUnit, IsUnit.mul_left_inj, MonovaryOn, T_zero, _mul_T, isUnit_T, mul_T_assoc, mul_left_inj, mul_one, neg_add_cancel
-/
lemma antivaryOn_inv_left : AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s := by
  simp [MonovaryOn, AntivaryOn]

/--
lemma `monovary_inv_left` / 引理 `monovary_inv_left`

English:
lemma monovary_inv_left
  statement: Monovary f⁻¹ g ↔ Antivary f g
  proof: by
  simp [Monovary, Antivary]

中文:
引理 monovary_inv_left
  结论: Monovary f⁻¹ g ↔ Antivary f g
  证明: by
  simp [Monovary, Antivary]

Depends on / 依赖: one_mul, toLaurent_one
-/
@[to_additive (attr := simp)] lemma monovary_inv_left : Monovary f⁻¹ g ↔ Antivary f g := by
  simp [Monovary, Antivary]

/--
lemma `antivary_inv_left` / 引理 `antivary_inv_left`

English:
lemma antivary_inv_left
  statement: Antivary f⁻¹ g ↔ Monovary f g
  proof: by
  simp [Monovary, Antivary]

中文:
引理 antivary_inv_left
  结论: Antivary f⁻¹ g ↔ Monovary f g
  证明: by
  simp [Monovary, Antivary]

Depends on / 依赖: _one_X_pow, convert, pow_one
-/
@[to_additive (attr := simp)] lemma antivary_inv_left : Antivary f⁻¹ g ↔ Monovary f g := by
  simp [Monovary, Antivary]

/--
lemma `MonovaryOn.mul_left` / 引理 `MonovaryOn.mul_left`

English:
lemma MonovaryOn.mul_left
  given: (h₁ : MonovaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s)
  proof: fun _i hi _j hj hij => mul_le_mul' (h₁ hi hj hij) (h₂ hi hj hij)

中文:
引理 MonovaryOn.mul_left
  条件: (h₁ : MonovaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s)
  证明: fun _i hi _j hj hij => mul_le_mul' (h₁ hi hj hij) (h₂ hi hj hij)
-/
@[to_additive] lemma MonovaryOn.mul_left (h₁ : MonovaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) :
    MonovaryOn (f₁ * f₂) g s := fun _i hi _j hj hij => mul_le_mul' (h₁ hi hj hij) (h₂ hi hj hij)

/--
lemma `AntivaryOn.mul_left` / 引理 `AntivaryOn.mul_left`

English:
lemma AntivaryOn.mul_left
  given: (h₁ : AntivaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s)
  proof: fun _i hi _j hj hij => mul_le_mul' (h₁ hi hj hij) (h₂ hi hj hij)

中文:
引理 AntivaryOn.mul_left
  条件: (h₁ : AntivaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s)
  证明: fun _i hi _j hj hij => mul_le_mul' (h₁ hi hj hij) (h₂ hi hj hij)
-/
@[to_additive] lemma AntivaryOn.mul_left (h₁ : AntivaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) :
    AntivaryOn (f₁ * f₂) g s := fun _i hi _j hj hij => mul_le_mul' (h₁ hi hj hij) (h₂ hi hj hij)

/--
lemma `MonovaryOn.div_left` / 引理 `MonovaryOn.div_left`

English:
lemma MonovaryOn.div_left
  given: (h₁ : MonovaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s)
  proof: fun _i hi _j hj hij => div_le_div'' (h₁ hi hj hij) (h₂ hi hj hij)

中文:
引理 MonovaryOn.div_left
  条件: (h₁ : MonovaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s)
  证明: fun _i hi _j hj hij => div_le_div'' (h₁ hi hj hij) (h₂ hi hj hij)
-/
@[to_additive] lemma MonovaryOn.div_left (h₁ : MonovaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) :
    MonovaryOn (f₁ / f₂) g s := fun _i hi _j hj hij => div_le_div'' (h₁ hi hj hij) (h₂ hi hj hij)

/--
lemma `AntivaryOn.div_left` / 引理 `AntivaryOn.div_left`

English:
lemma AntivaryOn.div_left
  given: (h₁ : AntivaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s)
  proof: fun _i hi _j hj hij => div_le_div'' (h₁ hi hj hij) (h₂ hi hj hij)

中文:
引理 AntivaryOn.div_left
  条件: (h₁ : AntivaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s)
  证明: fun _i hi _j hj hij => div_le_div'' (h₁ hi hj hij) (h₂ hi hj hij)
-/
@[to_additive] lemma AntivaryOn.div_left (h₁ : AntivaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) :
    AntivaryOn (f₁ / f₂) g s := fun _i hi _j hj hij => div_le_div'' (h₁ hi hj hij) (h₂ hi hj hij)

/--
lemma `MonovaryOn.pow_left` / 引理 `MonovaryOn.pow_left`

English:
lemma MonovaryOn.pow_left
  given: (hfg : MonovaryOn f g s) (n : Nat)
  proof: fun _i hi _j hj hij => pow_le_pow_left' (hfg hi hj hij) _

中文:
引理 MonovaryOn.pow_left
  条件: (hfg : MonovaryOn f g s) (n : 自然数)
  证明: fun _i hi _j hj hij => pow_le_pow_left' (hfg hi hj hij) _
-/
@[to_additive] lemma MonovaryOn.pow_left (hfg : MonovaryOn f g s) (n : Nat) :
    MonovaryOn (f ^ n) g s := fun _i hi _j hj hij => pow_le_pow_left' (hfg hi hj hij) _

/--
lemma `AntivaryOn.pow_left` / 引理 `AntivaryOn.pow_left`

English:
lemma AntivaryOn.pow_left
  given: (hfg : AntivaryOn f g s) (n : Nat)
  proof: fun _i hi _j hj hij => pow_le_pow_left' (hfg hi hj hij) _

@[to_additive]

中文:
引理 AntivaryOn.pow_left
  条件: (hfg : AntivaryOn f g s) (n : 自然数)
  证明: fun _i hi _j hj hij => pow_le_pow_left' (hfg hi hj hij) _

@[to_additive]
-/
@[to_additive] lemma AntivaryOn.pow_left (hfg : AntivaryOn f g s) (n : Nat) :
    AntivaryOn (f ^ n) g s := fun _i hi _j hj hij => pow_le_pow_left' (hfg hi hj hij) _

@[to_additive]
/--
lemma `Monovary.mul_left` / 引理 `Monovary.mul_left`

English:
lemma Monovary.mul_left
  given: (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g)
  statement: Monovary (f₁ * f₂) g
  proof: fun _i _j hij => mul_le_mul' (h₁ hij) (h₂ hij)

@[to_additive]

中文:
引理 Monovary.mul_left
  条件: (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g)
  结论: Monovary (f₁ * f₂) g
  证明: fun _i _j hij => mul_le_mul' (h₁ hij) (h₂ hij)

@[to_additive]

Depends on / 依赖: mul_le_mul
-/
lemma Monovary.mul_left (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g) : Monovary (f₁ * f₂) g :=
  fun _i _j hij => mul_le_mul' (h₁ hij) (h₂ hij)

@[to_additive]
/--
lemma `Antivary.mul_left` / 引理 `Antivary.mul_left`

English:
lemma Antivary.mul_left
  given: (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g)
  statement: Antivary (f₁ * f₂) g
  proof: fun _i _j hij => mul_le_mul' (h₁ hij) (h₂ hij)

@[to_additive]

中文:
引理 Antivary.mul_left
  条件: (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g)
  结论: Antivary (f₁ * f₂) g
  证明: fun _i _j hij => mul_le_mul' (h₁ hij) (h₂ hij)

@[to_additive]

Depends on / 依赖: mul_le_mul
-/
lemma Antivary.mul_left (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g) : Antivary (f₁ * f₂) g :=
  fun _i _j hij => mul_le_mul' (h₁ hij) (h₂ hij)

@[to_additive]
/--
lemma `Monovary.div_left` / 引理 `Monovary.div_left`

English:
lemma Monovary.div_left
  given: (h₁ : Monovary f₁ g) (h₂ : Antivary f₂ g)
  statement: Monovary (f₁ / f₂) g
  proof: fun _i _j hij => div_le_div'' (h₁ hij) (h₂ hij)

@[to_additive]

中文:
引理 Monovary.div_left
  条件: (h₁ : Monovary f₁ g) (h₂ : Antivary f₂ g)
  结论: Monovary (f₁ / f₂) g
  证明: fun _i _j hij => div_le_div'' (h₁ hij) (h₂ hij)

@[to_additive]

Depends on / 依赖: div_le_div
-/
lemma Monovary.div_left (h₁ : Monovary f₁ g) (h₂ : Antivary f₂ g) : Monovary (f₁ / f₂) g :=
  fun _i _j hij => div_le_div'' (h₁ hij) (h₂ hij)

@[to_additive]
/--
lemma `Antivary.div_left` / 引理 `Antivary.div_left`

English:
lemma Antivary.div_left
  given: (h₁ : Antivary f₁ g) (h₂ : Monovary f₂ g)
  statement: Antivary (f₁ / f₂) g
  proof: fun _i _j hij => div_le_div'' (h₁ hij) (h₂ hij)

中文:
引理 Antivary.div_left
  条件: (h₁ : Antivary f₁ g) (h₂ : Monovary f₂ g)
  结论: Antivary (f₁ / f₂) g
  证明: fun _i _j hij => div_le_div'' (h₁ hij) (h₂ hij)

Depends on / 依赖: div_le_div
-/
lemma Antivary.div_left (h₁ : Antivary f₁ g) (h₂ : Monovary f₂ g) : Antivary (f₁ / f₂) g :=
  fun _i _j hij => div_le_div'' (h₁ hij) (h₂ hij)

/--
lemma `Monovary.pow_left` / 引理 `Monovary.pow_left`

English:
lemma Monovary.pow_left
  given: (hfg : Monovary f g) (n : Nat)
  statement: Monovary (f ^ n) g
  proof: fun _i _j hij => pow_le_pow_left' (hfg hij) _

中文:
引理 Monovary.pow_left
  条件: (hfg : Monovary f g) (n : 自然数)
  结论: Monovary (f ^ n) g
  证明: fun _i _j hij => pow_le_pow_left' (hfg hij) _
-/
@[to_additive] lemma Monovary.pow_left (hfg : Monovary f g) (n : Nat) : Monovary (f ^ n) g :=
  fun _i _j hij => pow_le_pow_left' (hfg hij) _

/--
lemma `Antivary.pow_left` / 引理 `Antivary.pow_left`

English:
lemma Antivary.pow_left
  given: (hfg : Antivary f g) (n : Nat)
  statement: Antivary (f ^ n) g
  proof: fun _i _j hij => pow_le_pow_left' (hfg hij) _

中文:
引理 Antivary.pow_left
  条件: (hfg : Antivary f g) (n : 自然数)
  结论: Antivary (f ^ n) g
  证明: fun _i _j hij => pow_le_pow_left' (hfg hij) _
-/
@[to_additive] lemma Antivary.pow_left (hfg : Antivary f g) (n : Nat) : Antivary (f ^ n) g :=
  fun _i _j hij => pow_le_pow_left' (hfg hij) _

end

section
variable [PartialOrder α] [CommGroup β] [PartialOrder β] [IsOrderedMonoid β]
  {s : Set ι} {f f₁ f₂ : ι -> α} {g : ι -> β}

@[to_additive (attr := simp)]
/--
lemma `monovaryOn_inv_right` / 引理 `monovaryOn_inv_right`

English:
lemma monovaryOn_inv_right
  statement: MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s
  proof: by
  simpa [MonovaryOn, AntivaryOn] using forall₂_comm

@[to_additive (attr := simp)]

中文:
引理 monovaryOn_inv_right
  结论: MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s
  证明: by
  simpa [MonovaryOn, AntivaryOn] using forall₂_comm

@[to_additive (attr := simp)]

Depends on / 依赖: AntivaryOn, MonovaryOn
-/
lemma monovaryOn_inv_right : MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s := by
  simpa [MonovaryOn, AntivaryOn] using forall₂_comm

@[to_additive (attr := simp)]
/--
lemma `antivaryOn_inv_right` / 引理 `antivaryOn_inv_right`

English:
lemma antivaryOn_inv_right
  statement: AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s
  proof: by
  simpa [MonovaryOn, AntivaryOn] using forall₂_comm

中文:
引理 antivaryOn_inv_right
  结论: AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s
  证明: by
  simpa [MonovaryOn, AntivaryOn] using forall₂_comm

Depends on / 依赖: AntivaryOn, MonovaryOn
-/
lemma antivaryOn_inv_right : AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s := by
  simpa [MonovaryOn, AntivaryOn] using forall₂_comm

/--
lemma `monovary_inv_right` / 引理 `monovary_inv_right`

English:
lemma monovary_inv_right
  statement: Monovary f g⁻¹ ↔ Antivary f g
  proof: by
  simpa [Monovary, Antivary] using forall_comm

中文:
引理 monovary_inv_right
  结论: Monovary f g⁻¹ ↔ Antivary f g
  证明: by
  simpa [Monovary, Antivary] using forall_comm
-/
@[to_additive (attr := simp)] lemma monovary_inv_right : Monovary f g⁻¹ ↔ Antivary f g := by
  simpa [Monovary, Antivary] using forall_comm

/--
lemma `antivary_inv_right` / 引理 `antivary_inv_right`

English:
lemma antivary_inv_right
  statement: Antivary f g⁻¹ ↔ Monovary f g
  proof: by
  simpa [Monovary, Antivary] using forall_comm

中文:
引理 antivary_inv_right
  结论: Antivary f g⁻¹ ↔ Monovary f g
  证明: by
  simpa [Monovary, Antivary] using forall_comm
-/
@[to_additive (attr := simp)] lemma antivary_inv_right : Antivary f g⁻¹ ↔ Monovary f g := by
  simpa [Monovary, Antivary] using forall_comm
end

section
variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  [CommGroup β] [PartialOrder β] [IsOrderedMonoid β]
  {s : Set ι} {f f₁ f₂ : ι -> α} {g : ι -> β}

/--
lemma `monovaryOn_inv` / 引理 `monovaryOn_inv`

English:
lemma monovaryOn_inv
  statement: MonovaryOn f⁻¹ g⁻¹ s ↔ MonovaryOn f g s
  proof: by simp

中文:
引理 monovaryOn_inv
  结论: MonovaryOn f⁻¹ g⁻¹ s ↔ MonovaryOn f g s
  证明: by simp
-/
@[to_additive] lemma monovaryOn_inv : MonovaryOn f⁻¹ g⁻¹ s ↔ MonovaryOn f g s := by simp
/--
lemma `antivaryOn_inv` / 引理 `antivaryOn_inv`

English:
lemma antivaryOn_inv
  statement: AntivaryOn f⁻¹ g⁻¹ s ↔ AntivaryOn f g s
  proof: by simp

中文:
引理 antivaryOn_inv
  结论: AntivaryOn f⁻¹ g⁻¹ s ↔ AntivaryOn f g s
  证明: by simp
-/
@[to_additive] lemma antivaryOn_inv : AntivaryOn f⁻¹ g⁻¹ s ↔ AntivaryOn f g s := by simp

/--
lemma `monovary_inv` / 引理 `monovary_inv`

English:
lemma monovary_inv
  statement: Monovary f⁻¹ g⁻¹ ↔ Monovary f g
  proof: by simp

中文:
引理 monovary_inv
  结论: Monovary f⁻¹ g⁻¹ ↔ Monovary f g
  证明: by simp
-/
@[to_additive] lemma monovary_inv : Monovary f⁻¹ g⁻¹ ↔ Monovary f g := by simp
/--
lemma `antivary_inv` / 引理 `antivary_inv`

English:
lemma antivary_inv
  statement: Antivary f⁻¹ g⁻¹ ↔ Antivary f g
  proof: by simp

中文:
引理 antivary_inv
  结论: Antivary f⁻¹ g⁻¹ ↔ Antivary f g
  证明: by simp
-/
@[to_additive] lemma antivary_inv : Antivary f⁻¹ g⁻¹ ↔ Antivary f g := by simp

end

@[to_additive] alias ⟨MonovaryOn.of_inv_left, AntivaryOn.inv_left⟩ := monovaryOn_inv_left
@[to_additive] alias ⟨AntivaryOn.of_inv_left, MonovaryOn.inv_left⟩ := antivaryOn_inv_left
@[to_additive] alias ⟨MonovaryOn.of_inv_right, AntivaryOn.inv_right⟩ := monovaryOn_inv_right
@[to_additive] alias ⟨AntivaryOn.of_inv_right, MonovaryOn.inv_right⟩ := antivaryOn_inv_right
@[to_additive] alias ⟨MonovaryOn.of_inv, MonovaryOn.inv⟩ := monovaryOn_inv
@[to_additive] alias ⟨AntivaryOn.of_inv, AntivaryOn.inv⟩ := antivaryOn_inv
@[to_additive] alias ⟨Monovary.of_inv_left, Antivary.inv_left⟩ := monovary_inv_left
@[to_additive] alias ⟨Antivary.of_inv_left, Monovary.inv_left⟩ := antivary_inv_left
@[to_additive] alias ⟨Monovary.of_inv_right, Antivary.inv_right⟩ := monovary_inv_right
@[to_additive] alias ⟨Antivary.of_inv_right, Monovary.inv_right⟩ := antivary_inv_right
@[to_additive] alias ⟨Monovary.of_inv, Monovary.inv⟩ := monovary_inv
@[to_additive] alias ⟨Antivary.of_inv, Antivary.inv⟩ := antivary_inv

end OrderedCommGroup

section LinearOrderedCommGroup
variable [Preorder α] [CommGroup β] [LinearOrder β] [IsOrderedMonoid β] {s : Set ι} {f : ι -> α}
  {g g₁ g₂ : ι -> β}

/--
lemma `MonovaryOn.mul_right` / 引理 `MonovaryOn.mul_right`

English:
lemma MonovaryOn.mul_right
  given: (h₁ : MonovaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s)
  proof: fun _i hi _j hj hij => (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) h₂ hi hj

中文:
引理 MonovaryOn.mul_right
  条件: (h₁ : MonovaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s)
  证明: fun _i hi _j hj hij => (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) h₂ hi hj
-/
@[to_additive] lemma MonovaryOn.mul_right (h₁ : MonovaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) :
    MonovaryOn f (g₁ * g₂) s :=
fun _i hi _j hj hij => (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) h₂ hi hj

/--
lemma `AntivaryOn.mul_right` / 引理 `AntivaryOn.mul_right`

English:
lemma AntivaryOn.mul_right
  given: (h₁ : AntivaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s)
  proof: fun _i hi _j hj hij => (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) h₂ hi hj

中文:
引理 AntivaryOn.mul_right
  条件: (h₁ : AntivaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s)
  证明: fun _i hi _j hj hij => (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) h₂ hi hj
-/
@[to_additive] lemma AntivaryOn.mul_right (h₁ : AntivaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) :
    AntivaryOn f (g₁ * g₂) s :=
fun _i hi _j hj hij => (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) h₂ hi hj

/--
lemma `MonovaryOn.div_right` / 引理 `MonovaryOn.div_right`

English:
lemma MonovaryOn.div_right
  given: (h₁ : MonovaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s)
  proof: fun _i hi _j hj hij => (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) h₂ hj hi

中文:
引理 MonovaryOn.div_right
  条件: (h₁ : MonovaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s)
  证明: fun _i hi _j hj hij => (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) h₂ hj hi
-/
@[to_additive] lemma MonovaryOn.div_right (h₁ : MonovaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) :
    MonovaryOn f (g₁ / g₂) s :=
fun _i hi _j hj hij => (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) h₂ hj hi

/--
lemma `AntivaryOn.div_right` / 引理 `AntivaryOn.div_right`

English:
lemma AntivaryOn.div_right
  given: (h₁ : AntivaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s)
  proof: fun _i hi _j hj hij => (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) h₂ hj hi

中文:
引理 AntivaryOn.div_right
  条件: (h₁ : AntivaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s)
  证明: fun _i hi _j hj hij => (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) h₂ hj hi
-/
@[to_additive] lemma AntivaryOn.div_right (h₁ : AntivaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) :
    AntivaryOn f (g₁ / g₂) s :=
fun _i hi _j hj hij => (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) h₂ hj hi

/--
lemma `MonovaryOn.pow_right` / 引理 `MonovaryOn.pow_right`

English:
lemma MonovaryOn.pow_right
  given: (hfg : MonovaryOn f g s) (n : Nat)
  proof: fun _i hi _j hj hij => hfg hi hj lt_of_pow_lt_pow_left' _ hij

中文:
引理 MonovaryOn.pow_right
  条件: (hfg : MonovaryOn f g s) (n : 自然数)
  证明: fun _i hi _j hj hij => hfg hi hj lt_of_pow_lt_pow_left' _ hij
-/
@[to_additive] lemma MonovaryOn.pow_right (hfg : MonovaryOn f g s) (n : Nat) :
MonovaryOn f (g ^ n) s := fun _i hi _j hj hij => hfg hi hj lt_of_pow_lt_pow_left' _ hij

/--
lemma `AntivaryOn.pow_right` / 引理 `AntivaryOn.pow_right`

English:
lemma AntivaryOn.pow_right
  given: (hfg : AntivaryOn f g s) (n : Nat)
  proof: fun _i hi _j hj hij => hfg hi hj lt_of_pow_lt_pow_left' _ hij

中文:
引理 AntivaryOn.pow_right
  条件: (hfg : AntivaryOn f g s) (n : 自然数)
  证明: fun _i hi _j hj hij => hfg hi hj lt_of_pow_lt_pow_left' _ hij
-/
@[to_additive] lemma AntivaryOn.pow_right (hfg : AntivaryOn f g s) (n : Nat) :
AntivaryOn f (g ^ n) s := fun _i hi _j hj hij => hfg hi hj lt_of_pow_lt_pow_left' _ hij

/--
lemma `Monovary.mul_right` / 引理 `Monovary.mul_right`

English:
lemma Monovary.mul_right
  given: (h₁ : Monovary f g₁) (h₂ : Monovary f g₂)
  proof: fun _i _j hij => (lt_or_lt_of_mul_lt_mul hij).elim (fun h => h₁ h) fun h => h₂ h

中文:
引理 Monovary.mul_right
  条件: (h₁ : Monovary f g₁) (h₂ : Monovary f g₂)
  证明: fun _i _j hij => (lt_or_lt_of_mul_lt_mul hij).elim (fun h => h₁ h) fun h => h₂ h
-/
@[to_additive] lemma Monovary.mul_right (h₁ : Monovary f g₁) (h₂ : Monovary f g₂) :
    Monovary f (g₁ * g₂) :=
  fun _i _j hij => (lt_or_lt_of_mul_lt_mul hij).elim (fun h => h₁ h) fun h => h₂ h

/--
lemma `Antivary.mul_right` / 引理 `Antivary.mul_right`

English:
lemma Antivary.mul_right
  given: (h₁ : Antivary f g₁) (h₂ : Antivary f g₂)
  proof: fun _i _j hij => (lt_or_lt_of_mul_lt_mul hij).elim (fun h => h₁ h) fun h => h₂ h

中文:
引理 Antivary.mul_right
  条件: (h₁ : Antivary f g₁) (h₂ : Antivary f g₂)
  证明: fun _i _j hij => (lt_or_lt_of_mul_lt_mul hij).elim (fun h => h₁ h) fun h => h₂ h
-/
@[to_additive] lemma Antivary.mul_right (h₁ : Antivary f g₁) (h₂ : Antivary f g₂) :
    Antivary f (g₁ * g₂) :=
  fun _i _j hij => (lt_or_lt_of_mul_lt_mul hij).elim (fun h => h₁ h) fun h => h₂ h

/--
lemma `Monovary.div_right` / 引理 `Monovary.div_right`

English:
lemma Monovary.div_right
  given: (h₁ : Monovary f g₁) (h₂ : Antivary f g₂)
  proof: fun _i _j hij => (lt_or_lt_of_div_lt_div hij).elim (fun h => h₁ h) fun h => h₂ h

中文:
引理 Monovary.div_right
  条件: (h₁ : Monovary f g₁) (h₂ : Antivary f g₂)
  证明: fun _i _j hij => (lt_or_lt_of_div_lt_div hij).elim (fun h => h₁ h) fun h => h₂ h
-/
@[to_additive] lemma Monovary.div_right (h₁ : Monovary f g₁) (h₂ : Antivary f g₂) :
    Monovary f (g₁ / g₂) :=
  fun _i _j hij => (lt_or_lt_of_div_lt_div hij).elim (fun h => h₁ h) fun h => h₂ h

/--
lemma `Antivary.div_right` / 引理 `Antivary.div_right`

English:
lemma Antivary.div_right
  given: (h₁ : Antivary f g₁) (h₂ : Monovary f g₂)
  proof: fun _i _j hij => (lt_or_lt_of_div_lt_div hij).elim (fun h => h₁ h) fun h => h₂ h

中文:
引理 Antivary.div_right
  条件: (h₁ : Antivary f g₁) (h₂ : Monovary f g₂)
  证明: fun _i _j hij => (lt_or_lt_of_div_lt_div hij).elim (fun h => h₁ h) fun h => h₂ h
-/
@[to_additive] lemma Antivary.div_right (h₁ : Antivary f g₁) (h₂ : Monovary f g₂) :
    Antivary f (g₁ / g₂) :=
  fun _i _j hij => (lt_or_lt_of_div_lt_div hij).elim (fun h => h₁ h) fun h => h₂ h

/--
lemma `Monovary.pow_right` / 引理 `Monovary.pow_right`

English:
lemma Monovary.pow_right
  given: (hfg : Monovary f g) (n : Nat)
  statement: Monovary f (g ^ n)
  proof: fun _i _j hij => hfg lt_of_pow_lt_pow_left' _ hij

中文:
引理 Monovary.pow_right
  条件: (hfg : Monovary f g) (n : 自然数)
  结论: Monovary f (g ^ n)
  证明: fun _i _j hij => hfg lt_of_pow_lt_pow_left' _ hij
-/
@[to_additive] lemma Monovary.pow_right (hfg : Monovary f g) (n : Nat) : Monovary f (g ^ n) :=
fun _i _j hij => hfg lt_of_pow_lt_pow_left' _ hij

/--
lemma `Antivary.pow_right` / 引理 `Antivary.pow_right`

English:
lemma Antivary.pow_right
  given: (hfg : Antivary f g) (n : Nat)
  statement: Antivary f (g ^ n)
  proof: fun _i _j hij => hfg lt_of_pow_lt_pow_left' _ hij

中文:
引理 Antivary.pow_right
  条件: (hfg : Antivary f g) (n : 自然数)
  结论: Antivary f (g ^ n)
  证明: fun _i _j hij => hfg lt_of_pow_lt_pow_left' _ hij
-/
@[to_additive] lemma Antivary.pow_right (hfg : Antivary f g) (n : Nat) : Antivary f (g ^ n) :=
fun _i _j hij => hfg lt_of_pow_lt_pow_left' _ hij

end LinearOrderedCommGroup

section OrderedSemiring
variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι -> α} {g : ι -> β}

/--
lemma `MonovaryOn.mul_left₀` / 引理 `MonovaryOn.mul_left₀`

English:
lemma MonovaryOn.mul_left₀
  statement: (hf₁ : forall i in s, 0 <= f₁ i) (hf₂ : forall i in s, 0 <= f₂ i)
  proof: fun _i hi _j hj hij => mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hi) (hf₁ _ hj)

中文:
引理 MonovaryOn.mul_left₀
  结论: (hf₁ : 对任意 i in s, 0 <= f₁ i) (hf₂ : 对任意 i in s, 0 <= f₂ i)
  证明: fun _i hi _j hj hij => mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hi) (hf₁ _ hj)

Depends on / 依赖: mul_le_mul
-/
lemma MonovaryOn.mul_left₀ (hf₁ : forall i in s, 0 <= f₁ i) (hf₂ : forall i in s, 0 <= f₂ i)
    (h₁ : MonovaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) : MonovaryOn (f₁ * f₂) g s :=
  fun _i hi _j hj hij => mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hi) (hf₁ _ hj)

/--
lemma `AntivaryOn.mul_left₀` / 引理 `AntivaryOn.mul_left₀`

English:
lemma AntivaryOn.mul_left₀
  statement: (hf₁ : forall i in s, 0 <= f₁ i) (hf₂ : forall i in s, 0 <= f₂ i)
  proof: fun _i hi _j hj hij => mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hj) (hf₁ _ hi)

中文:
引理 AntivaryOn.mul_left₀
  结论: (hf₁ : 对任意 i in s, 0 <= f₁ i) (hf₂ : 对任意 i in s, 0 <= f₂ i)
  证明: fun _i hi _j hj hij => mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hj) (hf₁ _ hi)

Depends on / 依赖: mul_le_mul
-/
lemma AntivaryOn.mul_left₀ (hf₁ : forall i in s, 0 <= f₁ i) (hf₂ : forall i in s, 0 <= f₂ i)
    (h₁ : AntivaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) : AntivaryOn (f₁ * f₂) g s :=
  fun _i hi _j hj hij => mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hj) (hf₁ _ hi)

/--
lemma `MonovaryOn.pow_left₀` / 引理 `MonovaryOn.pow_left₀`

English:
lemma MonovaryOn.pow_left₀
  given: (hf : forall i in s, 0 <= f i) (hfg : MonovaryOn f g s) (n : Nat)
  proof: fun _i hi _j hj hij => pow_le_pow_left₀ (hf _ hi) (hfg hi hj hij) _

中文:
引理 MonovaryOn.pow_left₀
  条件: (hf : 对任意 i in s, 0 <= f i) (hfg : MonovaryOn f g s) (n : 自然数)
  证明: fun _i hi _j hj hij => pow_le_pow_left₀ (hf _ hi) (hfg hi hj hij) _
-/
lemma MonovaryOn.pow_left₀ (hf : forall i in s, 0 <= f i) (hfg : MonovaryOn f g s) (n : Nat) :
    MonovaryOn (f ^ n) g s :=
  fun _i hi _j hj hij => pow_le_pow_left₀ (hf _ hi) (hfg hi hj hij) _

/--
lemma `AntivaryOn.pow_left₀` / 引理 `AntivaryOn.pow_left₀`

English:
lemma AntivaryOn.pow_left₀
  given: (hf : forall i in s, 0 <= f i) (hfg : AntivaryOn f g s) (n : Nat)
  proof: fun _i hi _j hj hij => pow_le_pow_left₀ (hf _ hj) (hfg hi hj hij) _

中文:
引理 AntivaryOn.pow_left₀
  条件: (hf : 对任意 i in s, 0 <= f i) (hfg : AntivaryOn f g s) (n : 自然数)
  证明: fun _i hi _j hj hij => pow_le_pow_left₀ (hf _ hj) (hfg hi hj hij) _
-/
lemma AntivaryOn.pow_left₀ (hf : forall i in s, 0 <= f i) (hfg : AntivaryOn f g s) (n : Nat) :
    AntivaryOn (f ^ n) g s :=
  fun _i hi _j hj hij => pow_le_pow_left₀ (hf _ hj) (hfg hi hj hij) _

/--
lemma `Monovary.mul_left₀` / 引理 `Monovary.mul_left₀`

English:
lemma Monovary.mul_left₀
  given: (hf₁ : 0 <= f₁) (hf₂ : 0 <= f₂) (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g)
  proof: fun _i _j hij => mul_le_mul (h₁ hij) (h₂ hij) (hf₂ _) (hf₁ _)

中文:
引理 Monovary.mul_left₀
  条件: (hf₁ : 0 <= f₁) (hf₂ : 0 <= f₂) (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g)
  证明: fun _i _j hij => mul_le_mul (h₁ hij) (h₂ hij) (hf₂ _) (hf₁ _)

Depends on / 依赖: mul_le_mul
-/
lemma Monovary.mul_left₀ (hf₁ : 0 <= f₁) (hf₂ : 0 <= f₂) (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g) :
    Monovary (f₁ * f₂) g := fun _i _j hij => mul_le_mul (h₁ hij) (h₂ hij) (hf₂ _) (hf₁ _)

/--
lemma `Antivary.mul_left₀` / 引理 `Antivary.mul_left₀`

English:
lemma Antivary.mul_left₀
  given: (hf₁ : 0 <= f₁) (hf₂ : 0 <= f₂) (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g)
  proof: fun _i _j hij => mul_le_mul (h₁ hij) (h₂ hij) (hf₂ _) (hf₁ _)

中文:
引理 Antivary.mul_left₀
  条件: (hf₁ : 0 <= f₁) (hf₂ : 0 <= f₂) (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g)
  证明: fun _i _j hij => mul_le_mul (h₁ hij) (h₂ hij) (hf₂ _) (hf₁ _)

Depends on / 依赖: mul_le_mul
-/
lemma Antivary.mul_left₀ (hf₁ : 0 <= f₁) (hf₂ : 0 <= f₂) (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g) :
    Antivary (f₁ * f₂) g := fun _i _j hij => mul_le_mul (h₁ hij) (h₂ hij) (hf₂ _) (hf₁ _)

/--
lemma `Monovary.pow_left₀` / 引理 `Monovary.pow_left₀`

English:
lemma Monovary.pow_left₀
  given: (hf : 0 <= f) (hfg : Monovary f g) (n : Nat)
  statement: Monovary (f ^ n) g
  proof: fun _i _j hij => pow_le_pow_left₀ (hf _) (hfg hij) _

中文:
引理 Monovary.pow_left₀
  条件: (hf : 0 <= f) (hfg : Monovary f g) (n : 自然数)
  结论: Monovary (f ^ n) g
  证明: fun _i _j hij => pow_le_pow_left₀ (hf _) (hfg hij) _
-/
lemma Monovary.pow_left₀ (hf : 0 <= f) (hfg : Monovary f g) (n : Nat) : Monovary (f ^ n) g :=
  fun _i _j hij => pow_le_pow_left₀ (hf _) (hfg hij) _

/--
lemma `Antivary.pow_left₀` / 引理 `Antivary.pow_left₀`

English:
lemma Antivary.pow_left₀
  given: (hf : 0 <= f) (hfg : Antivary f g) (n : Nat)
  statement: Antivary (f ^ n) g
  proof: fun _i _j hij => pow_le_pow_left₀ (hf _) (hfg hij) _

中文:
引理 Antivary.pow_left₀
  条件: (hf : 0 <= f) (hfg : Antivary f g) (n : 自然数)
  结论: Antivary (f ^ n) g
  证明: fun _i _j hij => pow_le_pow_left₀ (hf _) (hfg hij) _
-/
lemma Antivary.pow_left₀ (hf : 0 <= f) (hfg : Antivary f g) (n : Nat) : Antivary (f ^ n) g :=
  fun _i _j hij => pow_le_pow_left₀ (hf _) (hfg hij) _

end OrderedSemiring

section LinearOrderedSemiring
variable [LinearOrder α] [Semiring β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f : ι -> α} {g g₁ g₂ : ι -> β}

/--
lemma `MonovaryOn.mul_right₀` / 引理 `MonovaryOn.mul_right₀`

English:
lemma MonovaryOn.mul_right₀
  statement: (hg₁ : forall i in s, 0 <= g₁ i) (hg₂ : forall i in s, 0 <= g₂ i)
  proof: (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

中文:
引理 MonovaryOn.mul_right₀
  结论: (hg₁ : 对任意 i in s, 0 <= g₁ i) (hg₂ : 对任意 i in s, 0 <= g₂ i)
  证明: (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

Depends on / 依赖: symm.mul_left
-/
lemma MonovaryOn.mul_right₀ (hg₁ : forall i in s, 0 <= g₁ i) (hg₂ : forall i in s, 0 <= g₂ i)
    (h₁ : MonovaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) : MonovaryOn f (g₁ * g₂) s :=
  (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

/--
lemma `AntivaryOn.mul_right₀` / 引理 `AntivaryOn.mul_right₀`

English:
lemma AntivaryOn.mul_right₀
  statement: (hg₁ : forall i in s, 0 <= g₁ i) (hg₂ : forall i in s, 0 <= g₂ i)
  proof: (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

中文:
引理 AntivaryOn.mul_right₀
  结论: (hg₁ : 对任意 i in s, 0 <= g₁ i) (hg₂ : 对任意 i in s, 0 <= g₂ i)
  证明: (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

Depends on / 依赖: symm.mul_left
-/
lemma AntivaryOn.mul_right₀ (hg₁ : forall i in s, 0 <= g₁ i) (hg₂ : forall i in s, 0 <= g₂ i)
    (h₁ : AntivaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) : AntivaryOn f (g₁ * g₂) s :=
  (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

/--
lemma `MonovaryOn.pow_right₀` / 引理 `MonovaryOn.pow_right₀`

English:
lemma MonovaryOn.pow_right₀
  given: (hg : forall i in s, 0 <= g i) (hfg : MonovaryOn f g s) (n : Nat)
  proof: (hfg.symm.pow_left₀ hg _).symm

中文:
引理 MonovaryOn.pow_right₀
  条件: (hg : 对任意 i in s, 0 <= g i) (hfg : MonovaryOn f g s) (n : 自然数)
  证明: (hfg.symm.pow_left₀ hg _).symm

Depends on / 依赖: hfg.symm.pow_left
-/
lemma MonovaryOn.pow_right₀ (hg : forall i in s, 0 <= g i) (hfg : MonovaryOn f g s) (n : Nat) :
    MonovaryOn f (g ^ n) s := (hfg.symm.pow_left₀ hg _).symm

/--
lemma `AntivaryOn.pow_right₀` / 引理 `AntivaryOn.pow_right₀`

English:
lemma AntivaryOn.pow_right₀
  given: (hg : forall i in s, 0 <= g i) (hfg : AntivaryOn f g s) (n : Nat)
  proof: (hfg.symm.pow_left₀ hg _).symm

中文:
引理 AntivaryOn.pow_right₀
  条件: (hg : 对任意 i in s, 0 <= g i) (hfg : AntivaryOn f g s) (n : 自然数)
  证明: (hfg.symm.pow_left₀ hg _).symm

Depends on / 依赖: hfg.symm.pow_left
-/
lemma AntivaryOn.pow_right₀ (hg : forall i in s, 0 <= g i) (hfg : AntivaryOn f g s) (n : Nat) :
    AntivaryOn f (g ^ n) s := (hfg.symm.pow_left₀ hg _).symm

/--
lemma `Monovary.mul_right₀` / 引理 `Monovary.mul_right₀`

English:
lemma Monovary.mul_right₀
  given: (hg₁ : 0 <= g₁) (hg₂ : 0 <= g₂) (h₁ : Monovary f g₁) (h₂ : Monovary f g₂)
  proof: (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

中文:
引理 Monovary.mul_right₀
  条件: (hg₁ : 0 <= g₁) (hg₂ : 0 <= g₂) (h₁ : Monovary f g₁) (h₂ : Monovary f g₂)
  证明: (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

Depends on / 依赖: symm.mul_left
-/
lemma Monovary.mul_right₀ (hg₁ : 0 <= g₁) (hg₂ : 0 <= g₂) (h₁ : Monovary f g₁) (h₂ : Monovary f g₂) :
    Monovary f (g₁ * g₂) := (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

/--
lemma `Antivary.mul_right₀` / 引理 `Antivary.mul_right₀`

English:
lemma Antivary.mul_right₀
  given: (hg₁ : 0 <= g₁) (hg₂ : 0 <= g₂) (h₁ : Antivary f g₁) (h₂ : Antivary f g₂)
  proof: (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

中文:
引理 Antivary.mul_right₀
  条件: (hg₁ : 0 <= g₁) (hg₂ : 0 <= g₂) (h₁ : Antivary f g₁) (h₂ : Antivary f g₂)
  证明: (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

Depends on / 依赖: symm.mul_left
-/
lemma Antivary.mul_right₀ (hg₁ : 0 <= g₁) (hg₂ : 0 <= g₂) (h₁ : Antivary f g₁) (h₂ : Antivary f g₂) :
    Antivary f (g₁ * g₂) := (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

/--
lemma `Monovary.pow_right₀` / 引理 `Monovary.pow_right₀`

English:
lemma Monovary.pow_right₀
  given: (hg : 0 <= g) (hfg : Monovary f g) (n : Nat)
  statement: Monovary f (g ^ n)
  proof: (hfg.symm.pow_left₀ hg _).symm

中文:
引理 Monovary.pow_right₀
  条件: (hg : 0 <= g) (hfg : Monovary f g) (n : 自然数)
  结论: Monovary f (g ^ n)
  证明: (hfg.symm.pow_left₀ hg _).symm

Depends on / 依赖: hfg.symm.pow_left
-/
lemma Monovary.pow_right₀ (hg : 0 <= g) (hfg : Monovary f g) (n : Nat) : Monovary f (g ^ n) :=
  (hfg.symm.pow_left₀ hg _).symm

/--
lemma `Antivary.pow_right₀` / 引理 `Antivary.pow_right₀`

English:
lemma Antivary.pow_right₀
  given: (hg : 0 <= g) (hfg : Antivary f g) (n : Nat)
  statement: Antivary f (g ^ n)
  proof: (hfg.symm.pow_left₀ hg _).symm

中文:
引理 Antivary.pow_right₀
  条件: (hg : 0 <= g) (hfg : Antivary f g) (n : 自然数)
  结论: Antivary f (g ^ n)
  证明: (hfg.symm.pow_left₀ hg _).symm

Depends on / 依赖: hfg.symm.pow_left
-/
lemma Antivary.pow_right₀ (hg : 0 <= g) (hfg : Antivary f g) (n : Nat) : Antivary f (g ^ n) :=
  (hfg.symm.pow_left₀ hg _).symm

end LinearOrderedSemiring

section LinearOrderedSemifield

section
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [LinearOrder β]
  {s : Set ι} {f f₁ f₂ : ι -> α} {g g₁ g₂ : ι -> β}

@[simp]
/--
lemma `monovaryOn_inv_left₀` / 引理 `monovaryOn_inv_left₀`

English:
lemma monovaryOn_inv_left₀
  given: (hf : forall i in s, 0 < f i)
  statement: MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s
  proof: forall₅_congr fun _i hi _j hj _ => inv_le_inv₀ (hf _ hi) (hf _ hj)

@[simp]

中文:
引理 monovaryOn_inv_left₀
  条件: (hf : 对任意 i in s, 0 < f i)
  结论: MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s
  证明: forall₅_congr fun _i hi _j hj _ => inv_le_inv₀ (hf _ hi) (hf _ hj)

@[simp]
-/
lemma monovaryOn_inv_left₀ (hf : forall i in s, 0 < f i) : MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s :=
  forall₅_congr fun _i hi _j hj _ => inv_le_inv₀ (hf _ hi) (hf _ hj)

@[simp]
/--
lemma `antivaryOn_inv_left₀` / 引理 `antivaryOn_inv_left₀`

English:
lemma antivaryOn_inv_left₀
  given: (hf : forall i in s, 0 < f i)
  statement: AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s
  proof: forall₅_congr fun _i hi _j hj _ => inv_le_inv₀ (hf _ hj) (hf _ hi)

中文:
引理 antivaryOn_inv_left₀
  条件: (hf : 对任意 i in s, 0 < f i)
  结论: AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s
  证明: forall₅_congr fun _i hi _j hj _ => inv_le_inv₀ (hf _ hj) (hf _ hi)
-/
lemma antivaryOn_inv_left₀ (hf : forall i in s, 0 < f i) : AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s :=
  forall₅_congr fun _i hi _j hj _ => inv_le_inv₀ (hf _ hj) (hf _ hi)

/--
lemma `monovary_inv_left₀` / 引理 `monovary_inv_left₀`

English:
lemma monovary_inv_left₀
  given: (hf : StrongLT 0 f)
  statement: Monovary f⁻¹ g ↔ Antivary f g
  proof: forall₃_congr fun _i _j _ => inv_le_inv₀ (hf _) (hf _)

中文:
引理 monovary_inv_left₀
  条件: (hf : StrongLT 0 f)
  结论: Monovary f⁻¹ g ↔ Antivary f g
  证明: forall₃_congr fun _i _j _ => inv_le_inv₀ (hf _) (hf _)
-/
@[simp] lemma monovary_inv_left₀ (hf : StrongLT 0 f) : Monovary f⁻¹ g ↔ Antivary f g :=
  forall₃_congr fun _i _j _ => inv_le_inv₀ (hf _) (hf _)

/--
lemma `antivary_inv_left₀` / 引理 `antivary_inv_left₀`

English:
lemma antivary_inv_left₀
  given: (hf : StrongLT 0 f)
  statement: Antivary f⁻¹ g ↔ Monovary f g
  proof: forall₃_congr fun _i _j _ => inv_le_inv₀ (hf _) (hf _)

中文:
引理 antivary_inv_left₀
  条件: (hf : StrongLT 0 f)
  结论: Antivary f⁻¹ g ↔ Monovary f g
  证明: forall₃_congr fun _i _j _ => inv_le_inv₀ (hf _) (hf _)
-/
@[simp] lemma antivary_inv_left₀ (hf : StrongLT 0 f) : Antivary f⁻¹ g ↔ Monovary f g :=
  forall₃_congr fun _i _j _ => inv_le_inv₀ (hf _) (hf _)

/--
lemma `MonovaryOn.div_left₀` / 引理 `MonovaryOn.div_left₀`

English:
lemma MonovaryOn.div_left₀
  statement: (hf₁ : forall i in s, 0 <= f₁ i) (hf₂ : forall i in s, 0 < f₂ i)
  proof: fun _i hi _j hj hij => div_le_div₀ (hf₁ _ hj) (h₁ hi hj hij) (hf₂ _ hj) h₂ hi hj hij

中文:
引理 MonovaryOn.div_left₀
  结论: (hf₁ : 对任意 i in s, 0 <= f₁ i) (hf₂ : 对任意 i in s, 0 < f₂ i)
  证明: fun _i hi _j hj hij => div_le_div₀ (hf₁ _ hj) (h₁ hi hj hij) (hf₂ _ hj) h₂ hi hj hij
-/
lemma MonovaryOn.div_left₀ (hf₁ : forall i in s, 0 <= f₁ i) (hf₂ : forall i in s, 0 < f₂ i)
    (h₁ : MonovaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) : MonovaryOn (f₁ / f₂) g s :=
fun _i hi _j hj hij => div_le_div₀ (hf₁ _ hj) (h₁ hi hj hij) (hf₂ _ hj) h₂ hi hj hij

/--
lemma `AntivaryOn.div_left₀` / 引理 `AntivaryOn.div_left₀`

English:
lemma AntivaryOn.div_left₀
  statement: (hf₁ : forall i in s, 0 <= f₁ i) (hf₂ : forall i in s, 0 < f₂ i)
  proof: fun _i hi _j hj hij => div_le_div₀ (hf₁ _ hi) (h₁ hi hj hij) (hf₂ _ hi) h₂ hi hj hij

中文:
引理 AntivaryOn.div_left₀
  结论: (hf₁ : 对任意 i in s, 0 <= f₁ i) (hf₂ : 对任意 i in s, 0 < f₂ i)
  证明: fun _i hi _j hj hij => div_le_div₀ (hf₁ _ hi) (h₁ hi hj hij) (hf₂ _ hi) h₂ hi hj hij
-/
lemma AntivaryOn.div_left₀ (hf₁ : forall i in s, 0 <= f₁ i) (hf₂ : forall i in s, 0 < f₂ i)
    (h₁ : AntivaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) : AntivaryOn (f₁ / f₂) g s :=
fun _i hi _j hj hij => div_le_div₀ (hf₁ _ hi) (h₁ hi hj hij) (hf₂ _ hi) h₂ hi hj hij

/--
lemma `Monovary.div_left₀` / 引理 `Monovary.div_left₀`

English:
lemma Monovary.div_left₀
  statement: (hf₁ : 0 <= f₁) (hf₂ : StrongLT 0 f₂) (h₁ : Monovary f₁ g)
  proof: fun _i _j hij => div_le_div₀ (hf₁ _) (h₁ hij) (hf₂ _) h₂ hij

中文:
引理 Monovary.div_left₀
  结论: (hf₁ : 0 <= f₁) (hf₂ : StrongLT 0 f₂) (h₁ : Monovary f₁ g)
  证明: fun _i _j hij => div_le_div₀ (hf₁ _) (h₁ hij) (hf₂ _) h₂ hij
-/
lemma Monovary.div_left₀ (hf₁ : 0 <= f₁) (hf₂ : StrongLT 0 f₂) (h₁ : Monovary f₁ g)
    (h₂ : Antivary f₂ g) : Monovary (f₁ / f₂) g :=
fun _i _j hij => div_le_div₀ (hf₁ _) (h₁ hij) (hf₂ _) h₂ hij

/--
lemma `Antivary.div_left₀` / 引理 `Antivary.div_left₀`

English:
lemma Antivary.div_left₀
  statement: (hf₁ : 0 <= f₁) (hf₂ : StrongLT 0 f₂) (h₁ : Antivary f₁ g)
  proof: fun _i _j hij => div_le_div₀ (hf₁ _) (h₁ hij) (hf₂ _) h₂ hij

中文:
引理 Antivary.div_left₀
  结论: (hf₁ : 0 <= f₁) (hf₂ : StrongLT 0 f₂) (h₁ : Antivary f₁ g)
  证明: fun _i _j hij => div_le_div₀ (hf₁ _) (h₁ hij) (hf₂ _) h₂ hij
-/
lemma Antivary.div_left₀ (hf₁ : 0 <= f₁) (hf₂ : StrongLT 0 f₂) (h₁ : Antivary f₁ g)
    (h₂ : Monovary f₂ g) : Antivary (f₁ / f₂) g :=
fun _i _j hij => div_le_div₀ (hf₁ _) (h₁ hij) (hf₂ _) h₂ hij

end

section
variable [LinearOrder α] [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι -> α} {g g₁ g₂ : ι -> β}

@[simp]
/--
lemma `monovaryOn_inv_right₀` / 引理 `monovaryOn_inv_right₀`

English:
lemma monovaryOn_inv_right₀
  given: (hg : forall i in s, 0 < g i)
  statement: MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s
  proof: forall₂_comm.trans forall₄_congr fun i hi j hj => by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]

@[simp]

中文:
引理 monovaryOn_inv_right₀
  条件: (hg : 对任意 i in s, 0 < g i)
  结论: MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s
  证明: forall₂_comm.trans forall₄_congr fun i hi j hj => by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]

@[simp]

Depends on / 依赖: _comm.trans
-/
lemma monovaryOn_inv_right₀ (hg : forall i in s, 0 < g i) : MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s :=
forall₂_comm.trans forall₄_congr fun i hi j hj => by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]

@[simp]
/--
lemma `antivaryOn_inv_right₀` / 引理 `antivaryOn_inv_right₀`

English:
lemma antivaryOn_inv_right₀
  given: (hg : forall i in s, 0 < g i)
  statement: AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s
  proof: forall₂_comm.trans forall₄_congr fun i hi j hj => by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]

中文:
引理 antivaryOn_inv_right₀
  条件: (hg : 对任意 i in s, 0 < g i)
  结论: AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s
  证明: forall₂_comm.trans forall₄_congr fun i hi j hj => by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]

Depends on / 依赖: _comm.trans
-/
lemma antivaryOn_inv_right₀ (hg : forall i in s, 0 < g i) : AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s :=
forall₂_comm.trans forall₄_congr fun i hi j hj => by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]

/--
lemma `monovary_inv_right₀` / 引理 `monovary_inv_right₀`

English:
lemma monovary_inv_right₀
  given: (hg : StrongLT 0 g)
  statement: Monovary f g⁻¹ ↔ Antivary f g
  proof: forall_comm.trans forall₂_congr fun i j => by simp [inv_lt_inv₀ (hg _) (hg _)]

中文:
引理 monovary_inv_right₀
  条件: (hg : StrongLT 0 g)
  结论: Monovary f g⁻¹ ↔ Antivary f g
  证明: forall_comm.trans forall₂_congr fun i j => by simp [inv_lt_inv₀ (hg _) (hg _)]
-/
@[simp] lemma monovary_inv_right₀ (hg : StrongLT 0 g) : Monovary f g⁻¹ ↔ Antivary f g :=
forall_comm.trans forall₂_congr fun i j => by simp [inv_lt_inv₀ (hg _) (hg _)]

/--
lemma `antivary_inv_right₀` / 引理 `antivary_inv_right₀`

English:
lemma antivary_inv_right₀
  given: (hg : StrongLT 0 g)
  statement: Antivary f g⁻¹ ↔ Monovary f g
  proof: forall_comm.trans forall₂_congr fun i j => by simp [inv_lt_inv₀ (hg _) (hg _)]

中文:
引理 antivary_inv_right₀
  条件: (hg : StrongLT 0 g)
  结论: Antivary f g⁻¹ ↔ Monovary f g
  证明: forall_comm.trans forall₂_congr fun i j => by simp [inv_lt_inv₀ (hg _) (hg _)]
-/
@[simp] lemma antivary_inv_right₀ (hg : StrongLT 0 g) : Antivary f g⁻¹ ↔ Monovary f g :=
forall_comm.trans forall₂_congr fun i j => by simp [inv_lt_inv₀ (hg _) (hg _)]

/--
lemma `MonovaryOn.div_right₀` / 引理 `MonovaryOn.div_right₀`

English:
lemma MonovaryOn.div_right₀
  statement: (hg₁ : forall i in s, 0 <= g₁ i) (hg₂ : forall i in s, 0 < g₂ i)
  proof: (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

中文:
引理 MonovaryOn.div_right₀
  结论: (hg₁ : 对任意 i in s, 0 <= g₁ i) (hg₂ : 对任意 i in s, 0 < g₂ i)
  证明: (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

Depends on / 依赖: symm.div_left
-/
lemma MonovaryOn.div_right₀ (hg₁ : forall i in s, 0 <= g₁ i) (hg₂ : forall i in s, 0 < g₂ i)
    (h₁ : MonovaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) : MonovaryOn f (g₁ / g₂) s :=
  (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

/--
lemma `AntivaryOn.div_right₀` / 引理 `AntivaryOn.div_right₀`

English:
lemma AntivaryOn.div_right₀
  statement: (hg₁ : forall i in s, 0 <= g₁ i) (hg₂ : forall i in s, 0 < g₂ i)
  proof: (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

中文:
引理 AntivaryOn.div_right₀
  结论: (hg₁ : 对任意 i in s, 0 <= g₁ i) (hg₂ : 对任意 i in s, 0 < g₂ i)
  证明: (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

Depends on / 依赖: symm.div_left
-/
lemma AntivaryOn.div_right₀ (hg₁ : forall i in s, 0 <= g₁ i) (hg₂ : forall i in s, 0 < g₂ i)
    (h₁ : AntivaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) : AntivaryOn f (g₁ / g₂) s :=
  (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

/--
lemma `Monovary.div_right₀` / 引理 `Monovary.div_right₀`

English:
lemma Monovary.div_right₀
  statement: (hg₁ : 0 <= g₁) (hg₂ : StrongLT 0 g₂) (h₁ : Monovary f g₁)
  proof: (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

中文:
引理 Monovary.div_right₀
  结论: (hg₁ : 0 <= g₁) (hg₂ : StrongLT 0 g₂) (h₁ : Monovary f g₁)
  证明: (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

Depends on / 依赖: symm.div_left
-/
lemma Monovary.div_right₀ (hg₁ : 0 <= g₁) (hg₂ : StrongLT 0 g₂) (h₁ : Monovary f g₁)
    (h₂ : Antivary f g₂) : Monovary f (g₁ / g₂) := (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

/--
lemma `Antivary.div_right₀` / 引理 `Antivary.div_right₀`

English:
lemma Antivary.div_right₀
  statement: (hg₁ : 0 <= g₁) (hg₂ : StrongLT 0 g₂) (h₁ : Antivary f g₁)
  proof: (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

中文:
引理 Antivary.div_right₀
  结论: (hg₁ : 0 <= g₁) (hg₂ : StrongLT 0 g₂) (h₁ : Antivary f g₁)
  证明: (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

Depends on / 依赖: symm.div_left
-/
lemma Antivary.div_right₀ (hg₁ : 0 <= g₁) (hg₂ : StrongLT 0 g₂) (h₁ : Antivary f g₁)
    (h₂ : Monovary f g₂) : Antivary f (g₁ / g₂) := (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

end

section
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι -> α} {g g₁ g₂ : ι -> β}

/--
lemma `monovaryOn_inv₀` / 引理 `monovaryOn_inv₀`

English:
lemma monovaryOn_inv₀
  given: (hf : forall i in s, 0 < f i) (hg : forall i in s, 0 < g i)
  proof: by
  rw [monovaryOn_inv_left₀ hf]; rw [antivaryOn_inv_right₀ hg]

中文:
引理 monovaryOn_inv₀
  条件: (hf : 对任意 i in s, 0 < f i) (hg : 对任意 i in s, 0 < g i)
  证明: by
  rw [monovaryOn_inv_left₀ hf]; rw [antivaryOn_inv_right₀ hg]
-/
lemma monovaryOn_inv₀ (hf : forall i in s, 0 < f i) (hg : forall i in s, 0 < g i) :
    MonovaryOn f⁻¹ g⁻¹ s ↔ MonovaryOn f g s := by
  rw [monovaryOn_inv_left₀ hf]; rw [antivaryOn_inv_right₀ hg]
/--
lemma `antivaryOn_inv₀` / 引理 `antivaryOn_inv₀`

English:
lemma antivaryOn_inv₀
  given: (hf : forall i in s, 0 < f i) (hg : forall i in s, 0 < g i)
  proof: by
  rw [antivaryOn_inv_left₀ hf]; rw [monovaryOn_inv_right₀ hg]

中文:
引理 antivaryOn_inv₀
  条件: (hf : 对任意 i in s, 0 < f i) (hg : 对任意 i in s, 0 < g i)
  证明: by
  rw [antivaryOn_inv_left₀ hf]; rw [monovaryOn_inv_right₀ hg]
-/
lemma antivaryOn_inv₀ (hf : forall i in s, 0 < f i) (hg : forall i in s, 0 < g i) :
    AntivaryOn f⁻¹ g⁻¹ s ↔ AntivaryOn f g s := by
  rw [antivaryOn_inv_left₀ hf]; rw [monovaryOn_inv_right₀ hg]

/--
lemma `monovary_inv₀` / 引理 `monovary_inv₀`

English:
lemma monovary_inv₀
  given: (hf : StrongLT 0 f) (hg : StrongLT 0 g)
  statement: Monovary f⁻¹ g⁻¹ ↔ Monovary f g
  proof: by
  rw [monovary_inv_left₀ hf]; rw [antivary_inv_right₀ hg]

中文:
引理 monovary_inv₀
  条件: (hf : StrongLT 0 f) (hg : StrongLT 0 g)
  结论: Monovary f⁻¹ g⁻¹ ↔ Monovary f g
  证明: by
  rw [monovary_inv_left₀ hf]; rw [antivary_inv_right₀ hg]
-/
lemma monovary_inv₀ (hf : StrongLT 0 f) (hg : StrongLT 0 g) : Monovary f⁻¹ g⁻¹ ↔ Monovary f g := by
  rw [monovary_inv_left₀ hf]; rw [antivary_inv_right₀ hg]
/--
lemma `antivary_inv₀` / 引理 `antivary_inv₀`

English:
lemma antivary_inv₀
  given: (hf : StrongLT 0 f) (hg : StrongLT 0 g)
  statement: Antivary f⁻¹ g⁻¹ ↔ Antivary f g
  proof: by
  rw [antivary_inv_left₀ hf]; rw [monovary_inv_right₀ hg]

中文:
引理 antivary_inv₀
  条件: (hf : StrongLT 0 f) (hg : StrongLT 0 g)
  结论: Antivary f⁻¹ g⁻¹ ↔ Antivary f g
  证明: by
  rw [antivary_inv_left₀ hf]; rw [monovary_inv_right₀ hg]
-/
lemma antivary_inv₀ (hf : StrongLT 0 f) (hg : StrongLT 0 g) : Antivary f⁻¹ g⁻¹ ↔ Antivary f g := by
  rw [antivary_inv_left₀ hf]; rw [monovary_inv_right₀ hg]

end

alias ⟨MonovaryOn.of_inv_left₀, AntivaryOn.inv_left₀⟩ := monovaryOn_inv_left₀
alias ⟨AntivaryOn.of_inv_left₀, MonovaryOn.inv_left₀⟩ := antivaryOn_inv_left₀
alias ⟨MonovaryOn.of_inv_right₀, AntivaryOn.inv_right₀⟩ := monovaryOn_inv_right₀
alias ⟨AntivaryOn.of_inv_right₀, MonovaryOn.inv_right₀⟩ := antivaryOn_inv_right₀
alias ⟨MonovaryOn.of_inv₀, MonovaryOn.inv₀⟩ := monovaryOn_inv₀
alias ⟨AntivaryOn.of_inv₀, AntivaryOn.inv₀⟩ := antivaryOn_inv₀
alias ⟨Monovary.of_inv_left₀, Antivary.inv_left₀⟩ := monovary_inv_left₀
alias ⟨Antivary.of_inv_left₀, Monovary.inv_left₀⟩ := antivary_inv_left₀
alias ⟨Monovary.of_inv_right₀, Antivary.inv_right₀⟩ := monovary_inv_right₀
alias ⟨Antivary.of_inv_right₀, Monovary.inv_right₀⟩ := antivary_inv_right₀
alias ⟨Monovary.of_inv₀, Monovary.inv₀⟩ := monovary_inv₀
alias ⟨Antivary.of_inv₀, Antivary.inv₀⟩ := antivary_inv₀

end LinearOrderedSemifield

/-! ### Rearrangement inequality characterisation -/

section LinearOrderedAddCommGroup
variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β]
  [IsStrictOrderedModule α β] {f : ι -> α} {g : ι -> β} {s : Set ι}

/--
lemma `monovaryOn_iff_forall_smul_nonneg` / 引理 `monovaryOn_iff_forall_smul_nonneg`

English:
lemma monovaryOn_iff_forall_smul_nonneg
  proof: by
  simp_rw [smul_nonneg_iff_pos_imp_nonneg, sub_pos, sub_nonneg, forall_and]
  exact (and_iff_right_of_imp MonovaryOn.symm).symm

中文:
引理 monovaryOn_iff_对任意_smul_nonneg
  证明: by
  simp_rw [smul_nonneg_iff_pos_imp_nonneg, sub_pos, sub_nonneg, forall_and]
  exact (and_iff_right_of_imp MonovaryOn.symm).symm

Depends on / 依赖: MonovaryOn, MonovaryOn.symm, and_iff_right_of_imp, forall_and, simp_rw, smul_nonneg_iff_pos_imp_nonneg, sub_nonneg, sub_pos
-/
lemma monovaryOn_iff_forall_smul_nonneg :
    MonovaryOn f g s ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> 0 <= (f j - f i) • (g j - g i) := by
  simp_rw [smul_nonneg_iff_pos_imp_nonneg, sub_pos, sub_nonneg, forall_and]
  exact (and_iff_right_of_imp MonovaryOn.symm).symm

/--
lemma `antivaryOn_iff_forall_smul_nonpos` / 引理 `antivaryOn_iff_forall_smul_nonpos`

English:
lemma antivaryOn_iff_forall_smul_nonpos
  proof: monovaryOn_toDual_right.symm.trans by rw [monovaryOn_iff_forall_smul_nonneg]; rfl

中文:
引理 antivaryOn_iff_对任意_smul_nonpos
  证明: monovaryOn_toDual_right.symm.trans by rw [monovaryOn_iff_forall_smul_nonneg]; rfl

Depends on / 依赖: monovaryOn_iff_forall_smul_nonneg, monovaryOn_toDual_right, monovaryOn_toDual_right.symm.trans
-/
lemma antivaryOn_iff_forall_smul_nonpos :
    AntivaryOn f g s ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> (f j - f i) • (g j - g i) <= 0 :=
monovaryOn_toDual_right.symm.trans by rw [monovaryOn_iff_forall_smul_nonneg]; rfl

/--
lemma `monovary_iff_forall_smul_nonneg` / 引理 `monovary_iff_forall_smul_nonneg`

English:
lemma monovary_iff_forall_smul_nonneg
  statement: Monovary f g ↔ forall i j, 0 <= (f j - f i) • (g j - g i)
  proof: monovaryOn_univ.symm.trans monovaryOn_iff_forall_smul_nonneg.trans by
    simp only [Set.mem_univ, forall_true_left]

中文:
引理 monovary_iff_对任意_smul_nonneg
  结论: Monovary f g ↔ 对任意 i j, 0 <= (f j - f i) • (g j - g i)
  证明: monovaryOn_univ.symm.trans monovaryOn_iff_forall_smul_nonneg.trans by
    simp only [Set.mem_univ, forall_true_left]

Depends on / 依赖: Set.mem_univ, forall_true_left, mem_univ, monovaryOn_iff_forall_smul_nonneg, monovaryOn_iff_forall_smul_nonneg.trans, monovaryOn_univ, monovaryOn_univ.symm.trans
-/
lemma monovary_iff_forall_smul_nonneg : Monovary f g ↔ forall i j, 0 <= (f j - f i) • (g j - g i) :=
monovaryOn_univ.symm.trans monovaryOn_iff_forall_smul_nonneg.trans by
    simp only [Set.mem_univ, forall_true_left]

/--
lemma `antivary_iff_forall_smul_nonpos` / 引理 `antivary_iff_forall_smul_nonpos`

English:
lemma antivary_iff_forall_smul_nonpos
  statement: Antivary f g ↔ forall i j, (f j - f i) • (g j - g i) <= 0
  proof: monovary_toDual_right.symm.trans by rw [monovary_iff_forall_smul_nonneg]; rfl

中文:
引理 antivary_iff_对任意_smul_nonpos
  结论: Antivary f g ↔ 对任意 i j, (f j - f i) • (g j - g i) <= 0
  证明: monovary_toDual_right.symm.trans by rw [monovary_iff_forall_smul_nonneg]; rfl

Depends on / 依赖: monovary_iff_forall_smul_nonneg, monovary_toDual_right, monovary_toDual_right.symm.trans
-/
lemma antivary_iff_forall_smul_nonpos : Antivary f g ↔ forall i j, (f j - f i) • (g j - g i) <= 0 :=
monovary_toDual_right.symm.trans by rw [monovary_iff_forall_smul_nonneg]; rfl

/--
lemma `monovaryOn_iff_smul_rearrangement` / 引理 `monovaryOn_iff_smul_rearrangement`

English:
lemma monovaryOn_iff_smul_rearrangement
  proof: monovaryOn_iff_forall_smul_nonneg.trans forall₄_congr fun i _ j _ => by
    simp [smul_sub, sub_smul, ← add_sub_right_comm, le_sub_iff_add_le, add_comm (f i • g i),
      add_comm (f i • g j)]

中文:
引理 monovaryOn_iff_smul_rearrangement
  证明: monovaryOn_iff_forall_smul_nonneg.trans forall₄_congr fun i _ j _ => by
    simp [smul_sub, sub_smul, ← add_sub_right_comm, le_sub_iff_add_le, add_comm (f i • g i),
      add_comm (f i • g j)]

Depends on / 依赖: add_comm, add_sub_right_comm, le_sub_iff_add_le, monovaryOn_iff_forall_smul_nonneg, monovaryOn_iff_forall_smul_nonneg.trans, smul_sub, sub_smul
-/
lemma monovaryOn_iff_smul_rearrangement :
    MonovaryOn f g s ↔
      forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> f i • g j + f j • g i <= f i • g i + f j • g j :=
monovaryOn_iff_forall_smul_nonneg.trans forall₄_congr fun i _ j _ => by
    simp [smul_sub, sub_smul, ← add_sub_right_comm, le_sub_iff_add_le, add_comm (f i • g i),
      add_comm (f i • g j)]

/--
lemma `antivaryOn_iff_smul_rearrangement` / 引理 `antivaryOn_iff_smul_rearrangement`

English:
lemma antivaryOn_iff_smul_rearrangement
  proof: monovaryOn_toDual_right.symm.trans by rw [monovaryOn_iff_smul_rearrangement]; rfl

中文:
引理 antivaryOn_iff_smul_rearrangement
  证明: monovaryOn_toDual_right.symm.trans by rw [monovaryOn_iff_smul_rearrangement]; rfl

Depends on / 依赖: monovaryOn_iff_smul_rearrangement, monovaryOn_toDual_right, monovaryOn_toDual_right.symm.trans
-/
lemma antivaryOn_iff_smul_rearrangement :
    AntivaryOn f g s ↔
      forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> f i • g i + f j • g j <= f i • g j + f j • g i :=
monovaryOn_toDual_right.symm.trans by rw [monovaryOn_iff_smul_rearrangement]; rfl

/--
lemma `monovary_iff_smul_rearrangement` / 引理 `monovary_iff_smul_rearrangement`

English:
lemma monovary_iff_smul_rearrangement
  proof: monovaryOn_univ.symm.trans monovaryOn_iff_smul_rearrangement.trans by
    simp only [Set.mem_univ, forall_true_left]

中文:
引理 monovary_iff_smul_rearrangement
  证明: monovaryOn_univ.symm.trans monovaryOn_iff_smul_rearrangement.trans by
    simp only [Set.mem_univ, forall_true_left]

Depends on / 依赖: Set.mem_univ, forall_true_left, mem_univ, monovaryOn_iff_smul_rearrangement, monovaryOn_iff_smul_rearrangement.trans, monovaryOn_univ, monovaryOn_univ.symm.trans
-/
lemma monovary_iff_smul_rearrangement :
    Monovary f g ↔ forall i j, f i • g j + f j • g i <= f i • g i + f j • g j :=
monovaryOn_univ.symm.trans monovaryOn_iff_smul_rearrangement.trans by
    simp only [Set.mem_univ, forall_true_left]

/--
lemma `antivary_iff_smul_rearrangement` / 引理 `antivary_iff_smul_rearrangement`

English:
lemma antivary_iff_smul_rearrangement
  proof: monovary_toDual_right.symm.trans by rw [monovary_iff_smul_rearrangement]; rfl

alias ⟨MonovaryOn.sub_smul_sub_nonneg, _⟩ := monovaryOn_iff_forall_smul_nonneg
alias ⟨AntivaryOn.sub_smul_sub_nonpos, _⟩ := antivaryOn_iff_forall_smul_nonpos
alias ⟨Monovary.sub_smul_sub_nonneg, _⟩ := monovary_iff_forall_

中文:
引理 antivary_iff_smul_rearrangement
  证明: monovary_toDual_right.symm.trans by rw [monovary_iff_smul_rearrangement]; rfl

alias ⟨MonovaryOn.sub_smul_sub_nonneg, _⟩ := monovaryOn_iff_forall_smul_nonneg
alias ⟨AntivaryOn.sub_smul_sub_nonpos, _⟩ := antivaryOn_iff_forall_smul_nonpos
alias ⟨Monovary.sub_smul_sub_nonneg, _⟩ := monovary_iff_forall_

Depends on / 依赖: monovary_iff_smul_rearrangement, monovary_toDual_right, monovary_toDual_right.symm.trans
-/
lemma antivary_iff_smul_rearrangement :
    Antivary f g ↔ forall i j, f i • g i + f j • g j <= f i • g j + f j • g i :=
monovary_toDual_right.symm.trans by rw [monovary_iff_smul_rearrangement]; rfl

alias ⟨MonovaryOn.sub_smul_sub_nonneg, _⟩ := monovaryOn_iff_forall_smul_nonneg
alias ⟨AntivaryOn.sub_smul_sub_nonpos, _⟩ := antivaryOn_iff_forall_smul_nonpos
alias ⟨Monovary.sub_smul_sub_nonneg, _⟩ := monovary_iff_forall_smul_nonneg
alias ⟨Antivary.sub_smul_sub_nonpos, _⟩ := antivary_iff_forall_smul_nonpos
alias ⟨Monovary.smul_add_smul_le_smul_add_smul, _⟩ := monovary_iff_smul_rearrangement
alias ⟨Antivary.smul_add_smul_le_smul_add_smul, _⟩ := antivary_iff_smul_rearrangement
alias ⟨MonovaryOn.smul_add_smul_le_smul_add_smul, _⟩ := monovaryOn_iff_smul_rearrangement
alias ⟨AntivaryOn.smul_add_smul_le_smul_add_smul, _⟩ := antivaryOn_iff_smul_rearrangement

end LinearOrderedAddCommGroup

section LinearOrderedRing
variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {f g : ι -> α} {s : Set ι}

/--
lemma `monovaryOn_iff_forall_mul_nonneg` / 引理 `monovaryOn_iff_forall_mul_nonneg`

English:
lemma monovaryOn_iff_forall_mul_nonneg
  proof: by
  simp only [smul_eq_mul, monovaryOn_iff_forall_smul_nonneg]

中文:
引理 monovaryOn_iff_对任意_mul_nonneg
  证明: by
  simp only [smul_eq_mul, monovaryOn_iff_forall_smul_nonneg]

Depends on / 依赖: monovaryOn_iff_forall_smul_nonneg, smul_eq_mul
-/
lemma monovaryOn_iff_forall_mul_nonneg :
    MonovaryOn f g s ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> 0 <= (f j - f i) * (g j - g i) := by
  simp only [smul_eq_mul, monovaryOn_iff_forall_smul_nonneg]

/--
lemma `antivaryOn_iff_forall_mul_nonpos` / 引理 `antivaryOn_iff_forall_mul_nonpos`

English:
lemma antivaryOn_iff_forall_mul_nonpos
  proof: by
  simp only [smul_eq_mul, antivaryOn_iff_forall_smul_nonpos]

中文:
引理 antivaryOn_iff_对任意_mul_nonpos
  证明: by
  simp only [smul_eq_mul, antivaryOn_iff_forall_smul_nonpos]

Depends on / 依赖: antivaryOn_iff_forall_smul_nonpos, smul_eq_mul
-/
lemma antivaryOn_iff_forall_mul_nonpos :
    AntivaryOn f g s ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> (f j - f i) * (g j - g i) <= 0 := by
  simp only [smul_eq_mul, antivaryOn_iff_forall_smul_nonpos]

/--
lemma `monovary_iff_forall_mul_nonneg` / 引理 `monovary_iff_forall_mul_nonneg`

English:
lemma monovary_iff_forall_mul_nonneg
  statement: Monovary f g ↔ forall i j, 0 <= (f j - f i) * (g j - g i)
  proof: by
  simp only [smul_eq_mul, monovary_iff_forall_smul_nonneg]

中文:
引理 monovary_iff_对任意_mul_nonneg
  结论: Monovary f g ↔ 对任意 i j, 0 <= (f j - f i) * (g j - g i)
  证明: by
  simp only [smul_eq_mul, monovary_iff_forall_smul_nonneg]

Depends on / 依赖: monovary_iff_forall_smul_nonneg, smul_eq_mul
-/
lemma monovary_iff_forall_mul_nonneg : Monovary f g ↔ forall i j, 0 <= (f j - f i) * (g j - g i) := by
  simp only [smul_eq_mul, monovary_iff_forall_smul_nonneg]

/--
lemma `antivary_iff_forall_mul_nonpos` / 引理 `antivary_iff_forall_mul_nonpos`

English:
lemma antivary_iff_forall_mul_nonpos
  statement: Antivary f g ↔ forall i j, (f j - f i) * (g j - g i) <= 0
  proof: by
  simp only [smul_eq_mul, antivary_iff_forall_smul_nonpos]

中文:
引理 antivary_iff_对任意_mul_nonpos
  结论: Antivary f g ↔ 对任意 i j, (f j - f i) * (g j - g i) <= 0
  证明: by
  simp only [smul_eq_mul, antivary_iff_forall_smul_nonpos]

Depends on / 依赖: antivary_iff_forall_smul_nonpos, smul_eq_mul
-/
lemma antivary_iff_forall_mul_nonpos : Antivary f g ↔ forall i j, (f j - f i) * (g j - g i) <= 0 := by
  simp only [smul_eq_mul, antivary_iff_forall_smul_nonpos]

/--
lemma `monovaryOn_iff_mul_rearrangement` / 引理 `monovaryOn_iff_mul_rearrangement`

English:
lemma monovaryOn_iff_mul_rearrangement
  proof: by
  simp only [smul_eq_mul, monovaryOn_iff_smul_rearrangement]

中文:
引理 monovaryOn_iff_mul_rearrangement
  证明: by
  simp only [smul_eq_mul, monovaryOn_iff_smul_rearrangement]

Depends on / 依赖: monovaryOn_iff_smul_rearrangement, smul_eq_mul
-/
lemma monovaryOn_iff_mul_rearrangement :
    MonovaryOn f g s ↔
      forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> f i * g j + f j * g i <= f i * g i + f j * g j := by
  simp only [smul_eq_mul, monovaryOn_iff_smul_rearrangement]

/--
lemma `antivaryOn_iff_mul_rearrangement` / 引理 `antivaryOn_iff_mul_rearrangement`

English:
lemma antivaryOn_iff_mul_rearrangement
  proof: by
  simp only [smul_eq_mul, antivaryOn_iff_smul_rearrangement]

中文:
引理 antivaryOn_iff_mul_rearrangement
  证明: by
  simp only [smul_eq_mul, antivaryOn_iff_smul_rearrangement]

Depends on / 依赖: Classical, Classical.decEq, Monic.def, Ne.symm, Subsingleton, Subsingleton.elim, antivaryOn_iff_smul_rearrangement, leadingCoeff, leadingCoeff_mul, one_mul, p.leadingCoeff, q.leadingCoeff, smul_eq_mul, subsingleton_of_zero_eq_one
-/
lemma antivaryOn_iff_mul_rearrangement :
    AntivaryOn f g s ↔
      forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> f i * g i + f j * g j <= f i * g j + f j * g i := by
  simp only [smul_eq_mul, antivaryOn_iff_smul_rearrangement]

/--
lemma `monovary_iff_mul_rearrangement` / 引理 `monovary_iff_mul_rearrangement`

English:
lemma monovary_iff_mul_rearrangement
  proof: by
  simp only [smul_eq_mul, monovary_iff_smul_rearrangement]

中文:
引理 monovary_iff_mul_rearrangement
  证明: by
  simp only [smul_eq_mul, monovary_iff_smul_rearrangement]

Depends on / 依赖: monovary_iff_smul_rearrangement, smul_eq_mul
-/
lemma monovary_iff_mul_rearrangement :
    Monovary f g ↔ forall i j, f i * g j + f j * g i <= f i * g i + f j * g j := by
  simp only [smul_eq_mul, monovary_iff_smul_rearrangement]

/--
lemma `antivary_iff_mul_rearrangement` / 引理 `antivary_iff_mul_rearrangement`

English:
lemma antivary_iff_mul_rearrangement
  proof: by
  simp only [smul_eq_mul, antivary_iff_smul_rearrangement]

alias ⟨MonovaryOn.sub_mul_sub_nonneg, _⟩ := monovaryOn_iff_forall_mul_nonneg
alias ⟨AntivaryOn.sub_mul_sub_nonpos, _⟩ := antivaryOn_iff_forall_mul_nonpos
alias ⟨Monovary.sub_mul_sub_nonneg, _⟩ := monovary_iff_forall_mul_nonneg
alias ⟨Ant

中文:
引理 antivary_iff_mul_rearrangement
  证明: by
  simp only [smul_eq_mul, antivary_iff_smul_rearrangement]

alias ⟨MonovaryOn.sub_mul_sub_nonneg, _⟩ := monovaryOn_iff_forall_mul_nonneg
alias ⟨AntivaryOn.sub_mul_sub_nonpos, _⟩ := antivaryOn_iff_forall_mul_nonpos
alias ⟨Monovary.sub_mul_sub_nonneg, _⟩ := monovary_iff_forall_mul_nonneg
alias ⟨Ant

Depends on / 依赖: antivary_iff_smul_rearrangement, smul_eq_mul
-/
lemma antivary_iff_mul_rearrangement :
    Antivary f g ↔ forall i j, f i * g i + f j * g j <= f i * g j + f j * g i := by
  simp only [smul_eq_mul, antivary_iff_smul_rearrangement]

alias ⟨MonovaryOn.sub_mul_sub_nonneg, _⟩ := monovaryOn_iff_forall_mul_nonneg
alias ⟨AntivaryOn.sub_mul_sub_nonpos, _⟩ := antivaryOn_iff_forall_mul_nonpos
alias ⟨Monovary.sub_mul_sub_nonneg, _⟩ := monovary_iff_forall_mul_nonneg
alias ⟨Antivary.sub_mul_sub_nonpos, _⟩ := antivary_iff_forall_mul_nonpos
alias ⟨Monovary.mul_add_mul_le_mul_add_mul, _⟩ := monovary_iff_mul_rearrangement
alias ⟨Antivary.mul_add_mul_le_mul_add_mul, _⟩ := antivary_iff_mul_rearrangement
alias ⟨MonovaryOn.mul_add_mul_le_mul_add_mul, _⟩ := monovaryOn_iff_mul_rearrangement
alias ⟨AntivaryOn.mul_add_mul_le_mul_add_mul, _⟩ := antivaryOn_iff_mul_rearrangement

end LinearOrderedRing
