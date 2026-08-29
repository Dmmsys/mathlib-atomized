/-
Copyright (c) 2025 Yaël Dillies, Strahinja Gvozdić, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Strahinja Gvozdić, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# Convolution

This file defines convolution of finite subsets `A` and `B` of group `G` as the map `A ⋆ B : G → ℕ`
that maps `x ∈ G` to the number of distinct representations of `x` in the form `x = ab` for
`a ∈ A`, `b ∈ B`. It is shown how convolution behaves under the change of order of `A` and `B`, as
well as under the left and right actions on `A`, `B`, and the function argument.
-/

@[expose] public section

open MulOpposite MulAction
open scoped Pointwise RightActions

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {A B : Finset G} {s x y : G}

/-- Given finite subsets `A` and `B` of a group `G`, convolution of `A` and `B` is a map `G → ℕ`
that maps `x ∈ G` to the number of distinct representations of `x` in the form `x = ab`, where
`a ∈ A`, `b ∈ B`. -/
@[to_additive addConvolution /-- Given finite subsets `A` and `B` of an additive group `G`,
convolution of `A` and `B` is a map `G → ℕ` that maps `x ∈ G` to the number of distinct
representations of `x` in the form `x = a + b`, where `a ∈ A`, `b ∈ B`. -/]
/--
Definition of `convolution` / `convolution` 的定义

English:
definition convolution
  signature: (A B : Finset G)
  body: fun x => #{ab in A ×ˢ B | ab.1 * ab.2 = x}

@[to_additive]

中文:
定义 convolution
  签名: (A B : 有限集 G)
  定义体: fun x => #{ab in A ×ˢ B | ab.1 * ab.2 = x}

@[to_additive]
-/
def convolution (A B : Finset G) : G -> Nat := fun x => #{ab in A ×ˢ B | ab.1 * ab.2 = x}

@[to_additive]
/--
lemma `card_smul_inter_smul` / 引理 `card_smul_inter_smul`

English:
lemma card_smul_inter_smul
  given: (A B : Finset G) (x y : G)
  proof: card_nbij' (fun z => (x⁻¹ * z, z⁻¹ * y)) (fun ab' => x • ab'.1)
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem, mul_assoc])
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem]
        simp +contextual [← eq_mul_inv_iff_mul_eq, mul_assoc])
    (by simp [S

中文:
引理 card_smul_inter_smul
  条件: (A B : 有限集 G) (x y : G)
  证明: card_nbij' (fun z => (x⁻¹ * z, z⁻¹ * y)) (fun ab' => x • ab'.1)
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem, mul_assoc])
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem]
        simp +contextual [← eq_mul_inv_iff_mul_eq, mul_assoc])
    (by simp [S

Depends on / 依赖: LeftInvOn, MapsTo, Set.LeftInvOn, Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem, card_nbij, contextual, eq_mul_inv_iff_mul_eq, mem_smul_set_iff_inv_smul_mem, mul_assoc
-/
lemma card_smul_inter_smul (A B : Finset G) (x y : G) :
    #((x • A) inter (y • B)) = A.convolution B⁻¹ (x⁻¹ * y) :=
  card_nbij' (fun z => (x⁻¹ * z, z⁻¹ * y)) (fun ab' => x • ab'.1)
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem, mul_assoc])
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem]
        simp +contextual [← eq_mul_inv_iff_mul_eq, mul_assoc])
    (by simp [Set.LeftInvOn])
    (by simp +contextual [Set.LeftInvOn, ← eq_mul_inv_iff_mul_eq, mul_assoc])

@[to_additive]
/--
lemma `card_inter_smul` / 引理 `card_inter_smul`

English:
lemma card_inter_smul
  given: (A B : Finset G) (x : G)
  statement: #(A inter (x • B)) = A.convolution B⁻¹ x
  proof: by
  simpa using card_smul_inter_smul _ _ 1 x

@[to_additive]

中文:
引理 card_inter_smul
  条件: (A B : 有限集 G) (x : G)
  结论: #(A inter (x • B)) = A.convolution B⁻¹ x
  证明: by
  simpa using card_smul_inter_smul _ _ 1 x

@[to_additive]

Depends on / 依赖: card_smul_inter_smul
-/
lemma card_inter_smul (A B : Finset G) (x : G) : #(A inter (x • B)) = A.convolution B⁻¹ x := by
  simpa using card_smul_inter_smul _ _ 1 x

@[to_additive]
/--
lemma `card_smul_inter` / 引理 `card_smul_inter`

English:
lemma card_smul_inter
  given: (A B : Finset G) (x : G)
  statement: #((x • A) inter B) = A.convolution B⁻¹ x⁻¹
  proof: by
  simpa using card_smul_inter_smul _ _ x 1

@[to_additive]

中文:
引理 card_smul_inter
  条件: (A B : 有限集 G) (x : G)
  结论: #((x • A) inter B) = A.convolution B⁻¹ x⁻¹
  证明: by
  simpa using card_smul_inter_smul _ _ x 1

@[to_additive]

Depends on / 依赖: card_smul_inter_smul
-/
lemma card_smul_inter (A B : Finset G) (x : G) : #((x • A) inter B) = A.convolution B⁻¹ x⁻¹ := by
  simpa using card_smul_inter_smul _ _ x 1

@[to_additive]
/--
lemma `card_inter_smul_inv` / 引理 `card_inter_smul_inv`

English:
lemma card_inter_smul_inv
  given: (A B : Finset G) (x : G)
  statement: #(A inter (x • B⁻¹)) = A.convolution B x
  proof: by
  simp [card_inter_smul]

@[to_additive]

中文:
引理 card_inter_smul_inv
  条件: (A B : 有限集 G) (x : G)
  结论: #(A inter (x • B⁻¹)) = A.convolution B x
  证明: by
  simp [card_inter_smul]

@[to_additive]

Depends on / 依赖: card_inter_smul
-/
lemma card_inter_smul_inv (A B : Finset G) (x : G) : #(A inter (x • B⁻¹)) = A.convolution B x := by
  simp [card_inter_smul]

@[to_additive]
/--
lemma `card_mul_eq` / 引理 `card_mul_eq`

English:
lemma card_mul_eq
  given: (A B : Finset G) (x : G)
  proof: rfl

@[to_additive]

中文:
引理 card_mul_eq
  条件: (A B : 有限集 G) (x : G)
  证明: rfl

@[to_additive]
-/
lemma card_mul_eq (A B : Finset G) (x : G) :
    #{ab in A ×ˢ B | ab.1 * ab.2 = x} = A.convolution B x := rfl

@[to_additive]
/--
lemma `card_div_eq` / 引理 `card_div_eq`

English:
lemma card_div_eq
  given: (A B : Finset G) (x : G)
  proof: Finset.card_equiv ((Equiv.refl _).prodCongr (.inv _)) (by simp [div_eq_mul_inv])

@[to_additive card_add_neg_eq_addConvolution_neg]

中文:
引理 card_div_eq
  条件: (A B : 有限集 G) (x : G)
  证明: Finset.card_equiv ((Equiv.refl _).prodCongr (.inv _)) (by simp [div_eq_mul_inv])

@[to_additive card_add_neg_eq_addConvolution_neg]

Depends on / 依赖: Equiv.refl, Finset, Finset.card_equiv, card_equiv, div_eq_mul_inv, prodCongr
-/
lemma card_div_eq (A B : Finset G) (x : G) :
    #{ab in A ×ˢ B | ab.1 / ab.2 = x} = A.convolution B⁻¹ x :=
  Finset.card_equiv ((Equiv.refl _).prodCongr (.inv _)) (by simp [div_eq_mul_inv])

@[to_additive card_add_neg_eq_addConvolution_neg]
/--
lemma `card_mul_inv_eq_convolution_inv` / 引理 `card_mul_inv_eq_convolution_inv`

English:
lemma card_mul_inv_eq_convolution_inv
  given: (A B : Finset G) (x : G)
  proof: card_nbij' (fun ab => (ab.1, ab.2⁻¹)) (fun ab => (ab.1, ab.2⁻¹))
    (by simp [Set.MapsTo]) (by simp [Set.MapsTo])
    (by simp [Set.LeftInvOn]) (by simp [Set.LeftInvOn])

@[to_additive (attr := simp) addConvolution_pos]

中文:
引理 card_mul_inv_eq_convolution_inv
  条件: (A B : 有限集 G) (x : G)
  证明: card_nbij' (fun ab => (ab.1, ab.2⁻¹)) (fun ab => (ab.1, ab.2⁻¹))
    (by simp [Set.MapsTo]) (by simp [Set.MapsTo])
    (by simp [Set.LeftInvOn]) (by simp [Set.LeftInvOn])

@[to_additive (attr := simp) addConvolution_pos]

Depends on / 依赖: LeftInvOn, MapsTo, Set.LeftInvOn, Set.MapsTo, card_nbij
-/
lemma card_mul_inv_eq_convolution_inv (A B : Finset G) (x : G) :
    #{ab in A ×ˢ B | ab.1 * ab.2⁻¹ = x} = A.convolution B⁻¹ x :=
  card_nbij' (fun ab => (ab.1, ab.2⁻¹)) (fun ab => (ab.1, ab.2⁻¹))
    (by simp [Set.MapsTo]) (by simp [Set.MapsTo])
    (by simp [Set.LeftInvOn]) (by simp [Set.LeftInvOn])

@[to_additive (attr := simp) addConvolution_pos]
/--
lemma `convolution_pos` / 引理 `convolution_pos`

English:
lemma convolution_pos
  statement: 0 < A.convolution B x ↔ x in A * B
  proof: by
  aesop (add simp [convolution, Finset.Nonempty, mem_mul])

@[to_additive addConvolution_ne_zero]

中文:
引理 convolution_pos
  结论: 0 < A.convolution B x ↔ x in A * B
  证明: by
  aesop (add simp [convolution, Finset.Nonempty, mem_mul])

@[to_additive addConvolution_ne_zero]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty, convolution, mem_mul
-/
lemma convolution_pos : 0 < A.convolution B x ↔ x in A * B := by
  aesop (add simp [convolution, Finset.Nonempty, mem_mul])

@[to_additive addConvolution_ne_zero]
/--
lemma `convolution_ne_zero` / 引理 `convolution_ne_zero`

English:
lemma convolution_ne_zero
  statement: A.convolution B x != 0 ↔ x in A * B
  proof: by
  suffices A.convolution B x != 0 ↔ 0 < A.convolution B x by simp [this]
  lia

@[to_additive (attr := simp) addConvolution_eq_zero]

中文:
引理 convolution_ne_zero
  结论: A.convolution B x != 0 ↔ x in A * B
  证明: by
  suffices A.convolution B x != 0 ↔ 0 < A.convolution B x by simp [this]
  lia

@[to_additive (attr := simp) addConvolution_eq_zero]

Depends on / 依赖: A.convolution, convolution
-/
lemma convolution_ne_zero : A.convolution B x != 0 ↔ x in A * B := by
  suffices A.convolution B x != 0 ↔ 0 < A.convolution B x by simp [this]
  lia

@[to_additive (attr := simp) addConvolution_eq_zero]
/--
lemma `convolution_eq_zero` / 引理 `convolution_eq_zero`

English:
lemma convolution_eq_zero
  statement: A.convolution B x = 0 ↔ x ∉ A * B
  proof: by
  simp [← convolution_ne_zero]

@[to_additive addConvolution_le_card_left]

中文:
引理 convolution_eq_zero
  结论: A.convolution B x = 0 ↔ x ∉ A * B
  证明: by
  simp [← convolution_ne_zero]

@[to_additive addConvolution_le_card_left]

Depends on / 依赖: convolution_ne_zero
-/
lemma convolution_eq_zero : A.convolution B x = 0 ↔ x ∉ A * B := by
  simp [← convolution_ne_zero]

@[to_additive addConvolution_le_card_left]
/--
lemma `convolution_le_card_left` / 引理 `convolution_le_card_left`

English:
lemma convolution_le_card_left
  statement: A.convolution B x <= #A
  proof: by
  rw [← inv_inv B]; rw [← card_inter_smul]
  exact card_le_card inter_subset_left

@[to_additive addConvolution_le_card_right]

中文:
引理 convolution_le_card_left
  结论: A.convolution B x <= #A
  证明: by
  rw [← inv_inv B]; rw [← card_inter_smul]
  exact card_le_card inter_subset_left

@[to_additive addConvolution_le_card_right]

Depends on / 依赖: card_inter_smul, card_le_card, inter_subset_left, inv_inv
-/
lemma convolution_le_card_left : A.convolution B x <= #A := by
  rw [← inv_inv B]; rw [← card_inter_smul]
  exact card_le_card inter_subset_left

@[to_additive addConvolution_le_card_right]
/--
lemma `convolution_le_card_right` / 引理 `convolution_le_card_right`

English:
lemma convolution_le_card_right
  statement: A.convolution B x <= #B
  proof: by
  rw [← inv_inv B]; rw [← inv_inv x]; rw [← card_smul_inter]; rw [card_inv]
  exact card_le_card inter_subset_right

@[to_additive (attr := simp) addConvolution_neg]

中文:
引理 convolution_le_card_right
  结论: A.convolution B x <= #B
  证明: by
  rw [← inv_inv B]; rw [← inv_inv x]; rw [← card_smul_inter]; rw [card_inv]
  exact card_le_card inter_subset_right

@[to_additive (attr := simp) addConvolution_neg]

Depends on / 依赖: card_inv, card_le_card, card_smul_inter, inter_subset_right, inv_inv
-/
lemma convolution_le_card_right : A.convolution B x <= #B := by
  rw [← inv_inv B]; rw [← inv_inv x]; rw [← card_smul_inter]; rw [card_inv]
  exact card_le_card inter_subset_right

@[to_additive (attr := simp) addConvolution_neg]
/--
lemma `convolution_inv` / 引理 `convolution_inv`

English:
lemma convolution_inv
  given: (A B : Finset G) (x : G)
  statement: A.convolution B x⁻¹ = B⁻¹.convolution A⁻¹ x
  proof: by
  nth_rw 1 [← inv_inv B]
  rw [← card_smul_inter]; rw [← card_inter_smul]; rw [inter_comm]

@[to_additive (attr := simp) op_vadd_addConvolution_eq_addConvolution_vadd]

中文:
引理 convolution_inv
  条件: (A B : 有限集 G) (x : G)
  结论: A.convolution B x⁻¹ = B⁻¹.convolution A⁻¹ x
  证明: by
  nth_rw 1 [← inv_inv B]
  rw [← card_smul_inter]; rw [← card_inter_smul]; rw [inter_comm]

@[to_additive (attr := simp) op_vadd_addConvolution_eq_addConvolution_vadd]

Depends on / 依赖: card_inter_smul, card_smul_inter, inter_comm, inv_inv, nth_rw
-/
lemma convolution_inv (A B : Finset G) (x : G) : A.convolution B x⁻¹ = B⁻¹.convolution A⁻¹ x := by
  nth_rw 1 [← inv_inv B]
  rw [← card_smul_inter]; rw [← card_inter_smul]; rw [inter_comm]

@[to_additive (attr := simp) op_vadd_addConvolution_eq_addConvolution_vadd]
/--
lemma `op_smul_convolution_eq_convolution_smul` / 引理 `op_smul_convolution_eq_convolution_smul`

English:
lemma op_smul_convolution_eq_convolution_smul
  given: (A B : Finset G) (s : G)
  proof: funext fun x => by
  nth_rw 1 [← inv_inv B, ← inv_inv (s • B), inv_smul_finset_distrib s B, ← card_inter_smul,
    ← card_inter_smul, smul_comm]
  simp [← card_smul_finset (op s) (A inter _), smul_finset_inter]

@[to_additive (attr := simp) vadd_addConvolution_eq_addConvolution_neg_add]

中文:
引理 op_smul_convolution_eq_convolution_smul
  条件: (A B : 有限集 G) (s : G)
  证明: funext fun x => by
  nth_rw 1 [← inv_inv B, ← inv_inv (s • B), inv_smul_finset_distrib s B, ← card_inter_smul,
    ← card_inter_smul, smul_comm]
  simp [← card_smul_finset (op s) (A inter _), smul_finset_inter]

@[to_additive (attr := simp) vadd_addConvolution_eq_addConvolution_neg_add]

Depends on / 依赖: card_inter_smul, card_smul_finset, inv_inv, inv_smul_finset_distrib, nth_rw, smul_comm, smul_finset_inter
-/
lemma op_smul_convolution_eq_convolution_smul (A B : Finset G) (s : G) :
    (A <• s).convolution B = A.convolution (s • B) := funext fun x => by
  nth_rw 1 [← inv_inv B, ← inv_inv (s • B), inv_smul_finset_distrib s B, ← card_inter_smul,
    ← card_inter_smul, smul_comm]
  simp [← card_smul_finset (op s) (A inter _), smul_finset_inter]

@[to_additive (attr := simp) vadd_addConvolution_eq_addConvolution_neg_add]
/--
lemma `smul_convolution_eq_convolution_inv_mul` / 引理 `smul_convolution_eq_convolution_inv_mul`

English:
lemma smul_convolution_eq_convolution_inv_mul
  given: (A B : Finset G) (s x : G)
  proof: by
  nth_rw 1 [← inv_inv x, ← inv_inv (s⁻¹ * x)]
  rw [← inv_inv B]; rw [← card_smul_inter]; rw [← card_smul_inter]; rw [mul_inv_rev]; rw [inv_inv]; rw [smul_smul]

@[to_additive (attr := simp) addConvolution_op_vadd_eq_addConvolution_add_neg]

中文:
引理 smul_convolution_eq_convolution_inv_mul
  条件: (A B : 有限集 G) (s x : G)
  证明: by
  nth_rw 1 [← inv_inv x, ← inv_inv (s⁻¹ * x)]
  rw [← inv_inv B]; rw [← card_smul_inter]; rw [← card_smul_inter]; rw [mul_inv_rev]; rw [inv_inv]; rw [smul_smul]

@[to_additive (attr := simp) addConvolution_op_vadd_eq_addConvolution_add_neg]

Depends on / 依赖: card_smul_inter, inv_inv, mul_inv_rev, nth_rw, smul_smul
-/
lemma smul_convolution_eq_convolution_inv_mul (A B : Finset G) (s x : G) :
    (s •> A).convolution B x = A.convolution B (s⁻¹ * x) := by
  nth_rw 1 [← inv_inv x, ← inv_inv (s⁻¹ * x)]
  rw [← inv_inv B]; rw [← card_smul_inter]; rw [← card_smul_inter]; rw [mul_inv_rev]; rw [inv_inv]; rw [smul_smul]

@[to_additive (attr := simp) addConvolution_op_vadd_eq_addConvolution_add_neg]
/--
lemma `convolution_op_smul_eq_convolution_mul_inv` / 引理 `convolution_op_smul_eq_convolution_mul_inv`

English:
lemma convolution_op_smul_eq_convolution_mul_inv
  given: (A B : Finset G) (s x : G)
  proof: by
  nth_rw 2 [← inv_inv B]
  rw [← inv_inv (B <• s)]; rw [inv_op_smul_finset_distrib]; rw [← card_inter_smul]; rw [← card_inter_smul]; rw [smul_smul]

中文:
引理 convolution_op_smul_eq_convolution_mul_inv
  条件: (A B : 有限集 G) (s x : G)
  证明: by
  nth_rw 2 [← inv_inv B]
  rw [← inv_inv (B <• s)]; rw [inv_op_smul_finset_distrib]; rw [← card_inter_smul]; rw [← card_inter_smul]; rw [smul_smul]

Depends on / 依赖: card_inter_smul, inv_inv, inv_op_smul_finset_distrib, nth_rw, smul_smul
-/
lemma convolution_op_smul_eq_convolution_mul_inv (A B : Finset G) (s x : G) :
    A.convolution (B <• s) x = A.convolution B (x * s⁻¹) := by
  nth_rw 2 [← inv_inv B]
  rw [← inv_inv (B <• s)]; rw [inv_op_smul_finset_distrib]; rw [← card_inter_smul]; rw [← card_inter_smul]; rw [smul_smul]

variable [Fintype G]

@[to_additive (attr := simp) univ_addConvolution]
/--
lemma `univ_convolution` / 引理 `univ_convolution`

English:
lemma univ_convolution
  given: (B : Finset G) (a : G)
  statement: univ.convolution B a = #B
  proof: by
  simp [← card_inter_smul_inv]

@[to_additive (attr := simp) addConvolution_univ]

中文:
引理 univ_convolution
  条件: (B : 有限集 G) (a : G)
  结论: univ.convolution B a = #B
  证明: by
  simp [← card_inter_smul_inv]

@[to_additive (attr := simp) addConvolution_univ]

Depends on / 依赖: card_inter_smul_inv
-/
lemma univ_convolution (B : Finset G) (a : G) : univ.convolution B a = #B := by
  simp [← card_inter_smul_inv]

@[to_additive (attr := simp) addConvolution_univ]
/--
lemma `convolution_univ` / 引理 `convolution_univ`

English:
lemma convolution_univ
  given: (A : Finset G) (a : G)
  statement: A.convolution univ a = #A
  proof: by
  simp [← card_inter_smul_inv]

中文:
引理 convolution_univ
  条件: (A : 有限集 G) (a : G)
  结论: A.convolution univ a = #A
  证明: by
  simp [← card_inter_smul_inv]

Depends on / 依赖: card_inter_smul_inv
-/
lemma convolution_univ (A : Finset G) (a : G) : A.convolution univ a = #A := by
  simp [← card_inter_smul_inv]

end Finset
