/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Algebraic properties of tuples
-/

public section

namespace Fin
variable {n : Nat} {α : Fin (n + 1) -> Type*}

@[to_additive (attr := simp)]
/--
lemma `insertNth_one_right` / 引理 `insertNth_one_right`

English:
lemma insertNth_one_right
  given: [forall j, One (α j)] (i : Fin (n + 1)) (x : α i)
  proof: insertNth_eq_iff.2 by unfold removeNth; simp [succAbove_ne, Pi.one_def]

@[to_additive (attr := simp)]

中文:
引理 insertNth_one_right
  条件: [对任意 j, 幺 (α j)] (i : 有限集 (n + 1)) (x : α i)
  证明: insertNth_eq_iff.2 by unfold removeNth; simp [succAbove_ne, Pi.one_def]

@[to_additive (attr := simp)]

Depends on / 依赖: Pi.one_def, insertNth_eq_iff, one_def, removeNth, succAbove_ne
-/
lemma insertNth_one_right [forall j, One (α j)] (i : Fin (n + 1)) (x : α i) :
    i.insertNth x 1 = Pi.mulSingle i x :=
insertNth_eq_iff.2 by unfold removeNth; simp [succAbove_ne, Pi.one_def]

@[to_additive (attr := simp)]
/--
lemma `insertNth_mul` / 引理 `insertNth_mul`

English:
lemma insertNth_mul
  given: [forall j, Mul (α j)] (i : Fin (n + 1)) (x y : α i) (p q : forall j, α (i.succAbove j))
  proof: insertNth_binop (fun _ => (· * ·)) i x y p q

@[to_additive (attr := simp)]

中文:
引理 insertNth_mul
  条件: [对任意 j, 乘法 (α j)] (i : 有限集 (n + 1)) (x y : α i) (p q : 对任意 j, α (i.succAbove j))
  证明: insertNth_binop (fun _ => (· * ·)) i x y p q

@[to_additive (attr := simp)]

Depends on / 依赖: insertNth_binop
-/
lemma insertNth_mul [forall j, Mul (α j)] (i : Fin (n + 1)) (x y : α i) (p q : forall j, α (i.succAbove j)) :
    i.insertNth (x * y) (p * q) = i.insertNth x p * i.insertNth y q :=
  insertNth_binop (fun _ => (· * ·)) i x y p q

@[to_additive (attr := simp)]
/--
lemma `insertNth_div` / 引理 `insertNth_div`

English:
lemma insertNth_div
  given: [forall j, Div (α j)] (i : Fin (n + 1)) (x y : α i) (p q : forall j, α (i.succAbove j))
  proof: insertNth_binop (fun _ => (· / ·)) i x y p q

@[to_additive (attr := simp)]

中文:
引理 insertNth_div
  条件: [对任意 j, 除法 (α j)] (i : 有限集 (n + 1)) (x y : α i) (p q : 对任意 j, α (i.succAbove j))
  证明: insertNth_binop (fun _ => (· / ·)) i x y p q

@[to_additive (attr := simp)]

Depends on / 依赖: insertNth_binop
-/
lemma insertNth_div [forall j, Div (α j)] (i : Fin (n + 1)) (x y : α i) (p q : forall j, α (i.succAbove j)) :
    i.insertNth (x / y) (p / q) = i.insertNth x p / i.insertNth y q :=
  insertNth_binop (fun _ => (· / ·)) i x y p q

@[to_additive (attr := simp)]
/--
lemma `insertNth_div_same` / 引理 `insertNth_div_same`

English:
lemma insertNth_div_same
  statement: [forall j, Group (α j)] (i : Fin (n + 1)) (x y : α i)
  proof: by
  simp_rw [← insertNth_div, ← insertNth_one_right, Pi.div_def, div_self', Pi.one_def]

中文:
引理 insertNth_div_same
  结论: [对任意 j, 群 (α j)] (i : 有限集 (n + 1)) (x y : α i)
  证明: by
  simp_rw [← insertNth_div, ← insertNth_one_right, Pi.div_def, div_self', Pi.one_def]

Depends on / 依赖: Pi.div_def, Pi.one_def, div_def, div_self, insertNth_div, insertNth_one_right, one_def, simp_rw
-/
lemma insertNth_div_same [forall j, Group (α j)] (i : Fin (n + 1)) (x y : α i)
    (p : forall j, α (i.succAbove j)) : i.insertNth x p / i.insertNth y p = Pi.mulSingle i (x / y) := by
  simp_rw [← insertNth_div, ← insertNth_one_right, Pi.div_def, div_self', Pi.one_def]

end Fin

namespace Matrix

variable {α M : Type*} {n : Nat}

section SMul
variable [SMul M α]

/--
lemma `smul_empty` / 引理 `smul_empty`

English:
lemma smul_empty
  given: (x : M) (v : Fin 0 -> α)
  statement: x • v = ![]
  proof: empty_eq _

中文:
引理 smul_empty
  条件: (x : M) (v : 有限集 0 -> α)
  结论: x • v = ![]
  证明: empty_eq _
-/
@[simp] lemma smul_empty (x : M) (v : Fin 0 -> α) : x • v = ![] := empty_eq _

/--
lemma `smul_cons` / 引理 `smul_cons`

English:
lemma smul_cons
  given: (x : M) (y : α) (v : Fin n -> α)
  proof: by ext i; refine i.cases ?_ ?_ <;> simp

中文:
引理 smul_cons
  条件: (x : M) (y : α) (v : 有限集 n -> α)
  证明: by ext i; refine i.cases ?_ ?_ <;> simp
-/
@[simp] lemma smul_cons (x : M) (y : α) (v : Fin n -> α) :
    x • vecCons y v = vecCons (x • y) (x • v) := by ext i; refine i.cases ?_ ?_ <;> simp

end SMul

section Add
variable [Add α]

/--
lemma `empty_add_empty` / 引理 `empty_add_empty`

English:
lemma empty_add_empty
  given: (v w : Fin 0 -> α)
  statement: v + w = ![]
  proof: empty_eq _

中文:
引理 empty_add_empty
  条件: (v w : 有限集 0 -> α)
  结论: v + w = ![]
  证明: empty_eq _
-/
@[simp] lemma empty_add_empty (v w : Fin 0 -> α) : v + w = ![] := empty_eq _

/--
lemma `cons_add` / 引理 `cons_add`

English:
lemma cons_add
  given: (x : α) (v : Fin n -> α) (w : Fin n.succ -> α)
  proof: by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]

中文:
引理 cons_add
  条件: (x : α) (v : 有限集 n -> α) (w : 有限集 n.succ -> α)
  证明: by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
-/
@[simp] lemma cons_add (x : α) (v : Fin n -> α) (w : Fin n.succ -> α) :
    vecCons x v + w = vecCons (x + vecHead w) (v + vecTail w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]

/--
lemma `add_cons` / 引理 `add_cons`

English:
lemma add_cons
  given: (v : Fin n.succ -> α) (y : α) (w : Fin n -> α)
  proof: by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]

中文:
引理 add_cons
  条件: (v : 有限集 n.succ -> α) (y : α) (w : 有限集 n -> α)
  证明: by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
-/
@[simp] lemma add_cons (v : Fin n.succ -> α) (y : α) (w : Fin n -> α) :
    v + vecCons y w = vecCons (vecHead v + y) (vecTail v + w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]

/--
lemma `cons_add_cons` / 引理 `cons_add_cons`

English:
lemma cons_add_cons
  given: (x : α) (v : Fin n -> α) (y : α) (w : Fin n -> α)
  proof: by simp

中文:
引理 cons_add_cons
  条件: (x : α) (v : 有限集 n -> α) (y : α) (w : 有限集 n -> α)
  证明: by simp
-/
lemma cons_add_cons (x : α) (v : Fin n -> α) (y : α) (w : Fin n -> α) :
    vecCons x v + vecCons y w = vecCons (x + y) (v + w) := by simp

/--
lemma `head_add` / 引理 `head_add`

English:
lemma head_add
  given: (a b : Fin n.succ -> α)
  statement: vecHead (a + b) = vecHead a + vecHead b
  proof: rfl

中文:
引理 head_add
  条件: (a b : 有限集 n.succ -> α)
  结论: vecHead (a + b) = vecHead a + vecHead b
  证明: rfl
-/
@[simp] lemma head_add (a b : Fin n.succ -> α) : vecHead (a + b) = vecHead a + vecHead b := rfl

/--
lemma `tail_add` / 引理 `tail_add`

English:
lemma tail_add
  given: (a b : Fin n.succ -> α)
  statement: vecTail (a + b) = vecTail a + vecTail b
  proof: rfl

中文:
引理 tail_add
  条件: (a b : 有限集 n.succ -> α)
  结论: vecTail (a + b) = vecTail a + vecTail b
  证明: rfl
-/
@[simp] lemma tail_add (a b : Fin n.succ -> α) : vecTail (a + b) = vecTail a + vecTail b := rfl

end Add

section Sub
variable [Sub α]

/--
lemma `empty_sub_empty` / 引理 `empty_sub_empty`

English:
lemma empty_sub_empty
  given: (v w : Fin 0 -> α)
  statement: v - w = ![]
  proof: empty_eq _

中文:
引理 empty_sub_empty
  条件: (v w : 有限集 0 -> α)
  结论: v - w = ![]
  证明: empty_eq _
-/
@[simp] lemma empty_sub_empty (v w : Fin 0 -> α) : v - w = ![] := empty_eq _

/--
lemma `cons_sub` / 引理 `cons_sub`

English:
lemma cons_sub
  given: (x : α) (v : Fin n -> α) (w : Fin n.succ -> α)
  proof: by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]

中文:
引理 cons_sub
  条件: (x : α) (v : 有限集 n -> α) (w : 有限集 n.succ -> α)
  证明: by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
-/
@[simp] lemma cons_sub (x : α) (v : Fin n -> α) (w : Fin n.succ -> α) :
    vecCons x v - w = vecCons (x - vecHead w) (v - vecTail w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]

/--
lemma `sub_cons` / 引理 `sub_cons`

English:
lemma sub_cons
  given: (v : Fin n.succ -> α) (y : α) (w : Fin n -> α)
  proof: by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]

中文:
引理 sub_cons
  条件: (v : 有限集 n.succ -> α) (y : α) (w : 有限集 n -> α)
  证明: by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
-/
@[simp] lemma sub_cons (v : Fin n.succ -> α) (y : α) (w : Fin n -> α) :
    v - vecCons y w = vecCons (vecHead v - y) (vecTail v - w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]

/--
lemma `cons_sub_cons` / 引理 `cons_sub_cons`

English:
lemma cons_sub_cons
  given: (x : α) (v : Fin n -> α) (y : α) (w : Fin n -> α)
  proof: by simp

中文:
引理 cons_sub_cons
  条件: (x : α) (v : 有限集 n -> α) (y : α) (w : 有限集 n -> α)
  证明: by simp
-/
lemma cons_sub_cons (x : α) (v : Fin n -> α) (y : α) (w : Fin n -> α) :
    vecCons x v - vecCons y w = vecCons (x - y) (v - w) := by simp

/--
lemma `head_sub` / 引理 `head_sub`

English:
lemma head_sub
  given: (a b : Fin n.succ -> α)
  statement: vecHead (a - b) = vecHead a - vecHead b
  proof: rfl

中文:
引理 head_sub
  条件: (a b : 有限集 n.succ -> α)
  结论: vecHead (a - b) = vecHead a - vecHead b
  证明: rfl
-/
@[simp] lemma head_sub (a b : Fin n.succ -> α) : vecHead (a - b) = vecHead a - vecHead b := rfl

/--
lemma `tail_sub` / 引理 `tail_sub`

English:
lemma tail_sub
  given: (a b : Fin n.succ -> α)
  statement: vecTail (a - b) = vecTail a - vecTail b
  proof: rfl

中文:
引理 tail_sub
  条件: (a b : 有限集 n.succ -> α)
  结论: vecTail (a - b) = vecTail a - vecTail b
  证明: rfl
-/
@[simp] lemma tail_sub (a b : Fin n.succ -> α) : vecTail (a - b) = vecTail a - vecTail b := rfl

end Sub

section Zero
variable [Zero α]

/--
lemma `zero_empty` / 引理 `zero_empty`

English:
lemma zero_empty
  statement: (0 : Fin 0 -> α) = ![]
  proof: empty_eq _

中文:
引理 zero_empty
  结论: (0 : 有限集 0 -> α) = ![]
  证明: empty_eq _
-/
@[simp] lemma zero_empty : (0 : Fin 0 -> α) = ![] := empty_eq _

/--
lemma `finZeroElim_eq_zero` / 引理 `finZeroElim_eq_zero`

English:
lemma finZeroElim_eq_zero
  statement: (@finZeroElim fun _ => α) = 0
  proof: by
  rw [Matrix.empty_eq finZeroElim]; rw [Matrix.zero_empty]

中文:
引理 finZeroElim_eq_zero
  结论: (@finZeroElim fun _ => α) = 0
  证明: by
  rw [Matrix.empty_eq finZeroElim]; rw [Matrix.zero_empty]
-/
@[simp] lemma finZeroElim_eq_zero : (@finZeroElim fun _ => α) = 0 := by
  rw [Matrix.empty_eq finZeroElim]; rw [Matrix.zero_empty]

/--
lemma `cons_zero_zero` / 引理 `cons_zero_zero`

English:
lemma cons_zero_zero
  statement: vecCons (0 : α) (0 : Fin n -> α) = 0
  proof: by
  ext i; exact i.cases rfl (by simp)

中文:
引理 cons_zero_zero
  结论: vecCons (0 : α) (0 : 有限集 n -> α) = 0
  证明: by
  ext i; exact i.cases rfl (by simp)
-/
@[simp] lemma cons_zero_zero : vecCons (0 : α) (0 : Fin n -> α) = 0 := by
  ext i; exact i.cases rfl (by simp)

/--
lemma `head_zero` / 引理 `head_zero`

English:
lemma head_zero
  statement: vecHead (0 : Fin n.succ -> α) = 0
  proof: rfl

中文:
引理 head_zero
  结论: vecHead (0 : 有限集 n.succ -> α) = 0
  证明: rfl
-/
@[simp] lemma head_zero : vecHead (0 : Fin n.succ -> α) = 0 := rfl

/--
lemma `tail_zero` / 引理 `tail_zero`

English:
lemma tail_zero
  statement: vecTail (0 : Fin n.succ -> α) = 0
  proof: rfl

中文:
引理 tail_zero
  结论: vecTail (0 : 有限集 n.succ -> α) = 0
  证明: rfl
-/
@[simp] lemma tail_zero : vecTail (0 : Fin n.succ -> α) = 0 := rfl

/--
lemma `cons_eq_zero_iff` / 引理 `cons_eq_zero_iff`

English:
lemma cons_eq_zero_iff
  given: {v : Fin n -> α} {x : α}
  statement: vecCons x v = 0 ↔ x = 0 ∧ v = 0 where
  proof: ⟨congr_fun h 0, by convert! congr_arg vecTail h⟩
  mpr := fun ⟨hx, hv⟩ => by simp [hx, hv]

中文:
引理 cons_eq_zero_iff
  条件: {v : 有限集 n -> α} {x : α}
  结论: vecCons x v = 0 ↔ x = 0 ∧ v = 0 where
  证明: ⟨congr_fun h 0, by convert! congr_arg vecTail h⟩
  mpr := fun ⟨hx, hv⟩ => by simp [hx, hv]
-/
@[simp] lemma cons_eq_zero_iff {v : Fin n -> α} {x : α} : vecCons x v = 0 ↔ x = 0 ∧ v = 0 where
  mp h := ⟨congr_fun h 0, by convert! congr_arg vecTail h⟩
  mpr := fun ⟨hx, hv⟩ => by simp [hx, hv]

/--
lemma `cons_nonzero_iff` / 引理 `cons_nonzero_iff`

English:
lemma cons_nonzero_iff
  given: {v : Fin n -> α} {x : α}
  statement: vecCons x v != 0 ↔ x != 0 ∨ v != 0 where
  proof: not_and_or.mp (h ∘ cons_eq_zero_iff.mpr)
  mpr h := mt cons_eq_zero_iff.mp (not_and_or.mpr h)

中文:
引理 cons_nonzero_iff
  条件: {v : 有限集 n -> α} {x : α}
  结论: vecCons x v != 0 ↔ x != 0 ∨ v != 0 where
  证明: not_and_or.mp (h ∘ cons_eq_zero_iff.mpr)
  mpr h := mt cons_eq_zero_iff.mp (not_and_or.mpr h)

Depends on / 依赖: cons_eq_zero_iff, cons_eq_zero_iff.mpr, not_and_or, not_and_or.mp
-/
lemma cons_nonzero_iff {v : Fin n -> α} {x : α} : vecCons x v != 0 ↔ x != 0 ∨ v != 0 where
  mp h := not_and_or.mp (h ∘ cons_eq_zero_iff.mpr)
  mpr h := mt cons_eq_zero_iff.mp (not_and_or.mpr h)

end Zero

section Neg
variable [Neg α]

/--
lemma `neg_empty` / 引理 `neg_empty`

English:
lemma neg_empty
  given: (v : Fin 0 -> α)
  statement: -v = ![]
  proof: empty_eq _

中文:
引理 neg_empty
  条件: (v : 有限集 0 -> α)
  结论: -v = ![]
  证明: empty_eq _
-/
@[simp] lemma neg_empty (v : Fin 0 -> α) : -v = ![] := empty_eq _

/--
lemma `neg_cons` / 引理 `neg_cons`

English:
lemma neg_cons
  given: (x : α) (v : Fin n -> α)
  statement: -vecCons x v = vecCons (-x) (-v)
  proof: by
  ext i; refine i.cases ?_ ?_ <;> simp

中文:
引理 neg_cons
  条件: (x : α) (v : 有限集 n -> α)
  结论: -vecCons x v = vecCons (-x) (-v)
  证明: by
  ext i; refine i.cases ?_ ?_ <;> simp
-/
@[simp] lemma neg_cons (x : α) (v : Fin n -> α) : -vecCons x v = vecCons (-x) (-v) := by
  ext i; refine i.cases ?_ ?_ <;> simp

/--
lemma `head_neg` / 引理 `head_neg`

English:
lemma head_neg
  given: (a : Fin n.succ -> α)
  statement: vecHead (-a) = -vecHead a
  proof: rfl

中文:
引理 head_neg
  条件: (a : 有限集 n.succ -> α)
  结论: vecHead (-a) = -vecHead a
  证明: rfl
-/
@[simp] lemma head_neg (a : Fin n.succ -> α) : vecHead (-a) = -vecHead a := rfl

/--
lemma `tail_neg` / 引理 `tail_neg`

English:
lemma tail_neg
  given: (a : Fin n.succ -> α)
  statement: vecTail (-a) = -vecTail a
  proof: rfl

中文:
引理 tail_neg
  条件: (a : 有限集 n.succ -> α)
  结论: vecTail (-a) = -vecTail a
  证明: rfl
-/
@[simp] lemma tail_neg (a : Fin n.succ -> α) : vecTail (-a) = -vecTail a := rfl

end Neg
end Matrix
