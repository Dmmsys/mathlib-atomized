/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
module

public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Logic.Embedding.Basic

/-!
# Embeddings of `Fin n`

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file defines embeddings between `Fin n` and other types,

## Main definitions

* `Fin.valEmbedding` : coercion to natural numbers as an `Embedding`;
* `Fin.succEmb` : `Fin.succ` as an `Embedding`;
* `Fin.castLEEmb h` : `Fin.castLE` as an `Embedding`, embed `Fin n` into `Fin m`, `h : n ≤ m`;
* `Fin.castAddEmb m` : `Fin.castAdd` as an `Embedding`, embed `Fin n` into `Fin (n+m)`;
* `Fin.castSuccEmb` : `Fin.castSucc` as an `Embedding`, embed `Fin n` into `Fin (n+1)`;
* `Fin.addNatEmb m i` : `Fin.addNat` as an `Embedding`, add `m` on `i` on the right,
  generalizes `Fin.succ`;
* `Fin.natAddEmb n i` : `Fin.natAdd` as an `Embedding`, adds `n` on `i` on the left;

-/

@[expose] public section

assert_not_exists Monoid Finset

open Fin Nat Function

namespace Fin

variable {n m : Nat}

section Order

/-!
### order
-/

/-- The inclusion map `Fin n → ℕ` is an embedding. -/
@[simps -fullyApplied apply]
/--
Definition of `valEmbedding` / `valEmbedding` 的定义

English:
definition valEmbedding
  signature: : Fin n ↪ Nat
  body: ⟨val, val_injective⟩

@[simp]

中文:
定义 valEmbedding
  签名: : Fin n ↪ 自然数
  定义体: ⟨val, val_injective⟩

@[simp]

Depends on / 依赖: val_injective
-/
def valEmbedding : Fin n ↪ Nat :=
  ⟨val, val_injective⟩

@[simp]
/--
theorem `equivSubtype_symm_trans_valEmbedding` / 定理 `equivSubtype_symm_trans_valEmbedding`

English:
theorem equivSubtype_symm_trans_valEmbedding
  proof: rfl

中文:
定理 equivSubtype_symm_trans_valEmbedding
  证明: rfl
-/
theorem equivSubtype_symm_trans_valEmbedding :
    equivSubtype.symm.toEmbedding.trans valEmbedding = Embedding.subtype (· < n) :=
  rfl

end Order

section Succ

/-!
### succ and casts into larger Fin types
-/

/--
Definition of `succEmb` / `succEmb` 的定义

English:
definition succEmb
  signature: (n : Nat)
  body: succ
  inj' := succ_injective _

@[simp]

中文:
定义 succEmb
  签名: (n : 自然数)
  定义体: succ
  inj' := succ_injective _

@[simp]
-/
def succEmb (n : Nat) : Fin n ↪ Fin (n + 1) where
  toFun := succ
  inj' := succ_injective _

@[simp]
/--
theorem `coe_succEmb` / 定理 `coe_succEmb`

English:
theorem coe_succEmb
  statement: ⇑(succEmb n) = Fin.succ
  proof: rfl

中文:
定理 coe_succEmb
  结论: ⇑(succEmb n) = Fin.succ
  证明: rfl
-/
theorem coe_succEmb : ⇑(succEmb n) = Fin.succ :=
  rfl

attribute [simp] castSucc_inj

/-- `Fin.castLE` as an `Embedding`, `castLEEmb h i` embeds `i` into a larger `Fin` type. -/
@[simps apply]
/--
Definition of `castLEEmb` / `castLEEmb` 的定义

English:
definition castLEEmb
  signature: (h : n <= m)
  body: castLE h
  inj' := castLE_injective _

中文:
定义 castLEEmb
  签名: (h : n <= m)
  定义体: castLE h
  inj' := castLE_injective _

Depends on / 依赖: castLE
-/
def castLEEmb (h : n <= m) : Fin n ↪ Fin m where
  toFun := castLE h
  inj' := castLE_injective _

/--
lemma `coe_castLEEmb` / 引理 `coe_castLEEmb`

English:
lemma coe_castLEEmb
  given: {m n} (hmn : m <= n)
  statement: castLEEmb hmn = castLE hmn
  proof: rfl

中文:
引理 coe_castLEEmb
  条件: {m n} (hmn : m <= n)
  结论: castLEEmb hmn = castLE hmn
  证明: rfl
-/
@[simp, norm_cast] lemma coe_castLEEmb {m n} (hmn : m <= n) : castLEEmb hmn = castLE hmn := rfl

/--
lemma `nonempty_embedding_iff` / 引理 `nonempty_embedding_iff`

English:
lemma nonempty_embedding_iff
  statement: Nonempty (Fin n ↪ Fin m) ↔ n <= m
  proof: by
  refine ⟨fun h => ?_, fun h => ⟨castLEEmb h⟩⟩
  induction n generalizing m with
  | zero => exact m.zero_le
  | succ n ihn =>
    obtain ⟨e⟩ := h
    rcases exists_eq_succ_of_ne_zero (pos_iff_nonempty.2 (Nonempty.map e inferInstance)).ne'
      with ⟨m, rfl⟩
refine Nat.succ_le_succ ihn ⟨?_⟩
    

中文:
引理 nonempty_embedding_iff
  结论: Nonempty (Fin n ↪ Fin m) ↔ n <= m
  证明: by
  refine ⟨fun h => ?_, fun h => ⟨castLEEmb h⟩⟩
  induction n generalizing m with
  | zero => exact m.zero_le
  | succ n ihn =>
    obtain ⟨e⟩ := h
    rcases exists_eq_succ_of_ne_zero (pos_iff_nonempty.2 (Nonempty.map e inferInstance)).ne'
      with ⟨m, rfl⟩
refine Nat.succ_le_succ ihn ⟨?_⟩
    

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Nat.succ_le_succ, Nonempty, Nonempty.map, apply_eq_iff_eq, castLEEmb, e.setValue, e.setValue_eq_iff, exists_eq_succ_of_ne_zero, generalizing, i.succ, i.succ_ne_zero, m.zero_le, pos_iff_nonempty, pred_inj, setValue, setValue_eq_iff, succ_inj, succ_le_succ
-/
lemma nonempty_embedding_iff : Nonempty (Fin n ↪ Fin m) ↔ n <= m := by
  refine ⟨fun h => ?_, fun h => ⟨castLEEmb h⟩⟩
  induction n generalizing m with
  | zero => exact m.zero_le
  | succ n ihn =>
    obtain ⟨e⟩ := h
    rcases exists_eq_succ_of_ne_zero (pos_iff_nonempty.2 (Nonempty.map e inferInstance)).ne'
      with ⟨m, rfl⟩
refine Nat.succ_le_succ ihn ⟨?_⟩
    refine ⟨fun i => (e.setValue 0 0 i.succ).pred (mt e.setValue_eq_iff.1 i.succ_ne_zero),
      fun i j h => ?_⟩
    simpa only [pred_inj, EmbeddingLike.apply_eq_iff_eq, succ_inj] using h

/--
lemma `equiv_iff_eq` / 引理 `equiv_iff_eq`

English:
lemma equiv_iff_eq
  statement: Nonempty (Fin m ≃ Fin n) ↔ m = n
  proof: ⟨fun ⟨e⟩ => le_antisymm (nonempty_embedding_iff.1 ⟨e⟩) (nonempty_embedding_iff.1 ⟨e.symm⟩),
    fun h => h ▸ ⟨.refl _⟩⟩

中文:
引理 equiv_iff_eq
  结论: Nonempty (Fin m ≃ Fin n) ↔ m = n
  证明: ⟨fun ⟨e⟩ => le_antisymm (nonempty_embedding_iff.1 ⟨e⟩) (nonempty_embedding_iff.1 ⟨e.symm⟩),
    fun h => h ▸ ⟨.refl _⟩⟩

Depends on / 依赖: e.symm, le_antisymm, nonempty_embedding_iff
-/
lemma equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n :=
  ⟨fun ⟨e⟩ => le_antisymm (nonempty_embedding_iff.1 ⟨e⟩) (nonempty_embedding_iff.1 ⟨e.symm⟩),
    fun h => h ▸ ⟨.refl _⟩⟩

/--
Definition of `castAddEmb` / `castAddEmb` 的定义

English:
definition castAddEmb
  signature: (m)
  body: castLEEmb (le_add_right n m)

@[simp]

中文:
定义 castAddEmb
  签名: (m)
  定义体: castLEEmb (le_add_right n m)

@[simp]

Depends on / 依赖: castLEEmb, le_add_right
-/
def castAddEmb (m) : Fin n ↪ Fin (n + m) := castLEEmb (le_add_right n m)

@[simp]
/--
lemma `coe_castAddEmb` / 引理 `coe_castAddEmb`

English:
lemma coe_castAddEmb
  given: (m)
  statement: (castAddEmb m : Fin n -> Fin (n + m)) = castAdd m
  proof: rfl

中文:
引理 coe_castAddEmb
  条件: (m)
  结论: (castAddEmb m : Fin n -> Fin (n + m)) = castAdd m
  证明: rfl
-/
lemma coe_castAddEmb (m) : (castAddEmb m : Fin n -> Fin (n + m)) = castAdd m := rfl

/--
lemma `castAddEmb_apply` / 引理 `castAddEmb_apply`

English:
lemma castAddEmb_apply
  given: (m) (i : Fin n)
  statement: castAddEmb m i = castAdd m i
  proof: rfl

中文:
引理 castAddEmb_apply
  条件: (m) (i : Fin n)
  结论: castAddEmb m i = castAdd m i
  证明: rfl
-/
lemma castAddEmb_apply (m) (i : Fin n) : castAddEmb m i = castAdd m i := rfl

/--
Definition of `castSuccEmb` / `castSuccEmb` 的定义

English:
definition castSuccEmb
  signature: : Fin n ↪ Fin (n + 1)
  body: castAddEmb _

中文:
定义 castSuccEmb
  签名: : Fin n ↪ Fin (n + 1)
  定义体: castAddEmb _

Depends on / 依赖: castAddEmb
-/
def castSuccEmb : Fin n ↪ Fin (n + 1) := castAddEmb _

/--
lemma `coe_castSuccEmb` / 引理 `coe_castSuccEmb`

English:
lemma coe_castSuccEmb
  statement: (castSuccEmb : Fin n -> Fin (n + 1)) = Fin.castSucc
  proof: rfl

中文:
引理 coe_castSuccEmb
  结论: (castSuccEmb : Fin n -> Fin (n + 1)) = Fin.castSucc
  证明: rfl
-/
@[simp, norm_cast] lemma coe_castSuccEmb : (castSuccEmb : Fin n -> Fin (n + 1)) = Fin.castSucc := rfl

/--
lemma `castSuccEmb_apply` / 引理 `castSuccEmb_apply`

English:
lemma castSuccEmb_apply
  given: (i : Fin n)
  statement: castSuccEmb i = i.castSucc
  proof: rfl

中文:
引理 castSuccEmb_apply
  条件: (i : Fin n)
  结论: castSuccEmb i = i.castSucc
  证明: rfl
-/
lemma castSuccEmb_apply (i : Fin n) : castSuccEmb i = i.castSucc := rfl

/-- `Fin.addNat` as an `Embedding`, `addNatEmb m i` adds `m` to `i`, generalizes `Fin.succ`. -/
@[simps! apply]
/--
Definition of `addNatEmb` / `addNatEmb` 的定义

English:
definition addNatEmb
  signature: (m)
  body: (addNat · m)
  inj' a b := by simp [Fin.ext_iff]

中文:
定义 addNatEmb
  签名: (m)
  定义体: (addNat · m)
  inj' a b := by simp [Fin.ext_iff]

Depends on / 依赖: addNat
-/
def addNatEmb (m) : Fin n ↪ Fin (n + m) where
  toFun := (addNat · m)
  inj' a b := by simp [Fin.ext_iff]

/-- `Fin.natAdd` as an `Embedding`, `natAddEmb n i` adds `n` to `i` "on the left". -/
@[simps! apply]
/--
Definition of `natAddEmb` / `natAddEmb` 的定义

English:
definition natAddEmb
  signature: (n) {m}
  body: natAdd n
  inj' a b := by simp [Fin.ext_iff]

中文:
定义 natAddEmb
  签名: (n) {m}
  定义体: natAdd n
  inj' a b := by simp [Fin.ext_iff]

Depends on / 依赖: natAdd
-/
def natAddEmb (n) {m} : Fin m ↪ Fin (n + m) where
  toFun := natAdd n
  inj' a b := by simp [Fin.ext_iff]

end Succ

section SuccAbove

variable {p : Fin (n + 1)}

/-- `Fin.succAbove p` as an `Embedding`. -/
@[simps!]
/--
Definition of `succAboveEmb` / `succAboveEmb` 的定义

English:
definition succAboveEmb
  signature: (p : Fin (n + 1))
  body: ⟨p.succAbove, succAbove_right_injective⟩

中文:
定义 succAboveEmb
  签名: (p : Fin (n + 1))
  定义体: ⟨p.succAbove, succAbove_right_injective⟩

Depends on / 依赖: p.succAbove, succAbove, succAbove_right_injective
-/
def succAboveEmb (p : Fin (n + 1)) : Fin n ↪ Fin (n + 1) := ⟨p.succAbove, succAbove_right_injective⟩

/--
lemma `coe_succAboveEmb` / 引理 `coe_succAboveEmb`

English:
lemma coe_succAboveEmb
  given: (p : Fin (n + 1))
  statement: p.succAboveEmb = p.succAbove
  proof: rfl

中文:
引理 coe_succAboveEmb
  条件: (p : Fin (n + 1))
  结论: p.succAboveEmb = p.succAbove
  证明: rfl
-/
@[simp, norm_cast] lemma coe_succAboveEmb (p : Fin (n + 1)) : p.succAboveEmb = p.succAbove := rfl

/-- `Fin.natAdd_castLEEmb` as an `Embedding` from `Fin n` to `Fin m`, by appending the former
at the end of the latter.
`natAdd_castLEEmb hmn i` maps `i : Fin m` to `i + (m - n) : Fin n` by adding `m - n` to `i` -/
@[simps!]
/--
Definition of `natAdd_castLEEmb` / `natAdd_castLEEmb` 的定义

English:
definition natAdd_castLEEmb
  signature: (hmn : n <= m)
  body: (addNatEmb (m - n)).trans (finCongr (by lia)).toEmbedding

中文:
定义 natAdd_castLEEmb
  签名: (hmn : n <= m)
  定义体: (addNatEmb (m - n)).trans (finCongr (by lia)).toEmbedding

Depends on / 依赖: addNatEmb, finCongr, toEmbedding
-/
def natAdd_castLEEmb (hmn : n <= m) : Fin n ↪ Fin m :=
  (addNatEmb (m - n)).trans (finCongr (by lia)).toEmbedding

/--
lemma `range_natAdd_castLEEmb` / 引理 `range_natAdd_castLEEmb`

English:
lemma range_natAdd_castLEEmb
  given: {n m : Nat} (hmn : n <= m)
  proof: by
  simp only [natAdd_castLEEmb, Nat.sub_le_iff_le_add]
  ext y
  exact ⟨fun ⟨x, hx⟩ => by simp [← hx]; lia,
    fun xin => ⟨subNat (m - n) (y.cast (Nat.add_sub_of_le hmn).symm)
    (Nat.sub_le_of_le_add xin), by simp⟩⟩

中文:
引理 range_natAdd_castLEEmb
  条件: {n m : 自然数} (hmn : n <= m)
  证明: by
  simp only [natAdd_castLEEmb, Nat.sub_le_iff_le_add]
  ext y
  exact ⟨fun ⟨x, hx⟩ => by simp [← hx]; lia,
    fun xin => ⟨subNat (m - n) (y.cast (Nat.add_sub_of_le hmn).symm)
    (Nat.sub_le_of_le_add xin), by simp⟩⟩

Depends on / 依赖: Nat.add_sub_of_le, Nat.sub_le_iff_le_add, Nat.sub_le_of_le_add, add_sub_of_le, natAdd_castLEEmb, subNat, sub_le_iff_le_add, sub_le_of_le_add, y.cast
-/
lemma range_natAdd_castLEEmb {n m : Nat} (hmn : n <= m) :
    Set.range (natAdd_castLEEmb hmn) = {i | m - n <= i.1} := by
  simp only [natAdd_castLEEmb, Nat.sub_le_iff_le_add]
  ext y
  exact ⟨fun ⟨x, hx⟩ => by simp [← hx]; lia,
    fun xin => ⟨subNat (m - n) (y.cast (Nat.add_sub_of_le hmn).symm)
    (Nat.sub_le_of_le_add xin), by simp⟩⟩

end SuccAbove

end Fin
