/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-!
# Connecting a chain complex and a cochain complex

Given a chain complex `K`: `... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0`,
a cochain complex `L`: `L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`,
a morphism `d₀ : K.X 0 ⟶ L.X 0` satisfying the identifies `K.d 1 0 ≫ d₀ = 0`
and `d₀ ≫ L.d 0 1 = 0`, we construct a cochain complex indexed by `ℤ` of the form
`... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0 ⟶ L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`,
where `K.X 0` lies in degree `-1` and `L.X 0` in degree `0`.

## Main definitions

Say `K : ChainComplex C ℕ` and `L : CochainComplex C ℕ`, so `... ⟶ K₂ ⟶ K₁ ⟶ K₀`
and `L⁰ ⟶ L¹ ⟶ L² ⟶ ...`.

* `ConnectData K L`: an auxiliary structure consisting of `d₀ : K₀ ⟶ L⁰` "connecting" the
  complexes and proofs that the induced maps `K₁ ⟶ K₀ ⟶ L⁰` and `K₀ ⟶ L⁰ ⟶ L¹` are both zero.

Now say `h : ConnectData K L`.

* `CochainComplex.ConnectData.cochainComplex h` : the induced ℤ-indexed complex
  `... ⟶ K₁ ⟶ K₀ ⟶ L⁰ ⟶ L¹ ⟶ ...`
* `CochainComplex.ConnectData.homologyIsoPos h (n : ℕ) (m : ℤ)` : if `m = n + 1`,
  the isomorphism `h.cochainComplex.homology m ≅ L.homology (n + 1)`
* `CochainComplex.ConnectData.homologyIsoNeg h (n : ℕ) (m : ℤ)` : if `m = -(n + 2)`,
  the isomorphism `h.cochainComplex.homology m ≅ K.homology (n + 1)`

## TODO

* Computation of `h.cochainComplex.homology k` when `k = 0` or `k = -1`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace CochainComplex

variable {K K' K'' : ChainComplex C Nat} {L L' L'' : CochainComplex C Nat}

variable (K L) in
/--
Definition of `ConnectData` / `ConnectData` 的定义

English:
structure ConnectData
  parameters: where
  axioms and operations (3):
    - d₀ : K.X 0 ⟶ L.X 0
    - comp_d₀ : K.d 1 0 ≫ d₀ = 0
    - d₀_comp : d₀ ≫ L.d 0 1 = 0

中文:
结构 余nnectData
  参数: where
  公理与运算 (3 个):
    - d₀ : K.X 0 ⟶ L.X 0
    - comp_d₀ : K.d 1 0 ≫ d₀ = 0
    - d₀_comp : d₀ ≫ L.d 0 1 = 0

Depends on / 依赖: Map_f_eq, Quiver, Quiver.Hom.op_inj, e.op, opFunctor, op_inj, truncGE
-/
structure ConnectData where
  /-- the differential which connect `K` and `L` -/
  d₀ : K.X 0 ⟶ L.X 0
  comp_d₀ : K.d 1 0 ≫ d₀ = 0
  d₀_comp : d₀ ≫ L.d 0 1 = 0

namespace ConnectData

attribute [reassoc (attr := simp)] comp_d₀ d₀_comp

variable (h : ConnectData K L) (h' : ConnectData K' L') (h'' : ConnectData K'' L'')

variable (K L) in
/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: : Int -> C

中文:
定义 X
  签名: : 整数 -> C

Depends on / 依赖: K.op.truncGE, Map_id, Quiver, Quiver.Hom.op, c.symm, congr_arg, congr_map, e.op, truncGE, unopFunctor
-/
def X : Int -> C
  | .ofNat n => L.X n
  | .negSucc n => K.X n

/--
lemma `X_ofNat` / 引理 `X_ofNat`

English:
lemma X_ofNat
  given: (n : Nat)
  statement: X K L n = L.X n
  proof: rfl

中文:
引理 X_of自然数
  条件: (n : 自然数)
  结论: X K L n = L.X n
  证明: rfl

Depends on / 依赖: Map_comp, Quiver, Quiver.Hom.op, c.symm, congr_arg, congr_map, e.op, opFunctor, truncGE, unopFunctor
-/
@[simp] lemma X_ofNat (n : Nat) : X K L n = L.X n := rfl
/--
lemma `X_negSucc` / 引理 `X_negSucc`

English:
lemma X_negSucc
  given: (n : Nat)
  statement: X K L (.negSucc n) = K.X n
  proof: rfl

中文:
引理 X_negSucc
  条件: (n : 自然数)
  结论: X K L (.negSucc n) = K.X n
  证明: rfl
-/
@[simp] lemma X_negSucc (n : Nat) : X K L (.negSucc n) = K.X n := rfl
/--
lemma `X_zero` / 引理 `X_zero`

English:
lemma X_zero
  statement: X K L 0 = L.X 0
  proof: rfl

中文:
引理 X_zero
  结论: X K L 0 = L.X 0
  证明: rfl
-/
@[simp] lemma X_zero : X K L 0 = L.X 0 := rfl
/--
lemma `X_negOne` / 引理 `X_negOne`

English:
lemma X_negOne
  statement: X K L (-1) = K.X 0
  proof: rfl

中文:
引理 X_negOne
  结论: X K L (-1) = K.X 0
  证明: rfl
-/
@[simp] lemma X_negOne : X K L (-1) = K.X 0 := rfl

/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: : forall (n m : Int), X K L n ⟶ X K L m

中文:
定义 d
  签名: : 对任意 (n m : 整数), X K L n ⟶ X K L m

Depends on / 依赖: K.op.restrictionToTruncGE, c.symm, e.op, restrictionToTruncGE, unopFunctor
-/
def d : forall (n m : Int), X K L n ⟶ X K L m
  | .ofNat n, .ofNat m => L.d n m
  | .negSucc n, .negSucc m => K.d n m
  | .negSucc 0, .ofNat 0 => h.d₀
  | .ofNat _, .negSucc _ => 0
  | .negSucc _, .ofNat _ => 0

/--
lemma `d_ofNat` / 引理 `d_ofNat`

English:
lemma d_ofNat
  given: (n m : Nat)
  statement: h.d n m = L.d n m
  proof: rfl

中文:
引理 d_of自然数
  条件: (n m : 自然数)
  结论: h.d n m = L.d n m
  证明: rfl
-/
@[simp] lemma d_ofNat (n m : Nat) : h.d n m = L.d n m := rfl
/--
lemma `d_negSucc` / 引理 `d_negSucc`

English:
lemma d_negSucc
  given: (n m : Nat)
  statement: h.d (.negSucc n) (.negSucc m) = K.d n m
  proof: by simp [d]

中文:
引理 d_negSucc
  条件: (n m : 自然数)
  结论: h.d (.negSucc n) (.negSucc m) = K.d n m
  证明: by simp [d]

Depends on / 依赖: Quiver, Quiver.Hom.op, _naturality, c.symm, congr_arg, congr_map, e.op, opFunctor, restrictionToTruncGE, unopFunctor
-/
@[simp] lemma d_negSucc (n m : Nat) : h.d (.negSucc n) (.negSucc m) = K.d n m := by simp [d]
/--
lemma `d_sub_one_zero` / 引理 `d_sub_one_zero`

English:
lemma d_sub_one_zero
  statement: h.d (-1) 0 = h.d₀
  proof: rfl

中文:
引理 d_sub_one_zero
  结论: h.d (-1) 0 = h.d₀
  证明: rfl

Depends on / 依赖: K.op.restrictionToTruncGE, e.op, restrictionToTruncGE
-/
@[simp] lemma d_sub_one_zero : h.d (-1) 0 = h.d₀ := rfl
/--
lemma `d_zero_one` / 引理 `d_zero_one`

English:
lemma d_zero_one
  statement: h.d 0 1 = L.d 0 1
  proof: rfl

中文:
引理 d_zero_one
  结论: h.d 0 1 = L.d 0 1
  证明: rfl
-/
@[simp] lemma d_zero_one : h.d 0 1 = L.d 0 1 := rfl
/--
lemma `d_sub_two_sub_one` / 引理 `d_sub_two_sub_one`

English:
lemma d_sub_two_sub_one
  statement: h.d (-2) (-1) = K.d 1 0
  proof: rfl

中文:
引理 d_sub_two_sub_one
  结论: h.d (-2) (-1) = K.d 1 0
  证明: rfl
-/
@[simp] lemma d_sub_two_sub_one : h.d (-2) (-1) = K.d 1 0 := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `shape` / 引理 `shape`

English:
lemma shape
  given: (n m : Int) (hnm : n + 1 != m)
  statement: h.d n m = 0
  proof: match n, m with
  | .ofNat n, .ofNat m => L.shape _ _ (by simp at hnm ⊢; lia)
  | .negSucc n, .negSucc m => by
    simpa only [d_negSucc] using! K.shape n m (by simp at hnm ⊢; lia)
  | .negSucc 0, .ofNat 0 => by simp at hnm
  | .ofNat _, .negSucc m => rfl
  | .negSucc n, .ofNat m => by
    obtain _ 

中文:
引理 shape
  条件: (n m : 整数) (hnm : n + 1 != m)
  结论: h.d n m = 0
  证明: match n, m with
  | .ofNat n, .ofNat m => L.shape _ _ (by simp at hnm ⊢; lia)
  | .negSucc n, .negSucc m => by
    simpa only [d_negSucc] using! K.shape n m (by simp at hnm ⊢; lia)
  | .negSucc 0, .ofNat 0 => by simp at hnm
  | .ofNat _, .negSucc m => rfl
  | .negSucc n, .ofNat m => by
    obtain _ 

Depends on / 依赖: K.op, K.shape, L.shape, d_negSucc, e.op, negSucc
-/
lemma shape (n m : Int) (hnm : n + 1 != m) : h.d n m = 0 :=
  match n, m with
  | .ofNat n, .ofNat m => L.shape _ _ (by simp at hnm ⊢; lia)
  | .negSucc n, .negSucc m => by
    simpa only [d_negSucc] using! K.shape n m (by simp at hnm ⊢; lia)
  | .negSucc 0, .ofNat 0 => by simp at hnm
  | .ofNat _, .negSucc m => rfl
  | .negSucc n, .ofNat m => by
    obtain _ | n := n
    · obtain _ | m := m
      · simp at hnm
      · rfl
    · simp only [d]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `d_comp_d` / 引理 `d_comp_d`

English:
lemma d_comp_d
  given: (n m p : Int)
  statement: h.d n m ≫ h.d m p = 0
  proof: by
  by_cases hnm : n + 1 = m; swap
  · rw [h.shape n m hnm, zero_comp]
  by_cases hmp : m + 1 = p; swap
  · rw [h.shape m p hmp, comp_zero]
  obtain n | (_ | _ | n) := n
  · obtain rfl : m = .ofNat (n + 1) := by simp [← hnm]
    obtain rfl : p = .ofNat (n + 2) := by simp [← hmp]; lia
    simp only 

中文:
引理 d_comp_d
  条件: (n m p : 整数)
  结论: h.d n m ≫ h.d m p = 0
  证明: by
  by_cases hnm : n + 1 = m; swap
  · rw [h.shape n m hnm, zero_comp]
  by_cases hmp : m + 1 = p; swap
  · rw [h.shape m p hmp, comp_zero]
  obtain n | (_ | _ | n) := n
  · obtain rfl : m = .ofNat (n + 1) := by simp [← hnm]
    obtain rfl : p = .ofNat (n + 2) := by simp [← hmp]; lia
    simp only 

Depends on / 依赖: HomologicalComplex, HomologicalComplex.d_comp_d, Int.ofNat_eq_natCast, X_ofNat, comp_zero, d_comp_d, d_ofNat, h.shape, ofNat_eq_natCast, zero_comp
-/
lemma d_comp_d (n m p : Int) : h.d n m ≫ h.d m p = 0 := by
  by_cases hnm : n + 1 = m; swap
  · rw [h.shape n m hnm, zero_comp]
  by_cases hmp : m + 1 = p; swap
  · rw [h.shape m p hmp, comp_zero]
  obtain n | (_ | _ | n) := n
  · obtain rfl : m = .ofNat (n + 1) := by simp [← hnm]
    obtain rfl : p = .ofNat (n + 2) := by simp [← hmp]; lia
    simp only [Int.ofNat_eq_natCast, X_ofNat, d_ofNat, HomologicalComplex.d_comp_d]
  · obtain rfl : m = 0 := by lia
    obtain rfl : p = 1 := by lia
    simp
  · obtain rfl : m = -1 := by lia
    obtain rfl : p = 0 := by lia
    simp
  · obtain rfl : m = .negSucc (n + 1) := by lia
    obtain rfl : p = .negSucc n := by lia
    simp

/-- Given `h : ConnectData K L` where `K : ChainComplex C ℕ` and `L : CochainComplex C ℕ`,
this is the cochain complex indexed by `ℤ` obtained by connecting `K` and `L`:
`... ⟶ K.X 2 ⟶ K.X 1 ⟶ K.X 0 ⟶ L.X 0 ⟶ L.X 1 ⟶ L.X 2 ⟶ ...`. -/
@[simps]
/--
Definition of `cochainComplex` / `cochainComplex` 的定义

English:
definition cochainComplex
  signature: : CochainComplex C Int where
  body: X K L
  d := h.d
  shape := h.shape

中文:
定义 cochainComplex
  签名: : 上链复形 C 整数 where
  定义体: X K L
  d := h.d
  shape := h.shape
-/
def cochainComplex : CochainComplex C Int where
  X := X K L
  d := h.d
  shape := h.shape

open HomologicalComplex

set_option backward.isDefEq.respectTransparency false in
/-- If `h : ConnectData K L`, then `h.cochainComplex` identifies to `L` in degrees `≥ 0`. -/
@[simps!]
/--
Definition of `restrictionGEIso` / `restrictionGEIso` 的定义

English:
definition restrictionGEIso
  signature: :
  body: Hom.isoOfComponents
    (fun n => h.cochainComplex.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
      (i := n) (i' := n) (by simp)) (by
    rintro n _ rfl
    rw [restriction_d_eq (e := (ComplexShape.embeddingUpIntGE 0)) _ (i' := n)
      (j' := (n + 1 : Nat)) (by simp) (by simp)]; rw [cochainC

中文:
定义 restrictionGEIso
  签名: :
  定义体: Hom.isoOfComponents
    (fun n => h.cochainComplex.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
      (i := n) (i' := n) (by simp)) (by
    rintro n _ rfl
    rw [restriction_d_eq (e := (ComplexShape.embeddingUpIntGE 0)) _ (i' := n)
      (j' := (n + 1 : Nat)) (by simp) (by simp)]; rw [cochainC

Depends on / 依赖: ComplexShape, ComplexShape.embeddingUpIntGE, Hom.isoOfComponents, cochainComplex, cochainComplex_d, d_ofNat, embeddingUpIntGE, h.cochainComplex.restrictionXIso, h.d_ofNat, isoOfComponents, restrictionXIso, restriction_d_eq
-/
def restrictionGEIso :
    h.cochainComplex.restriction (ComplexShape.embeddingUpIntGE 0) ≅ L :=
  Hom.isoOfComponents
    (fun n => h.cochainComplex.restrictionXIso (ComplexShape.embeddingUpIntGE 0)
      (i := n) (i' := n) (by simp)) (by
    rintro n _ rfl
    rw [restriction_d_eq (e := (ComplexShape.embeddingUpIntGE 0)) _ (i' := n)
      (j' := (n + 1 : Nat)) (by simp) (by simp)]; rw [cochainComplex_d]; rw [h.d_ofNat]
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `h : ConnectData K L`, then `h.cochainComplex` identifies to `K` in degrees `≤ -1`. -/
@[simps!]
/--
Definition of `restrictionLEIso` / `restrictionLEIso` 的定义

English:
definition restrictionLEIso
  signature: :
  body: Hom.isoOfComponents
    (fun n => h.cochainComplex.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
        (i := n) (i' := .negSucc n) (by dsimp; lia)) (by
    rintro _ n rfl
    rw [restriction_d_eq (e := (ComplexShape.embeddingUpIntLE (-1))) _
      (i' := Int.negSucc (n + 1)) (j' := Int.negS

中文:
定义 restrictionLEIso
  签名: :
  定义体: Hom.isoOfComponents
    (fun n => h.cochainComplex.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
        (i := n) (i' := .negSucc n) (by dsimp; lia)) (by
    rintro _ n rfl
    rw [restriction_d_eq (e := (ComplexShape.embeddingUpIntLE (-1))) _
      (i' := Int.negSucc (n + 1)) (j' := Int.negS

Depends on / 依赖: ComplexShape, ComplexShape.embeddingUpIntLE, Hom.isoOfComponents, Int.negSucc, IsStrictlySupported, K.op.truncGE, cochainComplex, cochainComplex_d, d_negSucc, e.op, embeddingUpIntLE, h.cochainComplex.restrictionXIso, isStrictlySupported_op_iff, isoOfComponents, negSucc, restrictionXIso, restriction_d_eq, truncGE
-/
def restrictionLEIso :
    h.cochainComplex.restriction (ComplexShape.embeddingUpIntLE (-1)) ≅ K :=
  Hom.isoOfComponents
    (fun n => h.cochainComplex.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
        (i := n) (i' := .negSucc n) (by dsimp; lia)) (by
    rintro _ n rfl
    rw [restriction_d_eq (e := (ComplexShape.embeddingUpIntLE (-1))) _
      (i' := Int.negSucc (n + 1)) (j' := Int.negSucc n) (by dsimp; lia) (by dsimp; lia)]; rw [cochainComplex_d]; rw [d_negSucc]
    simp)

/--
Definition of `homologyIsoPos` / `homologyIsoPos` 的定义

English:
definition homologyIsoPos
  signature: (n : Nat) [NeZero n] (m : Int) (hm : m = n)
  body: have := hasHomology_of_iso h.restrictionGEIso.symm n
  (h.cochainComplex.restrictionHomologyIso
    (ComplexShape.embeddingUpIntGE 0) (n - 1) n (n + 1) (by cases n <;> simp) (by simp)
      (i' := m - 1) (j' := m) (k' := m + 1) (by have := NeZero.ne n; cases n <;> simp <;> lia)
      (by simp; lia) 

中文:
定义 homologyIsoPos
  签名: (n : 自然数) [NeZero n] (m : 整数) (hm : m = n)
  定义体: have := hasHomology_of_iso h.restrictionGEIso.symm n
  (h.cochainComplex.restrictionHomologyIso
    (ComplexShape.embeddingUpIntGE 0) (n - 1) n (n + 1) (by cases n <;> simp) (by simp)
      (i' := m - 1) (j' := m) (k' := m + 1) (by have := NeZero.ne n; cases n <;> simp <;> lia)
      (by simp; lia) 

Depends on / 依赖: ComplexShape, ComplexShape.embeddingUpIntGE, HomologicalComplex, HomologicalComplex.homologyMapIso, NeZero, NeZero.ne, cochainComplex, embeddingUpIntGE, h.cochainComplex.restrictionHomologyIso, h.restrictionGEIso, h.restrictionGEIso.symm, hasHomology_of_iso, homologyMapIso, restrictionGEIso, restrictionHomologyIso
-/
noncomputable def homologyIsoPos (n : Nat) [NeZero n] (m : Int) (hm : m = n)
    [h.cochainComplex.HasHomology m] [L.HasHomology n] :
    h.cochainComplex.homology m ≅ L.homology n :=
  have := hasHomology_of_iso h.restrictionGEIso.symm n
  (h.cochainComplex.restrictionHomologyIso
    (ComplexShape.embeddingUpIntGE 0) (n - 1) n (n + 1) (by cases n <;> simp) (by simp)
      (i' := m - 1) (j' := m) (k' := m + 1) (by have := NeZero.ne n; cases n <;> simp <;> lia)
      (by simp; lia) (by simp; lia) (by simp) (by simp)).symm ≪≫
    HomologicalComplex.homologyMapIso h.restrictionGEIso n

/--
Definition of `homologyIsoNeg` / `homologyIsoNeg` 的定义

English:
definition homologyIsoNeg
  signature: (n : Nat) [NeZero n] (m : Int) (hm : m = -(n + 1 : Nat))
  body: have := hasHomology_of_iso h.restrictionLEIso.symm n
  (h.cochainComplex.restrictionHomologyIso
    (ComplexShape.embeddingUpIntLE (-1)) (n + 1) n (n - 1) (by simp) (by cases n <;> simp)
      (i' := m - 1) (j' := m) (k' := m + 1) (by simp; lia) (by simp; lia)
      (by have := NeZero.ne n; cases n 

中文:
定义 homologyIsoNeg
  签名: (n : 自然数) [NeZero n] (m : 整数) (hm : m = -(n + 1 : 自然数))
  定义体: have := hasHomology_of_iso h.restrictionLEIso.symm n
  (h.cochainComplex.restrictionHomologyIso
    (ComplexShape.embeddingUpIntLE (-1)) (n + 1) n (n - 1) (by simp) (by cases n <;> simp)
      (i' := m - 1) (j' := m) (k' := m + 1) (by simp; lia) (by simp; lia)
      (by have := NeZero.ne n; cases n 

Depends on / 依赖: ComplexShape, ComplexShape.embeddingUpIntLE, HomologicalComplex, HomologicalComplex.homologyMapIso, NeZero, NeZero.ne, cochainComplex, embeddingUpIntLE, h.cochainComplex.restrictionHomologyIso, h.restrictionLEIso, h.restrictionLEIso.symm, hasHomology_of_iso, homologyMapIso, restrictionHomologyIso, restrictionLEIso
-/
noncomputable def homologyIsoNeg (n : Nat) [NeZero n] (m : Int) (hm : m = -(n + 1 : Nat))
    [h.cochainComplex.HasHomology m] [K.HasHomology n] :
    h.cochainComplex.homology m ≅ K.homology n :=
  have := hasHomology_of_iso h.restrictionLEIso.symm n
  (h.cochainComplex.restrictionHomologyIso
    (ComplexShape.embeddingUpIntLE (-1)) (n + 1) n (n - 1) (by simp) (by cases n <;> simp)
      (i' := m - 1) (j' := m) (k' := m + 1) (by simp; lia) (by simp; lia)
      (by have := NeZero.ne n; cases n <;> simp <;> lia) (by simp) (by simp)).symm ≪≫
    HomologicalComplex.homologyMapIso h.restrictionLEIso n

variable
  (fK : K ⟶ K') (fL : L ⟶ L') (f_comm : fK.f 0 ≫ h'.d₀ = h.d₀ ≫ fL.f 0)
  (fK' : K' ⟶ K'') (fL' : L' ⟶ L'') (f_comm' : fK'.f 0 ≫ h''.d₀ = h'.d₀ ≫ fL'.f 0)

/-- Connecting complexes is functorial. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : h.cochainComplex ⟶ h'.cochainComplex where

中文:
定义 map
  签名: : h.cochainComplex ⟶ h'.cochainComplex where
-/
protected def map : h.cochainComplex ⟶ h'.cochainComplex where
  f
  | .ofNat n => fL.f n
  | .negSucc n => fK.f n
  comm'
  | .ofNat i, _, .refl _ => fL.comm _ _
  | .negSucc 0, _, .refl _ => by simpa
  | .negSucc (i + 1), _, .refl _ => fK.comm _ _

set_option backward.defeqAttrib.useBackward true in
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: h.map h (𝟙 K) (𝟙 L) (by simp) = 𝟙 _
  proof: by ext (m | _ | m) <;> simp; rfl

中文:
引理 map_id
  结论: h.map h (𝟙 K) (𝟙 L) (by simp) = 𝟙 _
  证明: by ext (m | _ | m) <;> simp; rfl

Depends on / 依赖: K.truncLE, ToRestriction, truncLE
-/
@[simp] lemma map_id : h.map h (𝟙 K) (𝟙 L) (by simp) = 𝟙 _ := by ext (m | _ | m) <;> simp; rfl

set_option backward.defeqAttrib.useBackward true in
/--
lemma `map_comp_map` / 引理 `map_comp_map`

English:
lemma map_comp_map
  proof: by
  ext (m | _ | m) <;> simp; rfl

中文:
引理 map_comp_map
  证明: by
  ext (m | _ | m) <;> simp; rfl
-/
lemma map_comp_map :
    h.map h' fK fL f_comm ≫ h'.map h'' fK' fL' f_comm'
     = h.map h'' (fK ≫ fK') (fL ≫ fL') (by simp [f_comm', reassoc_of% f_comm]) := by
  ext (m | _ | m) <;> simp; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `homologyMap_map_of_eq_succ` / 引理 `homologyMap_map_of_eq_succ`

English:
lemma homologyMap_map_of_eq_succ
  statement: (n : Nat) [NeZero n] (m : Int) (hmn : m = n)
  proof: by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [homologyIsoPos]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOp

中文:
引理 homologyMap_map_of_eq_succ
  结论: (n : 自然数) [NeZero n] (m : 整数) (hmn : m = n)
  证明: by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [homologyIsoPos]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOp

Depends on / 依赖: Category, Category.assoc, HomologicalComplex, HomologicalComplex.homology, HomologicalComplex.pOpcycles, cancel_epi, cancel_mono, homologyIsoPos, pOpcycles
-/
lemma homologyMap_map_of_eq_succ (n : Nat) [NeZero n] (m : Int) (hmn : m = n)
    [HasHomology h.cochainComplex m] [HasHomology L n]
    [HasHomology h'.cochainComplex m] [HasHomology L' n] :
    homologyMap (h.map h' fK fL f_comm) m =
    (h.homologyIsoPos n m hmn).hom ≫ homologyMap fL n ≫ (h'.homologyIsoPos n m hmn).inv := by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [homologyIsoPos]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOpcycles ..)]
  subst hmn
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `homologyMap_map_of_eq_neg_succ` / 引理 `homologyMap_map_of_eq_neg_succ`

English:
lemma homologyMap_map_of_eq_neg_succ
  statement: (n : Nat) [NeZero n] (m : Int) (hmn : m = -↑(n + 1))
  proof: by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [homologyIsoNeg]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOp

中文:
引理 homologyMap_map_of_eq_neg_succ
  结论: (n : 自然数) [NeZero n] (m : 整数) (hmn : m = -↑(n + 1))
  证明: by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [homologyIsoNeg]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOp

Depends on / 依赖: Category, Category.assoc, HomologicalComplex, HomologicalComplex.homology, HomologicalComplex.pOpcycles, cancel_epi, cancel_mono, homologyIsoNeg, negSucc, pOpcycles
-/
lemma homologyMap_map_of_eq_neg_succ (n : Nat) [NeZero n] (m : Int) (hmn : m = -↑(n + 1))
    [HasHomology h.cochainComplex m] [HasHomology K n]
    [HasHomology h'.cochainComplex m] [HasHomology K' n] :
    homologyMap (h.map h' fK fL f_comm) m =
      (h.homologyIsoNeg n m hmn).hom ≫ homologyMap fK n ≫ (h'.homologyIsoNeg n m hmn).inv := by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [homologyIsoNeg]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOpcycles ..)]
  obtain rfl : m = .negSucc n := hmn
  simp

end ConnectData

end CochainComplex
