/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The mapping cocone

Given a morphism `φ : K ⟶ L` of cochain complexes, the mapping cone
allows to obtain a triangle `K ⟶ L ⟶ mappingCone φ ⟶ ...`. In this
file, we define the mapping cocone, which fits in a rotated triangle:
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`.

-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex Pretriangulated

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C Int} (φ : K ⟶ L)

/--
Definition of `mappingCocone` / `mappingCocone` 的定义

English:
definition mappingCocone
  signature: [HasHomotopyCofiber φ]
  body: (mappingCone φ)⟦(-1 : Int)⟧

中文:
定义 mappingCocone
  签名: [有HomotopyCofiber φ]
  定义体: (mappingCone φ)⟦(-1 : Int)⟧

Depends on / 依赖: mappingCone
-/
noncomputable def mappingCocone [HasHomotopyCofiber φ] :
    CochainComplex C Int := (mappingCone φ)⟦(-1 : Int)⟧

namespace mappingCocone

section

variable [HasHomotopyCofiber φ]

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : mappingCocone φ ⟶ K
  body: -((mappingCone.fst φ).leftShift (-1) 0 (add_neg_cancel 1)).homOf

中文:
定义 fst
  签名: : mappingCocone φ ⟶ K
  定义体: -((mappingCone.fst φ).leftShift (-1) 0 (add_neg_cancel 1)).homOf

Depends on / 依赖: add_neg_cancel, leftShift, mappingCone, mappingCone.fst
-/
noncomputable def fst : mappingCocone φ ⟶ K :=
  -((mappingCone.fst φ).leftShift (-1) 0 (add_neg_cancel 1)).homOf

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : Cochain (mappingCocone φ) L (-1)
  body: (mappingCone.snd φ).leftShift (-1) (-1) (zero_add _)

中文:
定义 snd
  签名: : Cochain (mappingCocone φ) L (-1)
  定义体: (mappingCone.snd φ).leftShift (-1) (-1) (zero_add _)

Depends on / 依赖: leftShift, mappingCone, mappingCone.snd, zero_add
-/
noncomputable def snd : Cochain (mappingCocone φ) L (-1) :=
  (mappingCone.snd φ).leftShift (-1) (-1) (zero_add _)

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : Cochain K (mappingCocone φ) 0
  body: (mappingCone.inl φ).rightShift (-1) 0 (zero_add _)

中文:
定义 inl
  签名: : Cochain K (mappingCocone φ) 0
  定义体: (mappingCone.inl φ).rightShift (-1) 0 (zero_add _)

Depends on / 依赖: mappingCone, mappingCone.inl, rightShift, zero_add
-/
noncomputable def inl : Cochain K (mappingCocone φ) 0 :=
  (mappingCone.inl φ).rightShift (-1) 0 (zero_add _)

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : Cocycle L (mappingCocone φ) 1
  body: (Cocycle.ofHom (mappingCone.inr φ)).rightShift (-1) 1 (by lia)

中文:
定义 inr
  签名: : Cocycle L (mappingCocone φ) 1
  定义体: (Cocycle.ofHom (mappingCone.inr φ)).rightShift (-1) 1 (by lia)

Depends on / 依赖: Cocycle, Cocycle.ofHom, mappingCone, mappingCone.inr, rightShift
-/
noncomputable def inr : Cocycle L (mappingCocone φ) 1 :=
  (Cocycle.ofHom (mappingCone.inr φ)).rightShift (-1) 1 (by lia)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inl_v_fst_f` / 引理 `inl_v_fst_f`

English:
lemma inl_v_fst_f
  given: (p : Int)
  proof: by
  simp [inl, fst, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]

中文:
引理 inl_v_fst_f
  条件: (p : 整数)
  证明: by
  simp [inl, fst, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]

Depends on / 依赖: Cochain, Cochain.leftShift_v, Cochain.rightShift_v, leftShift_v, rightShift_v
-/
lemma inl_v_fst_f (p : Int) :
    (inl φ).v p p (add_zero p) ≫ (fst φ).f p = 𝟙 _ := by
  simp [inl, fst, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inl_v_snd_v` / 引理 `inl_v_snd_v`

English:
lemma inl_v_snd_v
  given: (p q : Int) (hpq : p + -1 = q)
  proof: by
  obtain rfl : q = p + -1 := by lia
  simp [inl, snd, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ hpq]

中文:
引理 inl_v_snd_v
  条件: (p q : 整数) (hpq : p + -1 = q)
  证明: by
  obtain rfl : q = p + -1 := by lia
  simp [inl, snd, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ hpq]

Depends on / 依赖: Cochain, Cochain.leftShift_v, Cochain.rightShift_v, leftShift_v, rightShift_v
-/
lemma inl_v_snd_v (p q : Int) (hpq : p + -1 = q) :
    (inl φ).v p p (add_zero p) ≫ (snd φ).v p q hpq = 0 := by
  obtain rfl : q = p + -1 := by lia
  simp [inl, snd, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ hpq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inr_v_fst_f` / 引理 `inr_v_fst_f`

English:
lemma inr_v_fst_f
  given: (p q : Int) (hpq : p + 1 = q)
  proof: by
  simp [inr, fst, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ hpq]

中文:
引理 inr_v_fst_f
  条件: (p q : 整数) (hpq : p + 1 = q)
  证明: by
  simp [inr, fst, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ hpq]

Depends on / 依赖: Cochain, Cochain.leftShift_v, Cochain.rightShift_v, add_zero, leftShift_v, rightShift_v
-/
lemma inr_v_fst_f (p q : Int) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (fst φ).f q = 0 := by
  simp [inr, fst, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ hpq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inr_v_snd_v` / 引理 `inr_v_snd_v`

English:
lemma inr_v_snd_v
  given: (p q : Int) (hpq : p + 1 = q)
  proof: by
  simp [inr, snd, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

中文:
引理 inr_v_snd_v
  条件: (p q : 整数) (hpq : p + 1 = q)
  证明: by
  simp [inr, snd, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

Depends on / 依赖: Cochain, Cochain.leftShift_v, Cochain.rightShift_v, Int.negOnePow_even, add_zero, leftShift_v, negOnePow_even, rightShift_v
-/
lemma inr_v_snd_v (p q : Int) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (snd φ).v q p (by lia) = 𝟙 _ := by
  simp [inr, snd, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `id_X` / 引理 `id_X`

English:
lemma id_X
  given: (p q : Int) (hpq : p + -1 = q)
  proof: by
  obtain rfl : q = p + -1 := by lia
  simp [fst, inl, snd, inr, mappingCocone,
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ hpq,
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add

中文:
引理 id_X
  条件: (p q : 整数) (hpq : p + -1 = q)
  证明: by
  obtain rfl : q = p + -1 := by lia
  simp [fst, inl, snd, inr, mappingCocone,
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ hpq,
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add

Depends on / 依赖: Cochain, Cochain.leftShift_v, Cochain.rightShift_v, Int.negOnePow_even, add_zero, id_X, leftShift_v, mappingCocone, mappingCone, mappingCone.id_X, negOnePow_even, rightShift_v
-/
lemma id_X (p q : Int) (hpq : p + -1 = q) :
    (fst φ).f p ≫ (inl φ).v p p (add_zero p) +
      (snd φ).v p q hpq ≫ (inr φ).1.v q p (by lia) = 𝟙 _ := by
  obtain rfl : q = p + -1 := by lia
  simp [fst, inl, snd, inr, mappingCocone,
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ hpq,
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Int.negOnePow_even 2 ⟨1, rfl⟩,
    mappingCone.id_X φ (p + -1) p (by lia)]

section

variable {M : CochainComplex C Int} {n m : Int}
  (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n)

/--
Definition of `descCochain` / `descCochain` 的定义

English:
definition descCochain
  signature: : Cochain (mappingCocone φ) M m
  body: (-m + 1).negOnePow • (mappingCone.descCochain φ α β h).leftShift (-1) m (by lia)

中文:
定义 descCochain
  签名: : Cochain (mappingCocone φ) M m
  定义体: (-m + 1).negOnePow • (mappingCone.descCochain φ α β h).leftShift (-1) m (by lia)

Depends on / 依赖: descCochain, leftShift, mappingCone, mappingCone.descCochain, negOnePow
-/
noncomputable def descCochain : Cochain (mappingCocone φ) M m :=
  (-m + 1).negOnePow • (mappingCone.descCochain φ α β h).leftShift (-1) m (by lia)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inl_v_descCochain_v` / 引理 `inl_v_descCochain_v`

English:
lemma inl_v_descCochain_v
  given: (p q : Int) (hpq : p + m = q)
  proof: by
  simp [inl, descCochain, mappingCocone,
    Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia), smul_smul,
    Cochain.leftShift_v (n := n) _ (-1) m (by lia) _ _ hpq (p + -1) (by lia)]

中文:
引理 inl_v_descCochain_v
  条件: (p q : 整数) (hpq : p + m = q)
  证明: by
  simp [inl, descCochain, mappingCocone,
    Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia), smul_smul,
    Cochain.leftShift_v (n := n) _ (-1) m (by lia) _ _ hpq (p + -1) (by lia)]

Depends on / 依赖: Cochain, Cochain.leftShift_v, Cochain.rightShift_v, descCochain, leftShift_v, mappingCocone, rightShift_v, smul_smul
-/
lemma inl_v_descCochain_v (p q : Int) (hpq : p + m = q) :
    (inl φ).v p p (add_zero _) ≫ (descCochain φ α β h).v p q hpq = α.v p q hpq := by
  simp [inl, descCochain, mappingCocone,
    Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia), smul_smul,
    Cochain.leftShift_v (n := n) _ (-1) m (by lia) _ _ hpq (p + -1) (by lia)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inr_v_descCochain_v` / 引理 `inr_v_descCochain_v`

English:
lemma inr_v_descCochain_v
  given: (p q : Int) (hpq : p + 1 = q) (r : Int) (hr : q + m = r)
  proof: by
  obtain rfl : p = q + -1 := by lia
  simp [inr, descCochain, mappingCocone, smul_smul,
    Cochain.rightShift_v _ _ _ _ _ _ hpq _ (add_zero (q + -1)),
    Cochain.leftShift_v (n := n) _ _ _ _ _ r _ (q + -1) (by lia)]

@[simp]

中文:
引理 inr_v_descCochain_v
  条件: (p q : 整数) (hpq : p + 1 = q) (r : 整数) (hr : q + m = r)
  证明: by
  obtain rfl : p = q + -1 := by lia
  simp [inr, descCochain, mappingCocone, smul_smul,
    Cochain.rightShift_v _ _ _ _ _ _ hpq _ (add_zero (q + -1)),
    Cochain.leftShift_v (n := n) _ _ _ _ _ r _ (q + -1) (by lia)]

@[simp]

Depends on / 依赖: Cochain, Cochain.leftShift_v, Cochain.rightShift_v, add_zero, descCochain, leftShift_v, mappingCocone, rightShift_v, smul_smul
-/
lemma inr_v_descCochain_v (p q : Int) (hpq : p + 1 = q) (r : Int) (hr : q + m = r) :
    (inr φ).1.v p q hpq ≫ (descCochain φ α β h).v q r hr = β.v p r (by lia) := by
  obtain rfl : p = q + -1 := by lia
  simp [inr, descCochain, mappingCocone, smul_smul,
    Cochain.rightShift_v _ _ _ _ _ _ hpq _ (add_zero (q + -1)),
    Cochain.leftShift_v (n := n) _ _ _ _ _ r _ (q + -1) (by lia)]

@[simp]
/--
lemma `inl_comp_descCochain` / 引理 `inl_comp_descCochain`

English:
lemma inl_comp_descCochain
  proof: by
  cat_disch

@[simp]

中文:
引理 inl_comp_descCochain
  证明: by
  cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma inl_comp_descCochain :
    (inl φ).comp (descCochain φ α β h) (zero_add m) = α := by
  cat_disch

@[simp]
/--
lemma `inr_comp_descCochain` / 引理 `inr_comp_descCochain`

English:
lemma inr_comp_descCochain
  proof: by
  ext p q hpq
  simp [Cochain.comp_v (n₂ := m) _ _ _ _ (p + 1) q rfl (by lia)]

中文:
引理 inr_comp_descCochain
  证明: by
  ext p q hpq
  simp [Cochain.comp_v (n₂ := m) _ _ _ _ (p + 1) q rfl (by lia)]

Depends on / 依赖: Cochain, Cochain.comp_v, comp_v
-/
lemma inr_comp_descCochain :
    (inr φ).1.comp (descCochain φ α β h) (by lia) = β := by
  ext p q hpq
  simp [Cochain.comp_v (n₂ := m) _ _ _ _ (p + 1) q rfl (by lia)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_descCochain` / 引理 `δ_descCochain`

English:
lemma δ_descCochain
  given: (n' : Int) (hn' : n + 1 = n')
  proof: by
  dsimp [descCochain, fst, snd, mappingCocone]
  ext p q hpq
  subst h
  obtain rfl : n' = m + 2 := by lia
  simp [Cochain.δ_leftShift _ (-1) _ (m + 1) _ (m + 2) (by lia),
    mappingCone.δ_descCochain (m := m) (n := m + 1) _ _ _ _ (m + 2) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ p p _ 

中文:
引理 δ_descCochain
  条件: (n' : 整数) (hn' : n + 1 = n')
  证明: by
  dsimp [descCochain, fst, snd, mappingCocone]
  ext p q hpq
  subst h
  obtain rfl : n' = m + 2 := by lia
  simp [Cochain.δ_leftShift _ (-1) _ (m + 1) _ (m + 2) (by lia),
    mappingCone.δ_descCochain (m := m) (n := m + 1) _ _ _ _ (m + 2) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ p p _ 

Depends on / 依赖: Cochain, Cochain.comp_v, Cochain.leftShift_v, add_zero, comp_v, descCochain, leftShift_v, mappingCocone, mappingCone
-/
lemma δ_descCochain (n' : Int) (hn' : n + 1 = n') :
    δ m n (descCochain φ α β h) =
      (Cochain.ofHom (fst φ)).comp
        (δ m n α + m.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (zero_add n) +
      (snd φ).comp (δ n n' β) (by lia) := by
  dsimp [descCochain, fst, snd, mappingCocone]
  ext p q hpq
  subst h
  obtain rfl : n' = m + 2 := by lia
  simp [Cochain.δ_leftShift _ (-1) _ (m + 1) _ (m + 2) (by lia),
    mappingCone.δ_descCochain (m := m) (n := m + 1) _ _ _ _ (m + 2) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ p p _ (p + -1) (by lia),
    Cochain.leftShift_v (n := m + 2) _ (-1) _ _ _ q _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.comp_v (n₁ := 1) _ _ _ (p + -1) p _ (by lia) hpq,
    Cochain.comp_v (n₂ := m + 2) _ _ _ p (p + -1) q rfl (by lia),
    smul_smul, Int.negOnePow_add, Int.negOnePow_even 2 ⟨1, rfl⟩]
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  abel

end

/-- Constructor for cocycles from `mappingCocone`. -/
@[simps]
/--
Definition of `descCocycle` / `descCocycle` 的定义

English:
definition descCocycle
  signature: {M : CochainComplex C Int} {n m : Int}
  body: ⟨descCochain φ α β h, by
    simp [Cocycle.mem_iff _ n h, δ_descCochain _ _ _ h (n + 1) (by lia), hαβ]⟩

中文:
定义 descCocycle
  签名: {M : 上链复形 C 整数} {n m : 整数}
  定义体: ⟨descCochain φ α β h, by
    simp [Cocycle.mem_iff _ n h, δ_descCochain _ _ _ h (n + 1) (by lia), hαβ]⟩

Depends on / 依赖: Cocycle, Cocycle.mem_iff, descCochain, mem_iff
-/
noncomputable def descCocycle {M : CochainComplex C Int} {n m : Int}
    (α : Cochain K M m) (β : Cocycle L M n) (h : m + 1 = n)
    (hαβ : δ m n α + m.negOnePow • (Cochain.ofHom φ).comp β.1 (zero_add n) = 0) :
    Cocycle (mappingCocone φ) M m :=
  ⟨descCochain φ α β h, by
    simp [Cocycle.mem_iff _ n h, δ_descCochain _ _ _ h (n + 1) (by lia), hαβ]⟩

section

variable {M : CochainComplex C Int} (α : Cochain K M 0) (β : Cocycle L M 1)
  (hαβ : δ 0 1 α + (Cochain.ofHom φ).comp β.1 (zero_add 1) = 0)

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: : mappingCocone φ ⟶ M
  body: (descCocycle φ α β (zero_add 1) (by simpa)).homOf

@[simp]

中文:
定义 desc
  签名: : mappingCocone φ ⟶ M
  定义体: (descCocycle φ α β (zero_add 1) (by simpa)).homOf

@[simp]

Depends on / 依赖: descCocycle, zero_add
-/
noncomputable def desc : mappingCocone φ ⟶ M :=
  (descCocycle φ α β (zero_add 1) (by simpa)).homOf

@[simp]
/--
lemma `ofHom_desc` / 引理 `ofHom_desc`

English:
lemma ofHom_desc
  proof: by
  simp [desc]

@[reassoc (attr := simp)]

中文:
引理 ofHom_desc
  证明: by
  simp [desc]

@[reassoc (attr := simp)]

Depends on / 依赖: HomologyMapData, HomologyMapData.id, homologyMap
-/
lemma ofHom_desc :
    Cochain.ofHom (desc φ α β hαβ) = descCochain φ α β.1 (by lia) := by
  simp [desc]

@[reassoc (attr := simp)]
/--
lemma `inl_v_desc_f` / 引理 `inl_v_desc_f`

English:
lemma inl_v_desc_f
  given: (p : Int)
  proof: by
  simp [desc]

@[reassoc (attr := simp)]

中文:
引理 inl_v_desc_f
  条件: (p : 整数)
  证明: by
  simp [desc]

@[reassoc (attr := simp)]
-/
lemma inl_v_desc_f (p : Int) :
    (inl φ).v p p (add_zero p) ≫ (desc φ α β hαβ).f p = α.v p p (add_zero p) := by
  simp [desc]

@[reassoc (attr := simp)]
/--
lemma `inr_v_desc_f` / 引理 `inr_v_desc_f`

English:
lemma inr_v_desc_f
  given: (p q : Int) (hpq : p + 1 = q)
  proof: by
  simp [desc]

中文:
引理 inr_v_desc_f
  条件: (p q : 整数) (hpq : p + 1 = q)
  证明: by
  simp [desc]

Depends on / 依赖: HomologyMapData, HomologyMapData.zero, homologyMap
-/
lemma inr_v_desc_f (p q : Int) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (desc φ α β hαβ).f q = β.1.v p q hpq := by
  simp [desc]

end

section

variable {M : CochainComplex C Int} {n m : Int}
  (α : Cochain M K n) (β : Cochain M L m) (h : m + 1 = n)

/--
Definition of `liftCochain` / `liftCochain` 的定义

English:
definition liftCochain
  signature: : Cochain M (mappingCocone φ) n
  body: (mappingCone.liftCochain φ α β h).rightShift (-1) n (by lia)

中文:
定义 liftCochain
  签名: : Cochain M (mappingCocone φ) n
  定义体: (mappingCone.liftCochain φ α β h).rightShift (-1) n (by lia)

Depends on / 依赖: liftCochain, mappingCone, mappingCone.liftCochain, rightShift
-/
noncomputable def liftCochain : Cochain M (mappingCocone φ) n :=
  (mappingCone.liftCochain φ α β h).rightShift (-1) n (by lia)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `liftCochain_v_fst_f` / 引理 `liftCochain_v_fst_f`

English:
lemma liftCochain_v_fst_f
  given: (p₁ p₂ : Int) (h₁₂ : p₁ + n = p₂)
  proof: by
  simp [liftCochain, mappingCocone, fst,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p₂ _ (p₂ + -1) (by lia)]

中文:
引理 liftCochain_v_fst_f
  条件: (p₁ p₂ : 整数) (h₁₂ : p₁ + n = p₂)
  证明: by
  simp [liftCochain, mappingCocone, fst,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p₂ _ (p₂ + -1) (by lia)]

Depends on / 依赖: Cochain, Cochain.leftShift_v, Cochain.rightShift_v, _comp, leftHomologyMap, leftShift_v, liftCochain, mappingCocone, rightShift_v
-/
lemma liftCochain_v_fst_f (p₁ p₂ : Int) (h₁₂ : p₁ + n = p₂) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ).f p₂ = α.v p₁ p₂ h₁₂ := by
  simp [liftCochain, mappingCocone, fst,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p₂ _ (p₂ + -1) (by lia)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `liftCochain_v_snd_v` / 引理 `liftCochain_v_snd_v`

English:
lemma liftCochain_v_snd_v
  given: (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + -1 = p₃)
  proof: by
  subst h₂₃
  simp [liftCochain, mappingCocone, snd,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ _ (add_zero _),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

@[simp]

中文:
引理 liftCochain_v_snd_v
  条件: (p₁ p₂ p₃ : 整数) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + -1 = p₃)
  证明: by
  subst h₂₃
  simp [liftCochain, mappingCocone, snd,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ _ (add_zero _),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

@[simp]

Depends on / 依赖: Cochain, Cochain.leftShift_v, Cochain.rightShift_v, Int.negOnePow_even, add_zero, leftShift_v, liftCochain, mappingCocone, negOnePow_even, rightShift_v
-/
lemma liftCochain_v_snd_v (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + -1 = p₃) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (snd φ).v p₂ p₃ h₂₃ = β.v p₁ p₃ (by lia) := by
  subst h₂₃
  simp [liftCochain, mappingCocone, snd,
    Cochain.rightShift_v (n := m) _ _ _ _ p₁ _ _ (p₂ + -1) (by lia),
    Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ _ (add_zero _),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

@[simp]
/--
lemma `liftCochain_comp_fst` / 引理 `liftCochain_comp_fst`

English:
lemma liftCochain_comp_fst
  proof: by
  cat_disch

@[simp]

中文:
引理 liftCochain_comp_fst
  证明: by
  cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma liftCochain_comp_fst :
    (liftCochain φ α β h).comp (Cochain.ofHom (fst φ)) (add_zero _) = α := by
  cat_disch

@[simp]
/--
lemma `liftCochain_comp_snd` / 引理 `liftCochain_comp_snd`

English:
lemma liftCochain_comp_snd
  proof: by
  ext p q hpq
  simp [Cochain.comp_v (n₁ := n) (n₂ := -1) (n₁₂ := m) _ _ _ p _ _ (by lia)
    (Int.add_neg_cancel_right q 1)]

中文:
引理 liftCochain_comp_snd
  证明: by
  ext p q hpq
  simp [Cochain.comp_v (n₁ := n) (n₂ := -1) (n₁₂ := m) _ _ _ p _ _ (by lia)
    (Int.add_neg_cancel_right q 1)]

Depends on / 依赖: Cochain, Cochain.comp_v, Int.add_neg_cancel_right, add_neg_cancel_right, comp_v
-/
lemma liftCochain_comp_snd :
    (liftCochain φ α β h).comp (snd φ) (by lia) = β := by
  ext p q hpq
  simp [Cochain.comp_v (n₁ := n) (n₂ := -1) (n₁₂ := m) _ _ _ p _ _ (by lia)
    (Int.add_neg_cancel_right q 1)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_liftCochain` / 引理 `δ_liftCochain`

English:
lemma δ_liftCochain
  given: (n' : Int) (hn' : n + 1 = n')
  proof: by
  dsimp [liftCochain, inl, inr]
  ext p q hpq
  simp [mappingCone.δ_liftCochain _ _ _ _ n' hn',
    Cochain.δ_rightShift _ (-1) _ n' _ n (by lia),
    Cochain.rightShift_v (n := n) _ _ _ _ p _ _ (q + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ (q + -1) rfl,
    Cochain.rightShift_v _ _ _

中文:
引理 δ_liftCochain
  条件: (n' : 整数) (hn' : n + 1 = n')
  证明: by
  dsimp [liftCochain, inl, inr]
  ext p q hpq
  simp [mappingCone.δ_liftCochain _ _ _ _ n' hn',
    Cochain.δ_rightShift _ (-1) _ n' _ n (by lia),
    Cochain.rightShift_v (n := n) _ _ _ _ p _ _ (q + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ (q + -1) rfl,
    Cochain.rightShift_v _ _ _

Depends on / 依赖: Before, Cochain, Cochain.comp_v, Cochain.rightShift_v, adaptation_note, add_zero, comp_v, github, github.com, leanprover, liftCochain, mappingCone, rightShift_v
-/
lemma δ_liftCochain (n' : Int) (hn' : n + 1 = n') :
    δ n n' (liftCochain φ α β h) =
      (δ n n' α).comp (inl φ) (add_zero _) -
        (δ m n β + α.comp (Cochain.ofHom φ) (add_zero n)).comp (inr φ).1 hn' := by
  dsimp [liftCochain, inl, inr]
  ext p q hpq
  simp [mappingCone.δ_liftCochain _ _ _ _ n' hn',
    Cochain.δ_rightShift _ (-1) _ n' _ n (by lia),
    Cochain.rightShift_v (n := n) _ _ _ _ p _ _ (q + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ (q + -1) rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (q + -1)),
    Cochain.comp_v _ _ _ p q _ hpq rfl,
    Cochain.comp_v (n₁ := n) (n₂ := 1) _ _ _ p (q + -1) q (by lia) (by lia)]
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  abel

end

/-- Constructor for cocycles to `mappingCocone`. -/
@[simps]
/--
Definition of `liftCocycle` / `liftCocycle` 的定义

English:
definition liftCocycle
  signature: {M : CochainComplex C Int} {n m : Int}
  body: ⟨liftCochain φ α β h,
    by simp [Cocycle.mem_iff _ _ rfl, δ_liftCochain _ _ _ _ _ rfl, hαβ]⟩

中文:
定义 liftCocycle
  签名: {M : 上链复形 C 整数} {n m : 整数}
  定义体: ⟨liftCochain φ α β h,
    by simp [Cocycle.mem_iff _ _ rfl, δ_liftCochain _ _ _ _ _ rfl, hαβ]⟩

Depends on / 依赖: Cocycle, Cocycle.mem_iff, liftCochain, mem_iff
-/
noncomputable def liftCocycle {M : CochainComplex C Int} {n m : Int}
    (α : Cocycle M K n) (β : Cochain M L m) (h : m + 1 = n)
    (hαβ : δ m n β + α.1.comp (Cochain.ofHom φ) (add_zero n) = 0) :
    Cocycle M (mappingCocone φ) n :=
  ⟨liftCochain φ α β h,
    by simp [Cocycle.mem_iff _ _ rfl, δ_liftCochain _ _ _ _ _ rfl, hαβ]⟩

section

variable {M : CochainComplex C Int} (α : M ⟶ K) (β : Cochain M L (-1))
  (hαβ : δ (-1) 0 β + Cochain.ofHom (α ≫ φ) = 0)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : M ⟶ mappingCocone φ
  body: Cocycle.homOf (liftCocycle φ (Cocycle.ofHom α) β (by simp) (by simpa [← Cochain.ofHom_comp]))

@[simp]

中文:
定义 lift
  签名: : M ⟶ mappingCocone φ
  定义体: Cocycle.homOf (liftCocycle φ (Cocycle.ofHom α) β (by simp) (by simpa [← Cochain.ofHom_comp]))

@[simp]

Depends on / 依赖: Cochain, Cochain.ofHom_comp, Cocycle, Cocycle.homOf, Cocycle.ofHom, liftCocycle, ofHom_comp
-/
noncomputable def lift : M ⟶ mappingCocone φ :=
  Cocycle.homOf (liftCocycle φ (Cocycle.ofHom α) β (by simp) (by simpa [← Cochain.ofHom_comp]))

@[simp]
/--
lemma `ofHom_lift` / 引理 `ofHom_lift`

English:
lemma ofHom_lift
  proof: by
  simp [lift]

@[reassoc (attr := simp)]

中文:
引理 ofHom_lift
  证明: by
  simp [lift]

@[reassoc (attr := simp)]
-/
lemma ofHom_lift :
    Cochain.ofHom (lift φ α β hαβ) = liftCochain φ (Cochain.ofHom α) β (by simp) := by
  simp [lift]

@[reassoc (attr := simp)]
/--
lemma `lift_f_fst_f` / 引理 `lift_f_fst_f`

English:
lemma lift_f_fst_f
  given: (p : Int)
  proof: by
  simp [lift]

@[reassoc (attr := simp)]

中文:
引理 lift_f_fst_f
  条件: (p : 整数)
  证明: by
  simp [lift]

@[reassoc (attr := simp)]
-/
lemma lift_f_fst_f (p : Int) :
    (lift φ α β hαβ).f p ≫ (fst φ).f p = α.f p := by
  simp [lift]

@[reassoc (attr := simp)]
/--
lemma `lift_fst` / 引理 `lift_fst`

English:
lemma lift_fst
  proof: by
  cat_disch

@[reassoc (attr := simp)]

中文:
引理 lift_fst
  证明: by
  cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: LeftHomologyData, RightHomologyData, RightHomologyData.liftH_, cancel_epi, cancel_mono, cat_disch
-/
lemma lift_fst :
    lift φ α β hαβ ≫ fst φ = α := by
  cat_disch

@[reassoc (attr := simp)]
/--
lemma `lift_f_snd_v` / 引理 `lift_f_snd_v`

English:
lemma lift_f_snd_v
  given: (p q : Int) (hpq : p + (-1) = q)
  proof: by
  simp [lift]

中文:
引理 lift_f_snd_v
  条件: (p q : 整数) (hpq : p + (-1) = q)
  证明: by
  simp [lift]
-/
lemma lift_f_snd_v (p q : Int) (hpq : p + (-1) = q) :
    (lift φ α β hαβ).f p ≫ (snd φ).v p q hpq = β.v p q hpq := by
  simp [lift]

end

end

section

variable [HasBinaryBiproducts C]

/-- Given a morphism `φ : K ⟶ L` of cochain complexes, this is the triangle
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`. -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
/--
Definition of `triangle` / `triangle` 的定义

English:
definition triangle
  signature: : Triangle (CochainComplex C Int)
  body: Triangle.mk (fst φ) φ
    ((mappingCone.triangle φ).mor₂ ≫ (shiftFunctorCompIsoId _ (-1 : Int) 1 (by lia)).inv.app _)

中文:
定义 triangle
  签名: : Triangle (上链复形 C 整数)
  定义体: Triangle.mk (fst φ) φ
    ((mappingCone.triangle φ).mor₂ ≫ (shiftFunctorCompIsoId _ (-1 : Int) 1 (by lia)).inv.app _)

Depends on / 依赖: Triangle, Triangle.mk, inv.app, mappingCone, mappingCone.triangle, shiftFunctorCompIsoId, triangle
-/
noncomputable def triangle : Triangle (CochainComplex C Int) :=
  Triangle.mk (fst φ) φ
    ((mappingCone.triangle φ).mor₂ ≫ (shiftFunctorCompIsoId _ (-1 : Int) 1 (by lia)).inv.app _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `rotateTriangleIso` / `rotateTriangleIso` 的定义

English:
definition rotateTriangleIso
  signature: :
  body: by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftFunctorCompIsoId _ (-1 : Int) 1 (by lia)).app _)
    (by simp) (by simp [triangle]) ?_
  dsimp
  ext n
  simp [fst, mappingCone.triangle, Cochain.leftShift_v _ _ _ _ _ _ _ _ rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
    shi

中文:
定义 rotateTriangleIso
  签名: :
  定义体: by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftFunctorCompIsoId _ (-1 : Int) 1 (by lia)).app _)
    (by simp) (by simp [triangle]) ?_
  dsimp
  ext n
  simp [fst, mappingCone.triangle, Cochain.leftShift_v _ _ _ _ _ _ _ _ rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
    shi

Depends on / 依赖: Cochain, Cochain.leftShift_v, Cochain.rightShift_v, Iso.refl, Triangle, Triangle.isoMk, _assoc, _i_assoc, _inv_app_f, cancel_epi, cancel_mono, cyclesMap, leftShift_v, mappingCone, mappingCone.triangle, p_opcyclesMap, rightShift_v, shiftFunctorAdd, shiftFunctorCompIsoId, shiftFunctorZero_hom_app_f
-/
noncomputable def rotateTriangleIso :
    (triangle φ).rotate ≅ mappingCone.triangle φ := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftFunctorCompIsoId _ (-1 : Int) 1 (by lia)).app _)
    (by simp) (by simp [triangle]) ?_
  dsimp
  ext n
  simp [fst, mappingCone.triangle, Cochain.leftShift_v _ _ _ _ _ _ _ _ rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
    shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]

end

end mappingCocone

end CochainComplex
