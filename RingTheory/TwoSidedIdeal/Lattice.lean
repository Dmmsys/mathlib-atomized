/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# The complete lattice structure on two-sided ideals
-/

public section

namespace TwoSidedIdeal

variable (R : Type*) [NonUnitalNonAssocRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (TwoSidedIdeal R)
  body: { ringCon := I.ringCon ⊔ J.ringCon }
  le_sup_left I J := by rw [ringCon_le_iff]; exact le_sup_left
  le_sup_right I J := by rw [ringCon_le_iff]; exact le_sup_right
  sup_le I J K h1 h2 := by rw [ringCon_le_iff] at h1 h2 ⊢; exact sup_le h1 h2

中文:
实例 :
  签名: SemilatticeSup (TwoSidedIdeal R)
  定义体: { ringCon := I.ringCon ⊔ J.ringCon }
  le_sup_left I J := by rw [ringCon_le_iff]; exact le_sup_left
  le_sup_right I J := by rw [ringCon_le_iff]; exact le_sup_right
  sup_le I J K h1 h2 := by rw [ringCon_le_iff] at h1 h2 ⊢; exact sup_le h1 h2

Depends on / 依赖: I.ringCon, J.ringCon, ringCon
-/
instance : SemilatticeSup (TwoSidedIdeal R) where
  sup I J := { ringCon := I.ringCon ⊔ J.ringCon }
  le_sup_left I J := by rw [ringCon_le_iff]; exact le_sup_left
  le_sup_right I J := by rw [ringCon_le_iff]; exact le_sup_right
  sup_le I J K h1 h2 := by rw [ringCon_le_iff] at h1 h2 ⊢; exact sup_le h1 h2

/--
lemma `sup_ringCon` / 引理 `sup_ringCon`

English:
lemma sup_ringCon
  given: (I J : TwoSidedIdeal R)
  statement: (I ⊔ J).ringCon = I.ringCon ⊔ J.ringCon
  proof: rfl

中文:
引理 sup_ringCon
  条件: (I J : TwoSidedIdeal R)
  结论: (I ⊔ J).ringCon = I.ringCon ⊔ J.ringCon
  证明: rfl
-/
lemma sup_ringCon (I J : TwoSidedIdeal R) : (I ⊔ J).ringCon = I.ringCon ⊔ J.ringCon := rfl

section sup

variable {R}

/--
lemma `mem_sup_left` / 引理 `mem_sup_left`

English:
lemma mem_sup_left
  given: {I J : TwoSidedIdeal R} {x : R} (h : x in I)
  proof: (show I <= I ⊔ J from le_sup_left) h

中文:
引理 mem_sup_left
  条件: {I J : TwoSidedIdeal R} {x : R} (h : x in I)
  证明: (show I <= I ⊔ J from le_sup_left) h

Depends on / 依赖: le_sup_left
-/
lemma mem_sup_left {I J : TwoSidedIdeal R} {x : R} (h : x in I) :
    x in I ⊔ J :=
  (show I <= I ⊔ J from le_sup_left) h

/--
lemma `mem_sup_right` / 引理 `mem_sup_right`

English:
lemma mem_sup_right
  given: {I J : TwoSidedIdeal R} {x : R} (h : x in J)
  proof: (show J <= I ⊔ J from le_sup_right) h

中文:
引理 mem_sup_right
  条件: {I J : TwoSidedIdeal R} {x : R} (h : x in J)
  证明: (show J <= I ⊔ J from le_sup_right) h

Depends on / 依赖: le_sup_right
-/
lemma mem_sup_right {I J : TwoSidedIdeal R} {x : R} (h : x in J) :
    x in I ⊔ J :=
  (show J <= I ⊔ J from le_sup_right) h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_sup` / 引理 `mem_sup`

English:
lemma mem_sup
  given: {I J : TwoSidedIdeal R} {x : R}
  proof: by
  constructor
  · let s : TwoSidedIdeal R := .mk'
      {x | exists y in I, exists z in J, y + z = x}
      ⟨0, ⟨zero_mem _, ⟨0, ⟨zero_mem _, zero_add _⟩⟩⟩⟩
      (by rintro _ _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩ ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩;
          exact ⟨x + a, ⟨add_mem _ hx ha, ⟨y + b, ⟨add_mem _ hy hb

中文:
引理 mem_sup
  条件: {I J : TwoSidedIdeal R} {x : R}
  证明: by
  constructor
  · let s : TwoSidedIdeal R := .mk'
      {x | exists y in I, exists z in J, y + z = x}
      ⟨0, ⟨zero_mem _, ⟨0, ⟨zero_mem _, zero_add _⟩⟩⟩⟩
      (by rintro _ _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩ ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩;
          exact ⟨x + a, ⟨add_mem _ hx ha, ⟨y + b, ⟨add_mem _ hy hb

Depends on / 依赖: TwoSidedIdeal, add_mem, mul_a, mul_mem_left, neg_mem, zero_add, zero_mem
-/
lemma mem_sup {I J : TwoSidedIdeal R} {x : R} :
    x in I ⊔ J ↔ exists y in I, exists z in J, y + z = x := by
  constructor
  · let s : TwoSidedIdeal R := .mk'
      {x | exists y in I, exists z in J, y + z = x}
      ⟨0, ⟨zero_mem _, ⟨0, ⟨zero_mem _, zero_add _⟩⟩⟩⟩
      (by rintro _ _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩ ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩;
          exact ⟨x + a, ⟨add_mem _ hx ha, ⟨y + b, ⟨add_mem _ hy hb, by abel⟩⟩⟩⟩)
      (by rintro _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
          exact ⟨-x, ⟨neg_mem _ hx, ⟨-y, ⟨neg_mem _ hy, by abel⟩⟩⟩⟩)
      (by rintro r _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
.symm⟩⟩⟩⟩) exact ⟨_, ⟨mul_mem_left _ _ _ hx, ⟨_, ⟨mul_mem_left _ _ _ hy, mul_add _ _ _
      (by rintro r _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
.symm⟩⟩⟩⟩) exact ⟨_, ⟨mul_mem_right _ _ _ hx, ⟨_, ⟨mul_mem_right _ _ _ hy, add_mul _ _ _
    suffices (I.ringCon ⊔ J.ringCon) <= s.ringCon by
      intro h; convert! this h; rw [rel_iff, sub_zero, mem_mk']; rfl
    refine sup_le (fun x y h => ?_) (fun x y h => ?_) <;> rw [rel_iff] at h ⊢ <;> rw [mem_mk']
    exacts [⟨_, ⟨h, ⟨0, ⟨zero_mem _, add_zero _⟩⟩⟩⟩, ⟨0, ⟨zero_mem _, ⟨_, ⟨h, zero_add _⟩⟩⟩⟩]
  · rintro ⟨y, ⟨hy, ⟨z, ⟨hz, rfl⟩⟩⟩⟩; exact add_mem _ (mem_sup_left hy) (mem_sup_right hz)

end sup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (TwoSidedIdeal R)
  body: { ringCon := I.ringCon ⊓ J.ringCon }
  inf_le_left I J := by rw [ringCon_le_iff]; exact inf_le_left
  inf_le_right I J := by rw [ringCon_le_iff]; exact inf_le_right
  le_inf I J K h1 h2 := by rw [ringCon_le_iff] at h1 h2 ⊢; exact le_inf h1 h2

中文:
实例 :
  签名: SemilatticeInf (TwoSidedIdeal R)
  定义体: { ringCon := I.ringCon ⊓ J.ringCon }
  inf_le_left I J := by rw [ringCon_le_iff]; exact inf_le_left
  inf_le_right I J := by rw [ringCon_le_iff]; exact inf_le_right
  le_inf I J K h1 h2 := by rw [ringCon_le_iff] at h1 h2 ⊢; exact le_inf h1 h2

Depends on / 依赖: I.ringCon, J.ringCon, ringCon
-/
instance : SemilatticeInf (TwoSidedIdeal R) where
  inf I J := { ringCon := I.ringCon ⊓ J.ringCon }
  inf_le_left I J := by rw [ringCon_le_iff]; exact inf_le_left
  inf_le_right I J := by rw [ringCon_le_iff]; exact inf_le_right
  le_inf I J K h1 h2 := by rw [ringCon_le_iff] at h1 h2 ⊢; exact le_inf h1 h2

/--
lemma `inf_ringCon` / 引理 `inf_ringCon`

English:
lemma inf_ringCon
  given: (I J : TwoSidedIdeal R)
  statement: (I ⊓ J).ringCon = I.ringCon ⊓ J.ringCon
  proof: rfl

中文:
引理 inf_ringCon
  条件: (I J : TwoSidedIdeal R)
  结论: (I ⊓ J).ringCon = I.ringCon ⊓ J.ringCon
  证明: rfl
-/
lemma inf_ringCon (I J : TwoSidedIdeal R) : (I ⊓ J).ringCon = I.ringCon ⊓ J.ringCon := rfl

/--
lemma `mem_inf` / 引理 `mem_inf`

English:
lemma mem_inf
  given: {I J : TwoSidedIdeal R} {x : R}
  proof: Iff.rfl

中文:
引理 mem_inf
  条件: {I J : TwoSidedIdeal R} {x : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_inf {I J : TwoSidedIdeal R} {x : R} :
    x in I ⊓ J ↔ x in I ∧ x in J :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (TwoSidedIdeal R)
  body: { ringCon := sSup <| TwoSidedIdeal.ringCon '' s }

中文:
实例 :
  签名: SupSet (TwoSidedIdeal R)
  定义体: { ringCon := sSup <| TwoSidedIdeal.ringCon '' s }

Depends on / 依赖: TwoSidedIdeal, TwoSidedIdeal.ringCon, ringCon
-/
instance : SupSet (TwoSidedIdeal R) where
  sSup s := { ringCon := sSup <| TwoSidedIdeal.ringCon '' s }

/--
lemma `sSup_ringCon` / 引理 `sSup_ringCon`

English:
lemma sSup_ringCon
  given: (S : Set (TwoSidedIdeal R))
  proof: rfl

中文:
引理 sSup_ringCon
  条件: (S : Set (TwoSidedIdeal R))
  证明: rfl
-/
lemma sSup_ringCon (S : Set (TwoSidedIdeal R)) :
    (sSup S).ringCon = sSup (TwoSidedIdeal.ringCon '' S) := rfl

/--
lemma `iSup_ringCon` / 引理 `iSup_ringCon`

English:
lemma iSup_ringCon
  given: {ι : Type*} (I : ι -> TwoSidedIdeal R)
  proof: by
  simp only [iSup, sSup_ringCon]; congr; ext; simp

中文:
引理 iSup_ringCon
  条件: {ι : 类型} (I : ι -> TwoSidedIdeal R)
  证明: by
  simp only [iSup, sSup_ringCon]; congr; ext; simp

Depends on / 依赖: sSup_ringCon
-/
lemma iSup_ringCon {ι : Type*} (I : ι -> TwoSidedIdeal R) :
    (⨆ i, I i).ringCon = ⨆ i, (I i).ringCon := by
  simp only [iSup, sSup_ringCon]; congr; ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeSup (TwoSidedIdeal R)
  body: .of_image ringCon_le_iff.symm (isLUB_sSup _)

中文:
实例 :
  签名: CompleteSemilatticeSup (TwoSidedIdeal R)
  定义体: .of_image ringCon_le_iff.symm (isLUB_sSup _)

Depends on / 依赖: isLUB_sSup, of_image, ringCon_le_iff, ringCon_le_iff.symm
-/
instance : CompleteSemilatticeSup (TwoSidedIdeal R) where
  isLUB_sSup _ := .of_image ringCon_le_iff.symm (isLUB_sSup _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (TwoSidedIdeal R)
  body: { ringCon := sInf <| TwoSidedIdeal.ringCon '' s }

中文:
实例 :
  签名: InfSet (TwoSidedIdeal R)
  定义体: { ringCon := sInf <| TwoSidedIdeal.ringCon '' s }

Depends on / 依赖: TwoSidedIdeal, TwoSidedIdeal.ringCon, ringCon
-/
instance : InfSet (TwoSidedIdeal R) where
  sInf s := { ringCon := sInf <| TwoSidedIdeal.ringCon '' s }

/--
lemma `sInf_ringCon` / 引理 `sInf_ringCon`

English:
lemma sInf_ringCon
  given: (S : Set (TwoSidedIdeal R))
  proof: rfl

中文:
引理 sInf_ringCon
  条件: (S : Set (TwoSidedIdeal R))
  证明: rfl
-/
lemma sInf_ringCon (S : Set (TwoSidedIdeal R)) :
    (sInf S).ringCon = sInf (TwoSidedIdeal.ringCon '' S) := rfl

/--
lemma `iInf_ringCon` / 引理 `iInf_ringCon`

English:
lemma iInf_ringCon
  given: {ι : Type*} (I : ι -> TwoSidedIdeal R)
  proof: by
  simp only [iInf, sInf_ringCon]; congr!; ext; simp

中文:
引理 iInf_ringCon
  条件: {ι : 类型} (I : ι -> TwoSidedIdeal R)
  证明: by
  simp only [iInf, sInf_ringCon]; congr!; ext; simp

Depends on / 依赖: sInf_ringCon
-/
lemma iInf_ringCon {ι : Type*} (I : ι -> TwoSidedIdeal R) :
    (⨅ i, I i).ringCon = ⨅ i, (I i).ringCon := by
  simp only [iInf, sInf_ringCon]; congr!; ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeInf (TwoSidedIdeal R)
  body: .of_image ringCon_le_iff.symm (isGLB_sInf _)

中文:
实例 :
  签名: CompleteSemilatticeInf (TwoSidedIdeal R)
  定义体: .of_image ringCon_le_iff.symm (isGLB_sInf _)

Depends on / 依赖: isGLB_sInf, of_image, ringCon_le_iff, ringCon_le_iff.symm
-/
instance : CompleteSemilatticeInf (TwoSidedIdeal R) where
  isGLB_sInf _ := .of_image ringCon_le_iff.symm (isGLB_sInf _)

/--
lemma `mem_iInf` / 引理 `mem_iInf`

English:
lemma mem_iInf
  given: {ι : Type*} {I : ι -> TwoSidedIdeal R} {x : R}
  proof: show (forall _, _) ↔ _ by simp [mem_iff]

中文:
引理 mem_iInf
  条件: {ι : 类型} {I : ι -> TwoSidedIdeal R} {x : R}
  证明: show (forall _, _) ↔ _ by simp [mem_iff]

Depends on / 依赖: mem_iff
-/
lemma mem_iInf {ι : Type*} {I : ι -> TwoSidedIdeal R} {x : R} :
    x in iInf I ↔ forall i, x in I i :=
  show (forall _, _) ↔ _ by simp [mem_iff]

/--
lemma `mem_sInf` / 引理 `mem_sInf`

English:
lemma mem_sInf
  given: {S : Set (TwoSidedIdeal R)} {x : R}
  proof: show (forall _, _) ↔ _ by simp [mem_iff]

中文:
引理 mem_sInf
  条件: {S : Set (TwoSidedIdeal R)} {x : R}
  证明: show (forall _, _) ↔ _ by simp [mem_iff]

Depends on / 依赖: mem_iff
-/
lemma mem_sInf {S : Set (TwoSidedIdeal R)} {x : R} :
    x in sInf S ↔ forall I in S, x in I :=
  show (forall _, _) ↔ _ by simp [mem_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (TwoSidedIdeal R)
  body: { ringCon := ⊤ }

中文:
实例 :
  签名: Top (TwoSidedIdeal R)
  定义体: { ringCon := ⊤ }

Depends on / 依赖: ringCon
-/
instance : Top (TwoSidedIdeal R) where
  top := { ringCon := ⊤ }

/--
lemma `top_ringCon` / 引理 `top_ringCon`

English:
lemma top_ringCon
  statement: (⊤ : TwoSidedIdeal R).ringCon = ⊤
  proof: rfl

@[simp]

中文:
引理 top_ringCon
  结论: (⊤ : TwoSidedIdeal R).ringCon = ⊤
  证明: rfl

@[simp]
-/
lemma top_ringCon : (⊤ : TwoSidedIdeal R).ringCon = ⊤ := rfl

@[simp]
/--
lemma `mem_top` / 引理 `mem_top`

English:
lemma mem_top
  given: {x : R}
  statement: x in (⊤ : TwoSidedIdeal R)
  proof: trivial

中文:
引理 mem_top
  条件: {x : R}
  结论: x in (⊤ : TwoSidedIdeal R)
  证明: trivial
-/
lemma mem_top {x : R} : x in (⊤ : TwoSidedIdeal R) := trivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (TwoSidedIdeal R)
  body: { ringCon := ⊥ }

中文:
实例 :
  签名: Bot (TwoSidedIdeal R)
  定义体: { ringCon := ⊥ }

Depends on / 依赖: ringCon
-/
instance : Bot (TwoSidedIdeal R) where
  bot := { ringCon := ⊥ }

/--
lemma `bot_ringCon` / 引理 `bot_ringCon`

English:
lemma bot_ringCon
  statement: (⊥ : TwoSidedIdeal R).ringCon = ⊥
  proof: rfl

@[simp]

中文:
引理 bot_ringCon
  结论: (⊥ : TwoSidedIdeal R).ringCon = ⊥
  证明: rfl

@[simp]
-/
lemma bot_ringCon : (⊥ : TwoSidedIdeal R).ringCon = ⊥ := rfl

@[simp]
/--
lemma `mem_bot` / 引理 `mem_bot`

English:
lemma mem_bot
  given: {x : R}
  statement: x in (⊥ : TwoSidedIdeal R) ↔ x = 0
  proof: Iff.rfl

中文:
引理 mem_bot
  条件: {x : R}
  结论: x in (⊥ : TwoSidedIdeal R) ↔ x = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_bot {x : R} : x in (⊥ : TwoSidedIdeal R) ↔ x = 0 :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (TwoSidedIdeal R)
  body: (inferInstance : SemilatticeSup (TwoSidedIdeal R))
  __ := (inferInstance : SemilatticeInf (TwoSidedIdeal R))
  __ := (inferInstance : CompleteSemilatticeSup (TwoSidedIdeal R))
  __ := (inferInstance : CompleteSemilatticeInf (TwoSidedIdeal R))
  le_top _ := by rw [ringCon_le_iff]; exact le_top
  bot

中文:
实例 :
  签名: CompleteLattice (TwoSidedIdeal R)
  定义体: (inferInstance : SemilatticeSup (TwoSidedIdeal R))
  __ := (inferInstance : SemilatticeInf (TwoSidedIdeal R))
  __ := (inferInstance : CompleteSemilatticeSup (TwoSidedIdeal R))
  __ := (inferInstance : CompleteSemilatticeInf (TwoSidedIdeal R))
  le_top _ := by rw [ringCon_le_iff]; exact le_top
  bot

Depends on / 依赖: SemilatticeSup, TwoSidedIdeal
-/
instance : CompleteLattice (TwoSidedIdeal R) where
  __ := (inferInstance : SemilatticeSup (TwoSidedIdeal R))
  __ := (inferInstance : SemilatticeInf (TwoSidedIdeal R))
  __ := (inferInstance : CompleteSemilatticeSup (TwoSidedIdeal R))
  __ := (inferInstance : CompleteSemilatticeInf (TwoSidedIdeal R))
  le_top _ := by rw [ringCon_le_iff]; exact le_top
  bot_le _ := by rw [ringCon_le_iff]; exact bot_le

@[simp]
/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: ((⊥ : TwoSidedIdeal R) : Set R) = {0}
  proof: rfl

@[simp]

中文:
引理 coe_bot
  结论: ((⊥ : TwoSidedIdeal R) : Set R) = {0}
  证明: rfl

@[simp]
-/
lemma coe_bot : ((⊥ : TwoSidedIdeal R) : Set R) = {0} := rfl

@[simp]
/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: ((⊤ : TwoSidedIdeal R) : Set R) = Set.univ
  proof: rfl

中文:
引理 coe_top
  结论: ((⊤ : TwoSidedIdeal R) : Set R) = Set.univ
  证明: rfl
-/
lemma coe_top : ((⊤ : TwoSidedIdeal R) : Set R) = Set.univ := rfl

/--
lemma `one_mem_iff` / 引理 `one_mem_iff`

English:
lemma one_mem_iff
  given: {R : Type*} [NonAssocRing R] (I : TwoSidedIdeal R)
  proof: ⟨fun h => eq_top_iff.2 fun x _ => by simpa using I.mul_mem_left x _ h, fun h => h.symm ▸ trivial⟩

alias ⟨eq_top, one_mem⟩ := one_mem_iff

中文:
引理 one_mem_iff
  条件: {R : 类型} [NonAssocRing R] (I : TwoSidedIdeal R)
  证明: ⟨fun h => eq_top_iff.2 fun x _ => by simpa using I.mul_mem_left x _ h, fun h => h.symm ▸ trivial⟩

alias ⟨eq_top, one_mem⟩ := one_mem_iff

Depends on / 依赖: I.mul_mem_left, eq_top_iff, h.symm, mul_mem_left
-/
lemma one_mem_iff {R : Type*} [NonAssocRing R] (I : TwoSidedIdeal R) :
    (1 : R) in I ↔ I = ⊤ :=
  ⟨fun h => eq_top_iff.2 fun x _ => by simpa using I.mul_mem_left x _ h, fun h => h.symm ▸ trivial⟩

alias ⟨eq_top, one_mem⟩ := one_mem_iff

end TwoSidedIdeal
