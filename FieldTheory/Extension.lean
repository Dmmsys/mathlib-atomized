/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Junyan Xu
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Extension of field embeddings

`IntermediateField.exists_algHom_of_adjoin_splits'` is the main result: if E/L/F is a tower of
field extensions, K is another extension of F, and `f` is an embedding of L/F into K/F, such
that the minimal polynomials of a set of generators of E/L splits in K (via `f`), then `f`
extends to an embedding of E/F into K/F.

## Reference

[Isaacs1980] *Roots of Polynomials in Algebraic Extensions of Fields*,
The American Mathematical Monthly

-/

@[expose] public section

open Polynomial

namespace IntermediateField

variable (F E K : Type*) [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] {S : Set E}

/--
Definition of `Lifts` / `Lifts` 的定义

English:
structure Lifts
  parameters: where
  axioms and operations (2):
    - carrier : IntermediateField F E
    - emb : carrier ->ₐ[F] K

中文:
结构 Lifts
  参数: where
  公理与运算 (2 个):
    - carrier : 中间域 F E
    - emb : carrier ->ₐ[F] K
-/
structure Lifts where
  /-- The domain of a lift. -/
  carrier : IntermediateField F E
  /-- The lifted RingHom, expressed as an AlgHom. -/
  emb : carrier ->ₐ[F] K

variable {F E K}

namespace Lifts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Lifts F E K)
  body: exists h : L₁.carrier <= L₂.carrier, forall x, L₂.emb (inclusion h x) = L₁.emb x
  le_refl L := ⟨le_rfl, by simp⟩
  le_trans L₁ L₂ L₃ := by
    rintro ⟨h₁₂, h₁₂'⟩ ⟨h₂₃, h₂₃'⟩
    refine ⟨h₁₂.trans h₂₃, fun _ => ?_⟩
    rw [← inclusion_inclusion h₁₂ h₂₃]; rw [h₂₃']; rw [h₁₂']
  le_antisymm := by
    rintro ⟨L₁, e₁⟩ ⟨L₂, e₂⟩ ⟨h₁₂, h₁₂'⟩ ⟨h₂₁, h₂₁'⟩
    obtain rfl : L₁ = L₂ := h₁₂.antisymm h₂₁
    congr
    exact AlgHom.ext h₂₁'

中文:
实例 :
  签名: 偏序 (Lifts F E K)
  定义体: exists h : L₁.carrier <= L₂.carrier, forall x, L₂.emb (inclusion h x) = L₁.emb x
  le_refl L := ⟨le_rfl, by simp⟩
  le_trans L₁ L₂ L₃ := by
    rintro ⟨h₁₂, h₁₂'⟩ ⟨h₂₃, h₂₃'⟩
    refine ⟨h₁₂.trans h₂₃, fun _ => ?_⟩
    rw [← inclusion_inclusion h₁₂ h₂₃]; rw [h₂₃']; rw [h₁₂']
  le_antisymm := by
    rintro ⟨L₁, e₁⟩ ⟨L₂, e₂⟩ ⟨h₁₂, h₁₂'⟩ ⟨h₂₁, h₂₁'⟩
    obtain rfl : L₁ = L₂ := h₁₂.antisymm h₂₁
    congr
    exact AlgHom.ext h₂₁'

Depends on / 依赖: carrier, inclusion
-/
instance : PartialOrder (Lifts F E K) where
  le L₁ L₂ := exists h : L₁.carrier <= L₂.carrier, forall x, L₂.emb (inclusion h x) = L₁.emb x
  le_refl L := ⟨le_rfl, by simp⟩
  le_trans L₁ L₂ L₃ := by
    rintro ⟨h₁₂, h₁₂'⟩ ⟨h₂₃, h₂₃'⟩
    refine ⟨h₁₂.trans h₂₃, fun _ => ?_⟩
    rw [← inclusion_inclusion h₁₂ h₂₃]; rw [h₂₃']; rw [h₁₂']
  le_antisymm := by
    rintro ⟨L₁, e₁⟩ ⟨L₂, e₂⟩ ⟨h₁₂, h₁₂'⟩ ⟨h₂₁, h₂₁'⟩
    obtain rfl : L₁ = L₂ := h₁₂.antisymm h₂₁
    congr
    exact AlgHom.ext h₂₁'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (Lifts F E K)
  body: ⟨⊥, (Algebra.ofId F K).comp (botEquiv F E)⟩
  bot_le L := ⟨bot_le, fun x => by
    obtain ⟨x, rfl⟩ := (botEquiv F E).symm.surjective x
    simp_rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact L.emb.commutes x⟩

中文:
实例 :
  签名: 有底序 (Lifts F E K)
  定义体: ⟨⊥, (Algebra.ofId F K).comp (botEquiv F E)⟩
  bot_le L := ⟨bot_le, fun x => by
    obtain ⟨x, rfl⟩ := (botEquiv F E).symm.surjective x
    simp_rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact L.emb.commutes x⟩

Depends on / 依赖: Algebra, Algebra.ofId, botEquiv
-/
noncomputable instance : OrderBot (Lifts F E K) where
  bot := ⟨⊥, (Algebra.ofId F K).comp (botEquiv F E)⟩
  bot_le L := ⟨bot_le, fun x => by
    obtain ⟨x, rfl⟩ := (botEquiv F E).symm.surjective x
    simp_rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact L.emb.commutes x⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Lifts F E K)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (Lifts F E K)
  定义体: ⟨⊥⟩
-/
noncomputable instance : Inhabited (Lifts F E K) :=
  ⟨⊥⟩

variable {L₁ L₂ : Lifts F E K}

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  statement: L₁ <= L₂ ↔
  proof: by
  simp_rw [AlgHom.ext_iff]; rfl

中文:
定理 le_iff
  结论: L₁ <= L₂ ↔
  证明: by
  simp_rw [AlgHom.ext_iff]; rfl

Depends on / 依赖: AlgHom, AlgHom.ext_iff, ext_iff, simp_rw
-/
theorem le_iff : L₁ <= L₂ ↔
    exists h : L₁.carrier <= L₂.carrier, L₂.emb.comp (inclusion h) = L₁.emb := by
  simp_rw [AlgHom.ext_iff]; rfl

/--
theorem `eq_iff_le_carrier_eq` / 定理 `eq_iff_le_carrier_eq`

English:
theorem eq_iff_le_carrier_eq
  statement: L₁ = L₂ ↔ L₁ <= L₂ ∧ L₁.carrier = L₂.carrier
  proof: ⟨fun eq => ⟨eq.le, congr_arg _ eq⟩, fun ⟨le, eq⟩ => le.antisymm ⟨eq.ge, fun x => (le.2 ⟨x, _⟩).symm⟩⟩

中文:
定理 eq_iff_le_carrier_eq
  结论: L₁ = L₂ ↔ L₁ <= L₂ ∧ L₁.carrier = L₂.carrier
  证明: ⟨fun eq => ⟨eq.le, congr_arg _ eq⟩, fun ⟨le, eq⟩ => le.antisymm ⟨eq.ge, fun x => (le.2 ⟨x, _⟩).symm⟩⟩

Depends on / 依赖: antisymm, congr_arg, eq.ge, eq.le, le.antisymm
-/
theorem eq_iff_le_carrier_eq : L₁ = L₂ ↔ L₁ <= L₂ ∧ L₁.carrier = L₂.carrier :=
  ⟨fun eq => ⟨eq.le, congr_arg _ eq⟩, fun ⟨le, eq⟩ => le.antisymm ⟨eq.ge, fun x => (le.2 ⟨x, _⟩).symm⟩⟩

/--
theorem `eq_iff` / 定理 `eq_iff`

English:
theorem eq_iff
  statement: L₁ = L₂ ↔
  proof: by
  rw [eq_iff_le_carrier_eq]; rw [le_iff]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩⟩

中文:
定理 eq_iff
  结论: L₁ = L₂ ↔
  证明: by
  rw [eq_iff_le_carrier_eq]; rw [le_iff]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩⟩

Depends on / 依赖: eq_iff_le_carrier_eq, le_iff
-/
theorem eq_iff : L₁ = L₂ ↔
    exists h : L₁.carrier = L₂.carrier, L₂.emb.comp (inclusion h.le) = L₁.emb := by
  rw [eq_iff_le_carrier_eq]; rw [le_iff]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩⟩

/--
theorem `lt_iff_le_carrier_ne` / 定理 `lt_iff_le_carrier_ne`

English:
theorem lt_iff_le_carrier_ne
  statement: L₁ < L₂ ↔ L₁ <= L₂ ∧ L₁.carrier != L₂.carrier
  proof: by
  rw [lt_iff_le_and_ne]; rw [and_congr_right]; intro h; simp_rw [Ne, eq_iff_le_carrier_eq, h, true_and]

中文:
定理 lt_iff_le_carrier_ne
  结论: L₁ < L₂ ↔ L₁ <= L₂ ∧ L₁.carrier != L₂.carrier
  证明: by
  rw [lt_iff_le_and_ne]; rw [and_congr_right]; intro h; simp_rw [Ne, eq_iff_le_carrier_eq, h, true_and]

Depends on / 依赖: and_congr_right, eq_iff_le_carrier_eq, lt_iff_le_and_ne, simp_rw, true_and
-/
theorem lt_iff_le_carrier_ne : L₁ < L₂ ↔ L₁ <= L₂ ∧ L₁.carrier != L₂.carrier := by
  rw [lt_iff_le_and_ne]; rw [and_congr_right]; intro h; simp_rw [Ne, eq_iff_le_carrier_eq, h, true_and]

/--
theorem `lt_iff` / 定理 `lt_iff`

English:
theorem lt_iff
  statement: L₁ < L₂ ↔
  proof: by
  rw [lt_iff_le_carrier_ne]; rw [le_iff]
  exact ⟨fun h => ⟨h.1.1.lt_of_ne h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1.ne⟩⟩

中文:
定理 lt_iff
  结论: L₁ < L₂ ↔
  证明: by
  rw [lt_iff_le_carrier_ne]; rw [le_iff]
  exact ⟨fun h => ⟨h.1.1.lt_of_ne h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1.ne⟩⟩

Depends on / 依赖: le_iff, lt_iff_le_carrier_ne, lt_of_ne
-/
theorem lt_iff : L₁ < L₂ ↔
    exists h : L₁.carrier < L₂.carrier, L₂.emb.comp (inclusion h.le) = L₁.emb := by
  rw [lt_iff_le_carrier_ne]; rw [le_iff]
  exact ⟨fun h => ⟨h.1.1.lt_of_ne h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1.ne⟩⟩

/--
theorem `le_of_carrier_le_iSup` / 定理 `le_of_carrier_le_iSup`

English:
theorem le_of_carrier_le_iSup
  statement: {ι} {ρ : ι -> Lifts F E K} {σ τ : Lifts F E K}
  proof: le_iff.mpr ⟨carrier_le.trans (iSup_le fun i => (hτ i).1), algHom_ext_of_eq_adjoin _
      (carrier_le.antisymm (iSup_le fun i => (hσ i).1)|>.trans <| iSup_eq_adjoin _ _) fun x hx =>
    have ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    ((hτ i).2 ⟨x, hx⟩).trans ((hσ i).2 ⟨x, hx⟩).symm⟩

中文:
定理 le_of_carrier_le_iSup
  结论: {ι} {ρ : ι -> Lifts F E K} {σ τ : Lifts F E K}
  证明: le_iff.mpr ⟨carrier_le.trans (iSup_le fun i => (hτ i).1), algHom_ext_of_eq_adjoin _
      (carrier_le.antisymm (iSup_le fun i => (hσ i).1)|>.trans <| iSup_eq_adjoin _ _) fun x hx =>
    have ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    ((hτ i).2 ⟨x, hx⟩).trans ((hσ i).2 ⟨x, hx⟩).symm⟩

Depends on / 依赖: Set.mem_iUnion.mp, algHom_ext_of_eq_adjoin, antisymm, carrier_le, carrier_le.antisymm, carrier_le.trans, iSup_eq_adjoin, iSup_le, le_iff, le_iff.mpr, mem_iUnion
-/
theorem le_of_carrier_le_iSup {ι} {ρ : ι -> Lifts F E K} {σ τ : Lifts F E K}
    (hσ : forall i, ρ i <= σ) (hτ : forall i, ρ i <= τ) (carrier_le : σ.carrier <= ⨆ i, (ρ i).carrier) :
    σ <= τ :=
  le_iff.mpr ⟨carrier_le.trans (iSup_le fun i => (hτ i).1), algHom_ext_of_eq_adjoin _
      (carrier_le.antisymm (iSup_le fun i => (hσ i).1)|>.trans <| iSup_eq_adjoin _ _) fun x hx =>
    have ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    ((hτ i).2 ⟨x, hx⟩).trans ((hσ i).2 ⟨x, hx⟩).symm⟩

/--
Definition of `IsExtendible` / `IsExtendible` 的定义

English:
definition IsExtendible
  signature: (σ : Lifts F E K)
  body: forall S : Finset E, exists τ >= σ, (S : Set E) subseteq τ.carrier

中文:
定义 IsExtendible
  签名: (σ : Lifts F E K)
  定义体: forall S : Finset E, exists τ >= σ, (S : Set E) subseteq τ.carrier

Depends on / 依赖: Finset, carrier, subseteq
-/
def IsExtendible (σ : Lifts F E K) : Prop :=
  forall S : Finset E, exists τ >= σ, (S : Set E) subseteq τ.carrier

section Chain
variable (c : Set (Lifts F E K)) (hc : IsChain (· <= ·) c)

/--
Definition of `union` / `union` 的定义

English:
definition union
  signature: : Lifts F E K
  body: let t (i : ↑(insert ⊥ c)) := i.val.carrier
  have hc := hc.insert fun _ _ _ => .inl bot_le
  have dir : Directed (· <= ·) t := hc.directedOn.directed_val.mono_comp _ fun _ _ h => h.1
  ⟨iSup t, (Subalgebra.iSupLift (toSubalgebra <| t ·) dir (·.val.emb) (fun i j h =>
    AlgHom.ext fun x => (hc.total i.2 j.2).elim (fun hij => (hij.snd x).symm) fun hji => by
      rw [AlgHom.comp_apply]; rw [← inclusion]
      dsimp only [coe_type_toSubalgebra]
      rw [← hji.snd (inclusion h x)]; rw [inclusion_inclusion]; rw [inclusion_self]; rw [AlgHom.id_apply x])
    _ le_rfl).comp
      (Subalgebra.equivOfEq _ _ <| toSubalgebra_iSup_of_directed dir)⟩

中文:
定义 union
  签名: : Lifts F E K
  定义体: let t (i : ↑(insert ⊥ c)) := i.val.carrier
  have hc := hc.insert fun _ _ _ => .inl bot_le
  have dir : Directed (· <= ·) t := hc.directedOn.directed_val.mono_comp _ fun _ _ h => h.1
  ⟨iSup t, (Subalgebra.iSupLift (toSubalgebra <| t ·) dir (·.val.emb) (fun i j h =>
    AlgHom.ext fun x => (hc.total i.2 j.2).elim (fun hij => (hij.snd x).symm) fun hji => by
      rw [AlgHom.comp_apply]; rw [← inclusion]
      dsimp only [coe_type_toSubalgebra]
      rw [← hji.snd (inclusion h x)]; rw [inclusion_inclusion]; rw [inclusion_self]; rw [AlgHom.id_apply x])
    _ le_rfl).comp
      (Subalgebra.equivOfEq _ _ <| toSubalgebra_iSup_of_directed dir)⟩

Depends on / 依赖: AlgHom, AlgHom.comp_apply, AlgHom.ext, Directed, Subalgebra, Subalgebra.iSupLift, bot_le, carrier, coe_type_toSubalgebra, comp_apply, directedOn, directed_val, hc.directedOn.directed_val.mono_comp, hc.insert, hc.total, hij.snd, hji.snd, i.val.carrier, iSupLift, inclusion
-/
noncomputable def union : Lifts F E K :=
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  have hc := hc.insert fun _ _ _ => .inl bot_le
  have dir : Directed (· <= ·) t := hc.directedOn.directed_val.mono_comp _ fun _ _ h => h.1
  ⟨iSup t, (Subalgebra.iSupLift (toSubalgebra <| t ·) dir (·.val.emb) (fun i j h =>
    AlgHom.ext fun x => (hc.total i.2 j.2).elim (fun hij => (hij.snd x).symm) fun hji => by
      rw [AlgHom.comp_apply]; rw [← inclusion]
      dsimp only [coe_type_toSubalgebra]
      rw [← hji.snd (inclusion h x)]; rw [inclusion_inclusion]; rw [inclusion_self]; rw [AlgHom.id_apply x])
    _ le_rfl).comp
      (Subalgebra.equivOfEq _ _ <| toSubalgebra_iSup_of_directed dir)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `le_union` / 定理 `le_union`

English:
theorem le_union
  given: ⦃σ
  statement: Lifts F E K⦄ (hσ : σ in c) : σ <= union c hc
  proof: have hσ := Set.mem_insert_of_mem ⊥ hσ
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  ⟨le_iSup t ⟨σ, hσ⟩, fun x => by
    dsimp only [union, AlgHom.comp_apply]
    exact Subalgebra.iSupLift_inclusion (K := (toSubalgebra <| t ·))
      (i := ⟨σ, hσ⟩) x (le_iSup (toSubalgebra <| t ·) ⟨σ, hσ⟩)⟩

中文:
定理 le_union
  条件: ⦃σ
  结论: Lifts F E K⦄ (hσ : σ in c) : σ <= union c hc
  证明: have hσ := Set.mem_insert_of_mem ⊥ hσ
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  ⟨le_iSup t ⟨σ, hσ⟩, fun x => by
    dsimp only [union, AlgHom.comp_apply]
    exact Subalgebra.iSupLift_inclusion (K := (toSubalgebra <| t ·))
      (i := ⟨σ, hσ⟩) x (le_iSup (toSubalgebra <| t ·) ⟨σ, hσ⟩)⟩

Depends on / 依赖: AlgHom, AlgHom.comp_apply, Set.mem_insert_of_mem, Subalgebra, Subalgebra.iSupLift_inclusion, carrier, comp_apply, i.val.carrier, iSupLift_inclusion, insert, le_iSup, mem_insert_of_mem, toSubalgebra
-/
theorem le_union ⦃σ : Lifts F E K⦄ (hσ : σ in c) : σ <= union c hc :=
  have hσ := Set.mem_insert_of_mem ⊥ hσ
  let t (i : ↑(insert ⊥ c)) := i.val.carrier
  ⟨le_iSup t ⟨σ, hσ⟩, fun x => by
    dsimp only [union, AlgHom.comp_apply]
    exact Subalgebra.iSupLift_inclusion (K := (toSubalgebra <| t ·))
      (i := ⟨σ, hσ⟩) x (le_iSup (toSubalgebra <| t ·) ⟨σ, hσ⟩)⟩

/--
theorem `carrier_union` / 定理 `carrier_union`

English:
theorem carrier_union
  statement: (union c hc).carrier = ⨆ i : c, i.1.carrier
  proof: le_antisymm (iSup_le <| by rintro ⟨i, rfl | hi⟩; exacts [bot_le, le_iSup_of_le ⟨i, hi⟩ le_rfl])
    iSup_le fun i => le_iSup_of_le ⟨i, .inr i.2⟩ le_rfl

中文:
定理 carrier_union
  结论: (union c hc).carrier = ⨆ i : c, i.1.carrier
  证明: le_antisymm (iSup_le <| by rintro ⟨i, rfl | hi⟩; exacts [bot_le, le_iSup_of_le ⟨i, hi⟩ le_rfl])
    iSup_le fun i => le_iSup_of_le ⟨i, .inr i.2⟩ le_rfl

Depends on / 依赖: bot_le, exacts, iSup_le, le_antisymm, le_iSup_of_le, le_rfl
-/
theorem carrier_union : (union c hc).carrier = ⨆ i : c, i.1.carrier :=
le_antisymm (iSup_le <| by rintro ⟨i, rfl | hi⟩; exacts [bot_le, le_iSup_of_le ⟨i, hi⟩ le_rfl])
    iSup_le fun i => le_iSup_of_le ⟨i, .inr i.2⟩ le_rfl

/--
theorem `exists_upper_bound` / 定理 `exists_upper_bound`

English:
theorem exists_upper_bound
  given: (c : Set (Lifts F E K)) (hc : IsChain (· <= ·) c)
  proof: ⟨_, le_union c hc⟩

中文:
定理 存在_upper_bound
  条件: (c : 集合 (Lifts F E K)) (hc : IsChain (· <= ·) c)
  证明: ⟨_, le_union c hc⟩

Depends on / 依赖: le_union
-/
theorem exists_upper_bound (c : Set (Lifts F E K)) (hc : IsChain (· <= ·) c) :
    exists ub, forall a in c, a <= ub := ⟨_, le_union c hc⟩

/--
theorem `union_isExtendible` / 定理 `union_isExtendible`

English:
theorem union_isExtendible
  statement: [alg : Algebra.IsAlgebraic F E]
  proof: fun S => by
  let Ω := adjoin F (S : Set E) ->ₐ[F] K
  have ⟨ω, hω⟩ : exists ω : Ω, forall π : c, exists θ >= π.1, ⟨_, ω⟩ <= θ ∧ θ.carrier = π.1.1 ⊔ adjoin F S := by
    by_contra!; choose π hπ using this
    have := finiteDimensional_adjoin (S := (S : Set E)) fun _ _ => (alg.isIntegral).1 _
    have ⟨π₀, hπ₀⟩ := hc.directed.finite_le π
    have ⟨θ, hθπ, hθ⟩ := hext _ π₀.2 S
    rw [← adjoin_le_iff] at hθ
    let θ₀ := θ.emb.comp (inclusion hθ)
    have := (hπ₀ θ₀).trans hθπ
exact hπ θ₀ ⟨_, θ.emb.comp inclusion sup_le this.1 hθ⟩
      ⟨le_sup_left, this.2⟩ ⟨le_sup_right, fun _ => rfl⟩ rfl
  choose θ ge hθ eq using hω
  have : IsChain (· <= ·) (Set.range θ) := by
    simp_rw [← restrictScalars_adjoin_eq_sup, restrictScalars_adjoin] at eq
    rintro _ ⟨π₁, rfl⟩ _ ⟨π₂, rfl⟩ -
    wlog h : π₁ <= π₂ generalizing π₁ π₂
    · exact (this _ _ <| (hc.total π₁.2 π₂.2).resolve_left h).symm
    refine .inl (le_iff.mpr ⟨?_, algHom_ext_of_eq_adjoin _ (eq _) ?_⟩)
    · rw [eq, eq]; exact adjoin.mono _ _ _ (Set.union_subset_union_left _ h.1)
    rintro x (hx | hx)
    · change (θ π₂).emb (inclusion (ge π₂).1 <| inclusion h.1 ⟨x, hx⟩) =
        (θ π₁).emb (inclusion (ge π₁).1 ⟨x, hx⟩)
      rw [(ge π₁).2]; rw [(ge π₂).2]; rw [h.2]
    · change (θ π₂).emb (inclusion (hθ π₂).1 ⟨x, subset_adjoin _ _ hx⟩) =
        (θ π₁).emb (inclusion (hθ π₁).1 ⟨x, subset_adjoin _ _ hx⟩)
      rw [(hθ π₁).2]; rw [(hθ π₂).2]
  refine ⟨union _ this, le_of_carrier_le_iSup (fun π => le_union c hc π.2)
    (fun π => (ge π).trans <| le_union _ _ ⟨_, rfl⟩) (carrier_union _ _).le, ?_⟩
  simp_rw [carrier_union, iSup_range', eq]
  exact (subset_adjoin _ _).trans (SetLike.coe_subset_coe.mpr <|
le_sup_right.trans le_iSup_of_le (Classical.arbitrary _) le_rfl)

中文:
定理 union_isExtendible
  结论: [alg : 代数.是代数 F E]
  证明: fun S => by
  let Ω := adjoin F (S : Set E) ->ₐ[F] K
  have ⟨ω, hω⟩ : exists ω : Ω, forall π : c, exists θ >= π.1, ⟨_, ω⟩ <= θ ∧ θ.carrier = π.1.1 ⊔ adjoin F S := by
    by_contra!; choose π hπ using this
    have := finiteDimensional_adjoin (S := (S : Set E)) fun _ _ => (alg.isIntegral).1 _
    have ⟨π₀, hπ₀⟩ := hc.directed.finite_le π
    have ⟨θ, hθπ, hθ⟩ := hext _ π₀.2 S
    rw [← adjoin_le_iff] at hθ
    let θ₀ := θ.emb.comp (inclusion hθ)
    have := (hπ₀ θ₀).trans hθπ
exact hπ θ₀ ⟨_, θ.emb.comp inclusion sup_le this.1 hθ⟩
      ⟨le_sup_left, this.2⟩ ⟨le_sup_right, fun _ => rfl⟩ rfl
  choose θ ge hθ eq using hω
  have : IsChain (· <= ·) (Set.range θ) := by
    simp_rw [← restrictScalars_adjoin_eq_sup, restrictScalars_adjoin] at eq
    rintro _ ⟨π₁, rfl⟩ _ ⟨π₂, rfl⟩ -
    wlog h : π₁ <= π₂ generalizing π₁ π₂
    · exact (this _ _ <| (hc.total π₁.2 π₂.2).resolve_left h).symm
    refine .inl (le_iff.mpr ⟨?_, algHom_ext_of_eq_adjoin _ (eq _) ?_⟩)
    · rw [eq, eq]; exact adjoin.mono _ _ _ (Set.union_subset_union_left _ h.1)
    rintro x (hx | hx)
    · change (θ π₂).emb (inclusion (ge π₂).1 <| inclusion h.1 ⟨x, hx⟩) =
        (θ π₁).emb (inclusion (ge π₁).1 ⟨x, hx⟩)
      rw [(ge π₁).2]; rw [(ge π₂).2]; rw [h.2]
    · change (θ π₂).emb (inclusion (hθ π₂).1 ⟨x, subset_adjoin _ _ hx⟩) =
        (θ π₁).emb (inclusion (hθ π₁).1 ⟨x, subset_adjoin _ _ hx⟩)
      rw [(hθ π₁).2]; rw [(hθ π₂).2]
  refine ⟨union _ this, le_of_carrier_le_iSup (fun π => le_union c hc π.2)
    (fun π => (ge π).trans <| le_union _ _ ⟨_, rfl⟩) (carrier_union _ _).le, ?_⟩
  simp_rw [carrier_union, iSup_range', eq]
  exact (subset_adjoin _ _).trans (SetLike.coe_subset_coe.mpr <|
le_sup_right.trans le_iSup_of_le (Classical.arbitrary _) le_rfl)

Depends on / 依赖: adjoin, adjoin_le_iff, alg.isIntegral, carrier, directed, emb.comp, finiteDimensional_adjoin, finite_le, hc.directed.finite_le, inclusion, isIntegral, sup_le
-/
theorem union_isExtendible [alg : Algebra.IsAlgebraic F E]
    [Nonempty c] (hext : forall σ in c, σ.IsExtendible) :
    (union c hc).IsExtendible := fun S => by
  let Ω := adjoin F (S : Set E) ->ₐ[F] K
  have ⟨ω, hω⟩ : exists ω : Ω, forall π : c, exists θ >= π.1, ⟨_, ω⟩ <= θ ∧ θ.carrier = π.1.1 ⊔ adjoin F S := by
    by_contra!; choose π hπ using this
    have := finiteDimensional_adjoin (S := (S : Set E)) fun _ _ => (alg.isIntegral).1 _
    have ⟨π₀, hπ₀⟩ := hc.directed.finite_le π
    have ⟨θ, hθπ, hθ⟩ := hext _ π₀.2 S
    rw [← adjoin_le_iff] at hθ
    let θ₀ := θ.emb.comp (inclusion hθ)
    have := (hπ₀ θ₀).trans hθπ
exact hπ θ₀ ⟨_, θ.emb.comp inclusion sup_le this.1 hθ⟩
      ⟨le_sup_left, this.2⟩ ⟨le_sup_right, fun _ => rfl⟩ rfl
  choose θ ge hθ eq using hω
  have : IsChain (· <= ·) (Set.range θ) := by
    simp_rw [← restrictScalars_adjoin_eq_sup, restrictScalars_adjoin] at eq
    rintro _ ⟨π₁, rfl⟩ _ ⟨π₂, rfl⟩ -
    wlog h : π₁ <= π₂ generalizing π₁ π₂
    · exact (this _ _ <| (hc.total π₁.2 π₂.2).resolve_left h).symm
    refine .inl (le_iff.mpr ⟨?_, algHom_ext_of_eq_adjoin _ (eq _) ?_⟩)
    · rw [eq, eq]; exact adjoin.mono _ _ _ (Set.union_subset_union_left _ h.1)
    rintro x (hx | hx)
    · change (θ π₂).emb (inclusion (ge π₂).1 <| inclusion h.1 ⟨x, hx⟩) =
        (θ π₁).emb (inclusion (ge π₁).1 ⟨x, hx⟩)
      rw [(ge π₁).2]; rw [(ge π₂).2]; rw [h.2]
    · change (θ π₂).emb (inclusion (hθ π₂).1 ⟨x, subset_adjoin _ _ hx⟩) =
        (θ π₁).emb (inclusion (hθ π₁).1 ⟨x, subset_adjoin _ _ hx⟩)
      rw [(hθ π₁).2]; rw [(hθ π₂).2]
  refine ⟨union _ this, le_of_carrier_le_iSup (fun π => le_union c hc π.2)
    (fun π => (ge π).trans <| le_union _ _ ⟨_, rfl⟩) (carrier_union _ _).le, ?_⟩
  simp_rw [carrier_union, iSup_range', eq]
  exact (subset_adjoin _ _).trans (SetLike.coe_subset_coe.mpr <|
le_sup_right.trans le_iSup_of_le (Classical.arbitrary _) le_rfl)

end Chain

/--
theorem `nonempty_algHom_of_exist_lifts_finset` / 定理 `nonempty_algHom_of_exist_lifts_finset`

English:
theorem nonempty_algHom_of_exist_lifts_finset
  statement: [alg : Algebra.IsAlgebraic F E]
  proof: by
  have : (⊥ : Lifts F E K).IsExtendible := fun S => have ⟨σ, hσ⟩ := h S; ⟨σ, bot_le, hσ⟩
  have ⟨ϕ, hϕ⟩ := zorn_le₀ {ϕ : Lifts F E K | ϕ.IsExtendible}
    fun c hext hc => (isEmpty_or_nonempty c).elim
      (fun _ => ⟨⊥, this, fun ϕ hϕ => isEmptyElim (⟨ϕ, hϕ⟩ : c)⟩)
      fun _ => ⟨_, union_isExtendible c hc hext, le_union c hc⟩
suffices ϕ.carrier = ⊤ from ⟨ϕ.emb.comp ((equivOfEq this).trans topEquiv).symm⟩
  by_contra!
  obtain ⟨α, -, hα⟩ := SetLike.exists_of_lt this.lt_top
  let _ : Algebra ϕ.carrier K := ϕ.emb.toAlgebra
  let Λ := ϕ.carrier⟮α⟯ ->ₐ[ϕ.carrier] K
  have := finiteDimensional_adjoin (S := {α}) fun _ _ => ((alg.tower_top ϕ.carrier).isIntegral).1 _
  let L (σ : Λ) : Lifts F E K := ⟨ϕ.carrier⟮α⟯.restrictScalars F, σ.restrictScalars F⟩
  have hL (σ : Λ) : ϕ < L σ := lt_iff.mpr
    ⟨by simpa only [L, restrictScalars_adjoin_eq_sup, left_lt_sup, adjoin_simple_le_iff],
      AlgHom.coe_ringHom_injective σ.comp_algebraMap⟩
  have ⟨(ϕ_ext : ϕ.IsExtendible), ϕ_max⟩ := maximal_iff_forall_gt.mp hϕ
  simp_rw [Set.mem_ofPred, IsExtendible] at ϕ_max; push Not at ϕ_max
  choose S hS using fun σ : Λ => ϕ_max (hL σ)
  classical
  have ⟨θ, hθϕ, hθ⟩ := ϕ_ext ({α} union Finset.univ.biUnion S)
  simp_rw [Finset.coe_union, Set.union_subset_iff, Finset.coe_singleton, Set.singleton_subset_iff,
    Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.iUnion_subset_iff] at hθ
  have : ϕ.carrier⟮α⟯.restrictScalars F <= θ.carrier := by
    rw [restrictScalars_adjoin_eq_sup]; rw [sup_le_iff]; rw [adjoin_simple_le_iff]; exact ⟨hθϕ.1, hθ.1⟩
  exact hS ⟨(θ.emb.comp <| inclusion this).toRingHom, hθϕ.2⟩ θ ⟨this, fun _ => rfl⟩ (hθ.2 _)

中文:
定理 nonempty_algHom_of_exist_lifts_finset
  结论: [alg : 代数.是代数 F E]
  证明: by
  have : (⊥ : Lifts F E K).IsExtendible := fun S => have ⟨σ, hσ⟩ := h S; ⟨σ, bot_le, hσ⟩
  have ⟨ϕ, hϕ⟩ := zorn_le₀ {ϕ : Lifts F E K | ϕ.IsExtendible}
    fun c hext hc => (isEmpty_or_nonempty c).elim
      (fun _ => ⟨⊥, this, fun ϕ hϕ => isEmptyElim (⟨ϕ, hϕ⟩ : c)⟩)
      fun _ => ⟨_, union_isExtendible c hc hext, le_union c hc⟩
suffices ϕ.carrier = ⊤ from ⟨ϕ.emb.comp ((equivOfEq this).trans topEquiv).symm⟩
  by_contra!
  obtain ⟨α, -, hα⟩ := SetLike.exists_of_lt this.lt_top
  let _ : Algebra ϕ.carrier K := ϕ.emb.toAlgebra
  let Λ := ϕ.carrier⟮α⟯ ->ₐ[ϕ.carrier] K
  have := finiteDimensional_adjoin (S := {α}) fun _ _ => ((alg.tower_top ϕ.carrier).isIntegral).1 _
  let L (σ : Λ) : Lifts F E K := ⟨ϕ.carrier⟮α⟯.restrictScalars F, σ.restrictScalars F⟩
  have hL (σ : Λ) : ϕ < L σ := lt_iff.mpr
    ⟨by simpa only [L, restrictScalars_adjoin_eq_sup, left_lt_sup, adjoin_simple_le_iff],
      AlgHom.coe_ringHom_injective σ.comp_algebraMap⟩
  have ⟨(ϕ_ext : ϕ.IsExtendible), ϕ_max⟩ := maximal_iff_forall_gt.mp hϕ
  simp_rw [Set.mem_ofPred, IsExtendible] at ϕ_max; push Not at ϕ_max
  choose S hS using fun σ : Λ => ϕ_max (hL σ)
  classical
  have ⟨θ, hθϕ, hθ⟩ := ϕ_ext ({α} union Finset.univ.biUnion S)
  simp_rw [Finset.coe_union, Set.union_subset_iff, Finset.coe_singleton, Set.singleton_subset_iff,
    Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.iUnion_subset_iff] at hθ
  have : ϕ.carrier⟮α⟯.restrictScalars F <= θ.carrier := by
    rw [restrictScalars_adjoin_eq_sup]; rw [sup_le_iff]; rw [adjoin_simple_le_iff]; exact ⟨hθϕ.1, hθ.1⟩
  exact hS ⟨(θ.emb.comp <| inclusion this).toRingHom, hθϕ.2⟩ θ ⟨this, fun _ => rfl⟩ (hθ.2 _)

Depends on / 依赖: Algebra, IsExtendible, SetLike, SetLike.exists_of_lt, bot_le, carrier, emb.comp, emb.toAl, equivOfEq, exists_of_lt, isEmptyElim, isEmpty_or_nonempty, le_union, lt_top, this.lt_top, topEquiv, union_isExtendible
-/
theorem nonempty_algHom_of_exist_lifts_finset [alg : Algebra.IsAlgebraic F E]
    (h : forall S : Finset E, exists σ : Lifts F E K, (S : Set E) subseteq σ.carrier) :
    Nonempty (E ->ₐ[F] K) := by
  have : (⊥ : Lifts F E K).IsExtendible := fun S => have ⟨σ, hσ⟩ := h S; ⟨σ, bot_le, hσ⟩
  have ⟨ϕ, hϕ⟩ := zorn_le₀ {ϕ : Lifts F E K | ϕ.IsExtendible}
    fun c hext hc => (isEmpty_or_nonempty c).elim
      (fun _ => ⟨⊥, this, fun ϕ hϕ => isEmptyElim (⟨ϕ, hϕ⟩ : c)⟩)
      fun _ => ⟨_, union_isExtendible c hc hext, le_union c hc⟩
suffices ϕ.carrier = ⊤ from ⟨ϕ.emb.comp ((equivOfEq this).trans topEquiv).symm⟩
  by_contra!
  obtain ⟨α, -, hα⟩ := SetLike.exists_of_lt this.lt_top
  let _ : Algebra ϕ.carrier K := ϕ.emb.toAlgebra
  let Λ := ϕ.carrier⟮α⟯ ->ₐ[ϕ.carrier] K
  have := finiteDimensional_adjoin (S := {α}) fun _ _ => ((alg.tower_top ϕ.carrier).isIntegral).1 _
  let L (σ : Λ) : Lifts F E K := ⟨ϕ.carrier⟮α⟯.restrictScalars F, σ.restrictScalars F⟩
  have hL (σ : Λ) : ϕ < L σ := lt_iff.mpr
    ⟨by simpa only [L, restrictScalars_adjoin_eq_sup, left_lt_sup, adjoin_simple_le_iff],
      AlgHom.coe_ringHom_injective σ.comp_algebraMap⟩
  have ⟨(ϕ_ext : ϕ.IsExtendible), ϕ_max⟩ := maximal_iff_forall_gt.mp hϕ
  simp_rw [Set.mem_ofPred, IsExtendible] at ϕ_max; push Not at ϕ_max
  choose S hS using fun σ : Λ => ϕ_max (hL σ)
  classical
  have ⟨θ, hθϕ, hθ⟩ := ϕ_ext ({α} union Finset.univ.biUnion S)
  simp_rw [Finset.coe_union, Set.union_subset_iff, Finset.coe_singleton, Set.singleton_subset_iff,
    Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.iUnion_subset_iff] at hθ
  have : ϕ.carrier⟮α⟯.restrictScalars F <= θ.carrier := by
    rw [restrictScalars_adjoin_eq_sup]; rw [sup_le_iff]; rw [adjoin_simple_le_iff]; exact ⟨hθϕ.1, hθ.1⟩
  exact hS ⟨(θ.emb.comp <| inclusion this).toRingHom, hθϕ.2⟩ θ ⟨this, fun _ => rfl⟩ (hθ.2 _)

/--
theorem `exists_lift_of_splits'` / 定理 `exists_lift_of_splits'`

English:
theorem exists_lift_of_splits'
  statement: (x : Lifts F E K) {s : E} (h1 : IsIntegral x.carrier s)
  proof: have I2 := (minpoly.degree_pos h1).ne'
  letI : Algebra x.carrier K := x.emb.toRingHom.toAlgebra
  let carrier := x.carrier⟮s⟯.restrictScalars F
  letI : Algebra x.carrier carrier := x.carrier⟮s⟯.toSubalgebra.algebra
  let φ : carrier ->ₐ[x.carrier] K := ((algHomAdjoinIntegralEquiv x.carrier h1).symm
    ⟨rootOfSplits h2 (by rwa [degree_map]), by
      rw [mem_aroots]; rw [and_iff_right (minpoly.ne_zero h1)]
      exact (eval_map _ _).symm.trans (eval_rootOfSplits _ _)⟩)
  ⟨⟨carrier, (@algHomEquivSigma F x.carrier carrier K _ _ _ _ _ _ _ _
      (IsScalarTower.of_algebraMap_eq fun _ => rfl)).symm ⟨x.emb, φ⟩⟩,
    ⟨fun z hz => algebraMap_mem x.carrier⟮s⟯ ⟨z, hz⟩, φ.commutes⟩,
    mem_adjoin_simple_self x.carrier s⟩

中文:
定理 存在_lift_of_splits'
  结论: (x : Lifts F E K) {s : E} (h1 : 是整 x.carrier s)
  证明: have I2 := (minpoly.degree_pos h1).ne'
  letI : Algebra x.carrier K := x.emb.toRingHom.toAlgebra
  let carrier := x.carrier⟮s⟯.restrictScalars F
  letI : Algebra x.carrier carrier := x.carrier⟮s⟯.toSubalgebra.algebra
  let φ : carrier ->ₐ[x.carrier] K := ((algHomAdjoinIntegralEquiv x.carrier h1).symm
    ⟨rootOfSplits h2 (by rwa [degree_map]), by
      rw [mem_aroots]; rw [and_iff_right (minpoly.ne_zero h1)]
      exact (eval_map _ _).symm.trans (eval_rootOfSplits _ _)⟩)
  ⟨⟨carrier, (@algHomEquivSigma F x.carrier carrier K _ _ _ _ _ _ _ _
      (IsScalarTower.of_algebraMap_eq fun _ => rfl)).symm ⟨x.emb, φ⟩⟩,
    ⟨fun z hz => algebraMap_mem x.carrier⟮s⟯ ⟨z, hz⟩, φ.commutes⟩,
    mem_adjoin_simple_self x.carrier s⟩

Depends on / 依赖: Algebra, algHomAdjoinIntegralEquiv, algHomEquivSigma, algebra, and_iff_right, carrie, carrier, degree_map, degree_pos, eval_map, eval_rootOfSplits, mem_aroots, minpoly, minpoly.degree_pos, minpoly.ne_zero, ne_zero, restrictScalars, rootOfSplits, symm.trans, toAlgebra
-/
theorem exists_lift_of_splits' (x : Lifts F E K) {s : E} (h1 : IsIntegral x.carrier s)
    (h2 : ((minpoly x.carrier s).map x.emb.toRingHom).Splits) : exists y, x <= y ∧ s in y.carrier :=
  have I2 := (minpoly.degree_pos h1).ne'
  letI : Algebra x.carrier K := x.emb.toRingHom.toAlgebra
  let carrier := x.carrier⟮s⟯.restrictScalars F
  letI : Algebra x.carrier carrier := x.carrier⟮s⟯.toSubalgebra.algebra
  let φ : carrier ->ₐ[x.carrier] K := ((algHomAdjoinIntegralEquiv x.carrier h1).symm
    ⟨rootOfSplits h2 (by rwa [degree_map]), by
      rw [mem_aroots]; rw [and_iff_right (minpoly.ne_zero h1)]
      exact (eval_map _ _).symm.trans (eval_rootOfSplits _ _)⟩)
  ⟨⟨carrier, (@algHomEquivSigma F x.carrier carrier K _ _ _ _ _ _ _ _
      (IsScalarTower.of_algebraMap_eq fun _ => rfl)).symm ⟨x.emb, φ⟩⟩,
    ⟨fun z hz => algebraMap_mem x.carrier⟮s⟯ ⟨z, hz⟩, φ.commutes⟩,
    mem_adjoin_simple_self x.carrier s⟩

/--
theorem `exists_lift_of_splits` / 定理 `exists_lift_of_splits`

English:
theorem exists_lift_of_splits
  statement: (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
  proof: exists_lift_of_splits' x h1.tower_top h1.minpoly_splits_tower_top' by
    rwa [← x.emb.comp_algebraMap] at h2

中文:
定理 存在_lift_of_splits
  结论: (x : Lifts F E K) {s : E} (h1 : 是整 F s)
  证明: exists_lift_of_splits' x h1.tower_top h1.minpoly_splits_tower_top' by
    rwa [← x.emb.comp_algebraMap] at h2

Depends on / 依赖: comp_algebraMap, exists_lift_of_splits, h1.minpoly_splits_tower_top, h1.tower_top, minpoly_splits_tower_top, tower_top, x.emb.comp_algebraMap
-/
theorem exists_lift_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : ((minpoly F s).map (algebraMap F K)).Splits) : exists y, x <= y ∧ s in y.carrier :=
exists_lift_of_splits' x h1.tower_top h1.minpoly_splits_tower_top' by
    rwa [← x.emb.comp_algebraMap] at h2

end Lifts

section

/--
theorem `exists_algHom_adjoin_of_splits''` / 定理 `exists_algHom_adjoin_of_splits''`

English:
theorem exists_algHom_adjoin_of_splits''
  statement: {L : IntermediateField F E}
  proof: by
  obtain ⟨φ, hfφ, hφ⟩ := zorn_le_nonempty_Ici₀ _
    (fun c _ hc _ _ => Lifts.exists_upper_bound c hc) ⟨L, f⟩ le_rfl
  refine ⟨φ.emb.comp (inclusion <| (le_extendScalars_iff hfφ.1 <| adjoin L S).mp <|
    adjoin_le_iff.mpr fun s h => ?_), AlgHom.ext hfφ.2⟩
  let := (inclusion hfφ.1).toAlgebra
  let : SMul L φ.carrier := Algebra.toSMul
  have : IsScalarTower L φ.carrier E := ⟨fun x y => smul_assoc x (y : E)⟩
  have := φ.exists_lift_of_splits' (hK s h).1.tower_top ((hK s h).1.minpoly_splits_tower_top' ?_)
  · obtain ⟨y, h1, h2⟩ := this
    exact (hφ h1).1 h2
  · convert! (hK s h).2; ext; apply hfφ.2

中文:
定理 存在_algHom_adjoin_of_splits''
  结论: {L : 中间域 F E}
  证明: by
  obtain ⟨φ, hfφ, hφ⟩ := zorn_le_nonempty_Ici₀ _
    (fun c _ hc _ _ => Lifts.exists_upper_bound c hc) ⟨L, f⟩ le_rfl
  refine ⟨φ.emb.comp (inclusion <| (le_extendScalars_iff hfφ.1 <| adjoin L S).mp <|
    adjoin_le_iff.mpr fun s h => ?_), AlgHom.ext hfφ.2⟩
  let := (inclusion hfφ.1).toAlgebra
  let : SMul L φ.carrier := Algebra.toSMul
  have : IsScalarTower L φ.carrier E := ⟨fun x y => smul_assoc x (y : E)⟩
  have := φ.exists_lift_of_splits' (hK s h).1.tower_top ((hK s h).1.minpoly_splits_tower_top' ?_)
  · obtain ⟨y, h1, h2⟩ := this
    exact (hφ h1).1 h2
  · convert! (hK s h).2; ext; apply hfφ.2
-/
private theorem exists_algHom_adjoin_of_splits'' {L : IntermediateField F E}
    (f : L ->ₐ[F] K) (hK : forall s in S, IsIntegral L s ∧ ((minpoly L s).map f.toRingHom).Splits) :
    exists φ : adjoin L S ->ₐ[F] K, φ.domRestrict L = f := by
  obtain ⟨φ, hfφ, hφ⟩ := zorn_le_nonempty_Ici₀ _
    (fun c _ hc _ _ => Lifts.exists_upper_bound c hc) ⟨L, f⟩ le_rfl
  refine ⟨φ.emb.comp (inclusion <| (le_extendScalars_iff hfφ.1 <| adjoin L S).mp <|
    adjoin_le_iff.mpr fun s h => ?_), AlgHom.ext hfφ.2⟩
  let := (inclusion hfφ.1).toAlgebra
  let : SMul L φ.carrier := Algebra.toSMul
  have : IsScalarTower L φ.carrier E := ⟨fun x y => smul_assoc x (y : E)⟩
  have := φ.exists_lift_of_splits' (hK s h).1.tower_top ((hK s h).1.minpoly_splits_tower_top' ?_)
  · obtain ⟨y, h1, h2⟩ := this
    exact (hφ h1).1 h2
  · convert! (hK s h).2; ext; apply hfφ.2

variable {L : Type*} [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]
  (f : L ->ₐ[F] K) (hK : forall s in S, IsIntegral L s ∧ ((minpoly L s).map f.toRingHom).Splits)

set_option backward.isDefEq.respectTransparency.types false in
include hK in
/--
theorem `exists_algHom_adjoin_of_splits'` / 定理 `exists_algHom_adjoin_of_splits'`

English:
theorem exists_algHom_adjoin_of_splits'
  proof: by
  let L' := (IsScalarTower.toAlgHom F L E).fieldRange
  let f' : L' ->ₐ[F] K := f.comp (AlgEquiv.ofInjectiveField _).symm.toAlgHom
  have := exists_algHom_adjoin_of_splits'' f' (S := S) fun s hs => ?_
· obtain ⟨φ, hφ⟩ := this; refine ⟨φ.comp
      inclusion (?_ : (adjoin L S).restrictScalars F <= (adjoin L' S).restrictScalars F), ?_⟩
    · simp_rw [← SetLike.coe_subset_coe, coe_restrictScalars, adjoin_subset_adjoin_iff]
      exact ⟨subset_adjoin_of_subset_left S (F := L'.toSubfield) le_rfl, subset_adjoin _ _⟩
    · ext x
      let y := (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) x
      refine Eq.trans congr($hφ y) ?_
      simp only [AlgHom.coe_comp, Function.comp_apply, f']
      exact congr_arg f (AlgEquiv.symm_apply_apply _ _)
  let : Algebra L L' := (AlgEquiv.ofInjectiveField _).toRingHom.toAlgebra
  have : IsScalarTower L L' E := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨(hK s hs).1.tower_top, (hK s hs).1.minpoly_splits_tower_top' ?_⟩
  convert! (hK s hs).2
  ext
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
    AlgHom.coe_comp, Function.comp_apply, f']
  exact congr_arg f (AlgEquiv.symm_apply_apply _ _)

include hK in

中文:
定理 存在_algHom_adjoin_of_splits'
  证明: by
  let L' := (IsScalarTower.toAlgHom F L E).fieldRange
  let f' : L' ->ₐ[F] K := f.comp (AlgEquiv.ofInjectiveField _).symm.toAlgHom
  have := exists_algHom_adjoin_of_splits'' f' (S := S) fun s hs => ?_
· obtain ⟨φ, hφ⟩ := this; refine ⟨φ.comp
      inclusion (?_ : (adjoin L S).restrictScalars F <= (adjoin L' S).restrictScalars F), ?_⟩
    · simp_rw [← SetLike.coe_subset_coe, coe_restrictScalars, adjoin_subset_adjoin_iff]
      exact ⟨subset_adjoin_of_subset_left S (F := L'.toSubfield) le_rfl, subset_adjoin _ _⟩
    · ext x
      let y := (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) x
      refine Eq.trans congr($hφ y) ?_
      simp only [AlgHom.coe_comp, Function.comp_apply, f']
      exact congr_arg f (AlgEquiv.symm_apply_apply _ _)
  let : Algebra L L' := (AlgEquiv.ofInjectiveField _).toRingHom.toAlgebra
  have : IsScalarTower L L' E := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨(hK s hs).1.tower_top, (hK s hs).1.minpoly_splits_tower_top' ?_⟩
  convert! (hK s hs).2
  ext
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
    AlgHom.coe_comp, Function.comp_apply, f']
  exact congr_arg f (AlgEquiv.symm_apply_apply _ _)

include hK in

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, IsScalarTower, IsScalarTower.toAlgHom, SetLike, SetLike.coe_subset_coe, adjoin, adjoin_subset_adjoin_iff, coe_restrictScalars, coe_subset_coe, exists_algHom_adjoin_of_splits, f.comp, fieldRange, inclusion, le_rfl, ofInjectiveField, restrictScalars, simp_rw, subset_adjoin, subset_adjoin_of_subset_left
-/
theorem exists_algHom_adjoin_of_splits' :
    exists φ : adjoin L S ->ₐ[F] K, φ.domRestrict L = f := by
  let L' := (IsScalarTower.toAlgHom F L E).fieldRange
  let f' : L' ->ₐ[F] K := f.comp (AlgEquiv.ofInjectiveField _).symm.toAlgHom
  have := exists_algHom_adjoin_of_splits'' f' (S := S) fun s hs => ?_
· obtain ⟨φ, hφ⟩ := this; refine ⟨φ.comp
      inclusion (?_ : (adjoin L S).restrictScalars F <= (adjoin L' S).restrictScalars F), ?_⟩
    · simp_rw [← SetLike.coe_subset_coe, coe_restrictScalars, adjoin_subset_adjoin_iff]
      exact ⟨subset_adjoin_of_subset_left S (F := L'.toSubfield) le_rfl, subset_adjoin _ _⟩
    · ext x
      let y := (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) x
      refine Eq.trans congr($hφ y) ?_
      simp only [AlgHom.coe_comp, Function.comp_apply, f']
      exact congr_arg f (AlgEquiv.symm_apply_apply _ _)
  let : Algebra L L' := (AlgEquiv.ofInjectiveField _).toRingHom.toAlgebra
  have : IsScalarTower L L' E := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨(hK s hs).1.tower_top, (hK s hs).1.minpoly_splits_tower_top' ?_⟩
  convert! (hK s hs).2
  ext
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
    AlgHom.coe_comp, Function.comp_apply, f']
  exact congr_arg f (AlgEquiv.symm_apply_apply _ _)

include hK in
/--
theorem `exists_algHom_of_adjoin_splits'` / 定理 `exists_algHom_of_adjoin_splits'`

English:
theorem exists_algHom_of_adjoin_splits'
  given: (hS : adjoin L S = ⊤)
  proof: have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits' f hK
  ⟨φ.comp (((equivOfEq hS).trans topEquiv).symm.toAlgHom.restrictScalars F), hφ⟩

中文:
定理 存在_algHom_of_adjoin_splits'
  条件: (hS : adjoin L S = ⊤)
  证明: have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits' f hK
  ⟨φ.comp (((equivOfEq hS).trans topEquiv).symm.toAlgHom.restrictScalars F), hφ⟩

Depends on / 依赖: equivOfEq, exists_algHom_adjoin_of_splits, restrictScalars, symm.toAlgHom.restrictScalars, toAlgHom, topEquiv
-/
theorem exists_algHom_of_adjoin_splits' (hS : adjoin L S = ⊤) :
    exists φ : E ->ₐ[F] K, φ.domRestrict L = f :=
  have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits' f hK
  ⟨φ.comp (((equivOfEq hS).trans topEquiv).symm.toAlgHom.restrictScalars F), hφ⟩

/--
theorem `exists_algHom_of_splits'` / 定理 `exists_algHom_of_splits'`

English:
theorem exists_algHom_of_splits'
  proof: exists_algHom_of_adjoin_splits' f (fun x _ => hK x) (adjoin_univ L E)

中文:
定理 存在_algHom_of_splits'
  证明: exists_algHom_of_adjoin_splits' f (fun x _ => hK x) (adjoin_univ L E)

Depends on / 依赖: adjoin_univ, exists_algHom_of_adjoin_splits
-/
theorem exists_algHom_of_splits'
    (hK : forall s : E, IsIntegral L s ∧ ((minpoly L s).map f.toRingHom).Splits) :
    exists φ : E ->ₐ[F] K, φ.domRestrict L = f :=
  exists_algHom_of_adjoin_splits' f (fun x _ => hK x) (adjoin_univ L E)

end

variable (hK : forall s in S, IsIntegral F s ∧ ((minpoly F s).map (algebraMap F K)).Splits)
  (hK' : forall s : E, IsIntegral F s ∧ ((minpoly F s).map (algebraMap F K)).Splits)
  {L : IntermediateField F E} (f : L ->ₐ[F] K) (hL : L <= adjoin F S) {x : E} {y : K}

section
include hK

/--
theorem `exists_algHom_adjoin_of_splits` / 定理 `exists_algHom_adjoin_of_splits`

English:
theorem exists_algHom_adjoin_of_splits
  statement: exists φ : adjoin F S ->ₐ[F] K, φ.comp (inclusion hL) = f
  proof: by
  obtain ⟨φ, hfφ, hφ⟩ := zorn_le_nonempty_Ici₀ _
    (fun c _ hc _ _ => Lifts.exists_upper_bound c hc) ⟨L, f⟩ le_rfl
  refine ⟨φ.emb.comp (inclusion <| adjoin_le_iff.mpr fun s hs => ?_), ?_⟩
  · rcases φ.exists_lift_of_splits (hK s hs).1 (hK s hs).2 with ⟨y, h1, h2⟩
    exact (hφ h1).1 h2
  · ext; apply hfφ.2

中文:
定理 存在_algHom_adjoin_of_splits
  结论: 存在 φ : adjoin F S ->ₐ[F] K, φ.comp (inclusion hL) = f
  证明: by
  obtain ⟨φ, hfφ, hφ⟩ := zorn_le_nonempty_Ici₀ _
    (fun c _ hc _ _ => Lifts.exists_upper_bound c hc) ⟨L, f⟩ le_rfl
  refine ⟨φ.emb.comp (inclusion <| adjoin_le_iff.mpr fun s hs => ?_), ?_⟩
  · rcases φ.exists_lift_of_splits (hK s hs).1 (hK s hs).2 with ⟨y, h1, h2⟩
    exact (hφ h1).1 h2
  · ext; apply hfφ.2

Depends on / 依赖: Lifts.exists_upper_bound, adjoin_le_iff, adjoin_le_iff.mpr, emb.comp, exists_lift_of_splits, exists_upper_bound, inclusion, le_rfl
-/
theorem exists_algHom_adjoin_of_splits : exists φ : adjoin F S ->ₐ[F] K, φ.comp (inclusion hL) = f := by
  obtain ⟨φ, hfφ, hφ⟩ := zorn_le_nonempty_Ici₀ _
    (fun c _ hc _ _ => Lifts.exists_upper_bound c hc) ⟨L, f⟩ le_rfl
  refine ⟨φ.emb.comp (inclusion <| adjoin_le_iff.mpr fun s hs => ?_), ?_⟩
  · rcases φ.exists_lift_of_splits (hK s hs).1 (hK s hs).2 with ⟨y, h1, h2⟩
    exact (hφ h1).1 h2
  · ext; apply hfφ.2

/--
theorem `nonempty_algHom_adjoin_of_splits` / 定理 `nonempty_algHom_adjoin_of_splits`

English:
theorem nonempty_algHom_adjoin_of_splits
  statement: Nonempty (adjoin F S ->ₐ[F] K)
  proof: have ⟨φ, _⟩ := exists_algHom_adjoin_of_splits hK (⊥ : Lifts F E K).emb bot_le; ⟨φ⟩

中文:
定理 nonempty_algHom_adjoin_of_splits
  结论: 非空 (adjoin F S ->ₐ[F] K)
  证明: have ⟨φ, _⟩ := exists_algHom_adjoin_of_splits hK (⊥ : Lifts F E K).emb bot_le; ⟨φ⟩

Depends on / 依赖: bot_le, exists_algHom_adjoin_of_splits
-/
theorem nonempty_algHom_adjoin_of_splits : Nonempty (adjoin F S ->ₐ[F] K) :=
  have ⟨φ, _⟩ := exists_algHom_adjoin_of_splits hK (⊥ : Lifts F E K).emb bot_le; ⟨φ⟩

variable (hS : adjoin F S = ⊤)

include hS in
/--
theorem `exists_algHom_of_adjoin_splits` / 定理 `exists_algHom_of_adjoin_splits`

English:
theorem exists_algHom_of_adjoin_splits
  statement: exists φ : E ->ₐ[F] K, φ.comp L.val = f
  proof: have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK f (hS.symm ▸ le_top)
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩

include hS in

中文:
定理 存在_algHom_of_adjoin_splits
  结论: 存在 φ : E ->ₐ[F] K, φ.comp L.val = f
  证明: have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK f (hS.symm ▸ le_top)
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩

include hS in

Depends on / 依赖: equivOfEq, exists_algHom_adjoin_of_splits, hS.symm, le_top, symm.toAlgHom, toAlgHom, topEquiv
-/
theorem exists_algHom_of_adjoin_splits : exists φ : E ->ₐ[F] K, φ.comp L.val = f :=
  have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK f (hS.symm ▸ le_top)
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩

include hS in
/--
theorem `nonempty_algHom_of_adjoin_splits` / 定理 `nonempty_algHom_of_adjoin_splits`

English:
theorem nonempty_algHom_of_adjoin_splits
  statement: Nonempty (E ->ₐ[F] K)
  proof: have ⟨φ, _⟩ := exists_algHom_of_adjoin_splits hK (⊥ : Lifts F E K).emb hS; ⟨φ⟩

中文:
定理 nonempty_algHom_of_adjoin_splits
  结论: 非空 (E ->ₐ[F] K)
  证明: have ⟨φ, _⟩ := exists_algHom_of_adjoin_splits hK (⊥ : Lifts F E K).emb hS; ⟨φ⟩

Depends on / 依赖: exists_algHom_of_adjoin_splits
-/
theorem nonempty_algHom_of_adjoin_splits : Nonempty (E ->ₐ[F] K) :=
  have ⟨φ, _⟩ := exists_algHom_of_adjoin_splits hK (⊥ : Lifts F E K).emb hS; ⟨φ⟩

variable (hx : x in adjoin F S) (hy : aeval y (minpoly F x) = 0)
include hy

/--
theorem `exists_algHom_adjoin_of_splits_of_aeval` / 定理 `exists_algHom_adjoin_of_splits_of_aeval`

English:
theorem exists_algHom_adjoin_of_splits_of_aeval
  statement: exists φ : adjoin F S ->ₐ[F] K, φ ⟨x, hx⟩ = y
  proof: by
  have := isAlgebraic_adjoin (fun s hs => (hK s hs).1)
  have ix : IsAlgebraic F _ := Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : adjoin F S)
  rw [isAlgebraic_iff_isIntegral]; rw [isIntegral_iff] at ix
  obtain ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK ((algHomAdjoinIntegralEquiv F ix).symm
    ⟨y, mem_aroots.mpr ⟨minpoly.ne_zero ix, hy⟩⟩) (adjoin_simple_le_iff.mpr hx)
exact ⟨φ, (DFunLike.congr_fun hφ <| AdjoinSimple.gen F x).trans
    algHomAdjoinIntegralEquiv_symm_apply_gen F ix _⟩

include hS in

中文:
定理 存在_algHom_adjoin_of_splits_of_aeval
  结论: 存在 φ : adjoin F S ->ₐ[F] K, φ ⟨x, hx⟩ = y
  证明: by
  have := isAlgebraic_adjoin (fun s hs => (hK s hs).1)
  have ix : IsAlgebraic F _ := Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : adjoin F S)
  rw [isAlgebraic_iff_isIntegral]; rw [isIntegral_iff] at ix
  obtain ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK ((algHomAdjoinIntegralEquiv F ix).symm
    ⟨y, mem_aroots.mpr ⟨minpoly.ne_zero ix, hy⟩⟩) (adjoin_simple_le_iff.mpr hx)
exact ⟨φ, (DFunLike.congr_fun hφ <| AdjoinSimple.gen F x).trans
    algHomAdjoinIntegralEquiv_symm_apply_gen F ix _⟩

include hS in

Depends on / 依赖: AdjoinSimple, AdjoinSimple.gen, Algebra, Algebra.IsAlgebraic.isAlgebraic, DFunLike, DFunLike.congr_fun, IsAlgebraic, adjoin, adjoin_simple_le_iff, adjoin_simple_le_iff.mpr, algHomAdjoinIntegralEquiv, algHomAdjoinIntegralEquiv_symm_apply_gen, congr_fun, exists_algHom_adjoin_of_splits, isAlgebraic, isAlgebraic_adjoin, isAlgebraic_iff_isIntegral, isIntegral_iff, mem_aroots, mem_aroots.mpr
-/
theorem exists_algHom_adjoin_of_splits_of_aeval : exists φ : adjoin F S ->ₐ[F] K, φ ⟨x, hx⟩ = y := by
  have := isAlgebraic_adjoin (fun s hs => (hK s hs).1)
  have ix : IsAlgebraic F _ := Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : adjoin F S)
  rw [isAlgebraic_iff_isIntegral]; rw [isIntegral_iff] at ix
  obtain ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits hK ((algHomAdjoinIntegralEquiv F ix).symm
    ⟨y, mem_aroots.mpr ⟨minpoly.ne_zero ix, hy⟩⟩) (adjoin_simple_le_iff.mpr hx)
exact ⟨φ, (DFunLike.congr_fun hφ <| AdjoinSimple.gen F x).trans
    algHomAdjoinIntegralEquiv_symm_apply_gen F ix _⟩

include hS in
/--
theorem `exists_algHom_of_adjoin_splits_of_aeval` / 定理 `exists_algHom_of_adjoin_splits_of_aeval`

English:
theorem exists_algHom_of_adjoin_splits_of_aeval
  statement: exists φ : E ->ₐ[F] K, φ x = y
  proof: have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits_of_aeval hK (hS ▸ mem_top) hy
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩


include hK'

中文:
定理 存在_algHom_of_adjoin_splits_of_aeval
  结论: 存在 φ : E ->ₐ[F] K, φ x = y
  证明: have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits_of_aeval hK (hS ▸ mem_top) hy
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩


include hK'

Depends on / 依赖: equivOfEq, exists_algHom_adjoin_of_splits_of_aeval, mem_top, symm.toAlgHom, toAlgHom, topEquiv
-/
theorem exists_algHom_of_adjoin_splits_of_aeval : exists φ : E ->ₐ[F] K, φ x = y :=
  have ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits_of_aeval hK (hS ▸ mem_top) hy
  ⟨φ.comp ((equivOfEq hS).trans topEquiv).symm.toAlgHom, hφ⟩


include hK'

end

section
include hK'

/--
theorem `exists_algHom_of_splits` / 定理 `exists_algHom_of_splits`

English:
theorem exists_algHom_of_splits
  statement: exists φ : E ->ₐ[F] K, φ.comp L.val = f
  proof: exists_algHom_of_adjoin_splits (fun x _ => hK' x) f (adjoin_univ F E)

中文:
定理 存在_algHom_of_splits
  结论: 存在 φ : E ->ₐ[F] K, φ.comp L.val = f
  证明: exists_algHom_of_adjoin_splits (fun x _ => hK' x) f (adjoin_univ F E)

Depends on / 依赖: adjoin_univ, exists_algHom_of_adjoin_splits
-/
theorem exists_algHom_of_splits : exists φ : E ->ₐ[F] K, φ.comp L.val = f :=
  exists_algHom_of_adjoin_splits (fun x _ => hK' x) f (adjoin_univ F E)

/--
theorem `nonempty_algHom_of_splits` / 定理 `nonempty_algHom_of_splits`

English:
theorem nonempty_algHom_of_splits
  statement: Nonempty (E ->ₐ[F] K)
  proof: nonempty_algHom_of_adjoin_splits (fun x _ => hK' x) (adjoin_univ F E)

中文:
定理 nonempty_algHom_of_splits
  结论: 非空 (E ->ₐ[F] K)
  证明: nonempty_algHom_of_adjoin_splits (fun x _ => hK' x) (adjoin_univ F E)

Depends on / 依赖: adjoin_univ, nonempty_algHom_of_adjoin_splits
-/
theorem nonempty_algHom_of_splits : Nonempty (E ->ₐ[F] K) :=
  nonempty_algHom_of_adjoin_splits (fun x _ => hK' x) (adjoin_univ F E)

/--
theorem `exists_algHom_of_splits_of_aeval` / 定理 `exists_algHom_of_splits_of_aeval`

English:
theorem exists_algHom_of_splits_of_aeval
  given: (hy : aeval y (minpoly F x) = 0)
  proof: exists_algHom_of_adjoin_splits_of_aeval (fun x _ => hK' x) (adjoin_univ F E) hy

中文:
定理 存在_algHom_of_splits_of_aeval
  条件: (hy : aeval y (minpoly F x) = 0)
  证明: exists_algHom_of_adjoin_splits_of_aeval (fun x _ => hK' x) (adjoin_univ F E) hy

Depends on / 依赖: adjoin_univ, exists_algHom_of_adjoin_splits_of_aeval
-/
theorem exists_algHom_of_splits_of_aeval (hy : aeval y (minpoly F x) = 0) :
    exists φ : E ->ₐ[F] K, φ x = y :=
  exists_algHom_of_adjoin_splits_of_aeval (fun x _ => hK' x) (adjoin_univ F E) hy

end

end IntermediateField

section Algebra.IsAlgebraic

/--
theorem `Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits` / 定理 `Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits`

English:
theorem Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits
  statement: {F K : Type*} (L : Type*)
  proof: by
  ext a
  rw [mem_rootSet_of_ne (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))]
  refine ⟨fun ⟨ψ, hψ⟩ => ?_, fun ha => IntermediateField.exists_algHom_of_splits_of_aeval
    (fun x => ⟨Algebra.IsIntegral.isIntegral x, hA x⟩) ha⟩
  rw [← hψ]; rw [Polynomial.aeval_algHom_apply ψ x]; rw [minpoly.aeval]; rw [map_zero]

中文:
定理 代数.是代数.range_eval_eq_rootSet_minpoly_of_splits
  结论: {F K : 类型} (L : 类型)
  证明: by
  ext a
  rw [mem_rootSet_of_ne (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))]
  refine ⟨fun ⟨ψ, hψ⟩ => ?_, fun ha => IntermediateField.exists_algHom_of_splits_of_aeval
    (fun x => ⟨Algebra.IsIntegral.isIntegral x, hA x⟩) ha⟩
  rw [← hψ]; rw [Polynomial.aeval_algHom_apply ψ x]; rw [minpoly.aeval]; rw [map_zero]

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IntermediateField, IntermediateField.exists_algHom_of_splits_of_aeval, IsIntegral, Polynomial, Polynomial.aeval_algHom_apply, aeval_algHom_apply, exists_algHom_of_splits_of_aeval, isIntegral, map_zero, mem_rootSet_of_ne, minpoly, minpoly.aeval, minpoly.ne_zero, ne_zero
-/
theorem Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits {F K : Type*} (L : Type*)
    [Field F] [Field K] [Field L] [Algebra F L] [Algebra F K]
    (hA : forall x : K, ((minpoly F x).map (algebraMap F L)).Splits)
    [Algebra.IsAlgebraic F K] (x : K) :
    (Set.range fun (ψ : K ->ₐ[F] L) => ψ x) = (minpoly F x).rootSet L := by
  ext a
  rw [mem_rootSet_of_ne (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))]
  refine ⟨fun ⟨ψ, hψ⟩ => ?_, fun ha => IntermediateField.exists_algHom_of_splits_of_aeval
    (fun x => ⟨Algebra.IsIntegral.isIntegral x, hA x⟩) ha⟩
  rw [← hψ]; rw [Polynomial.aeval_algHom_apply ψ x]; rw [minpoly.aeval]; rw [map_zero]

end Algebra.IsAlgebraic
