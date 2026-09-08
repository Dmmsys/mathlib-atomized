/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Length

/-!
# Lengths along extensions of local rings

This file proves results relating lengths along extensions of local rings.

## Main results
- `IsLocalRing.length_restrictScalars`: If `B/A` is an extension of local rings, and if `M`
  is a `B`-module, then `ℓ_A(M) = ℓ_B(M) * [κ(B) : κ(A)]`.
- `IsLocalRing.length_baseChange`: If `B/A` is a flat extension of local rings, and if `M` is an
  `A`-module, then `ℓ_B(B ⊗[A] M) = ℓ_A(M) * ℓ_B(B ⧸ m_A)`.
-/

public section

open IsLocalRing LinearMap Module Submodule TensorProduct AlgebraTensorModule

variable {A B M : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [AddCommGroup M] [Module A M]

section tower

variable [Module B M] [IsScalarTower A B M]

variable (A) in
/-
**CovBy.length_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.length_restrictScalars {p q : Submodule B M} (h : p ⋖ q) : length A 
q = Module.length A p + Module.length (ResidueField A) (ResidueField B)
参数：h : p ⋖ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.le`：CovBy.le (h : a ⋖ b) : a <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_inclusion`：range_inclusion (p q : Submodule R M) (h : p 
<= q) : range (inclusion h) = comap q.subtype p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `covBy_iff_quot_is_simple`：covBy_iff_quot_is_simple {A B : Submodule R M}
 (hAB : A <= B) : A ⋖ B ↔ IsSimpleModule R (B ⧸ Submodule.comap B.subtype A)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSimpleModule_iff_quot_maximal`：isSimpleModule_iff_quot_maximal : IsSim
pleModule R M ↔ exists I : Ideal R, I.IsMaximal ∧ Nonempty (M ≃ₗ[R] R ⧸ I)
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.ker_comp`：ker_comp (l : M ->ₛₗ[σ₁₂] M₂) : LinearMap.ker (((e
'' : M₂ ->ₛₗ[σ₂₃] M₃).comp l : M ->ₛₗ[σ₁₃] M₃) : M ->ₛₗ[σ₁₃] M₃) = LinearMap.ker
 l
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用引理 `Module.length_eq_add_of_exact`：Module.length_eq_add_of_exact : Module.le
ngth R M = Module.length R N + Module.length R P
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.length_eq_of_surjective`：Module.length_eq_of_surjective {S : Type
*} [CommRing S] [Algebra S R] [Module S M] [IsScalarTower S R M] (h : Function.S
urjective (algebraMa…
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst_3
 : IsLocalRing S] [inst_4 : Alge…
· 使用引理 `IsLocalRing.residue_surjective`：residue_surjective : Function.Surjective
 (IsLocalRing.residue R)
· 使用引理 `Module.length_eq_rank`：Module.length_eq_rank (K M : Type*) [DivisionRing
 K] [AddCommGroup M] [Module K M] : Module.length K M = (Module.rank K M).toENat
-/
theorem CovBy.length_restrictScalars {p q : Submodule B M} (h : p ⋖ q) :
    length A q = Module.length A p + Module.length (ResidueField A) (ResidueField B) := by
  let f : p →ₗ[B] q := inclusion h.le
  have key : IsSimpleModule B (q ⧸ f.range) := by
    rwa [range_inclusion, ← covBy_iff_quot_is_simple h.le]
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
  rw [eq_maximalIdeal hm] at e
  -- `0 -> p -> q -> κ(B) -> 0` is exact, and length is additive
  let g : q →ₗ[B] ResidueField B := e.comp f.range.mkQ
  have : Function.Injective f := inclusion_injective _
  have : Function.Surjective g := e.surjective.comp f.range.mkQ_surjective
  have : Function.Exact f g := exact_iff.mpr ((e.ker_comp f.range.mkQ).trans f.range.ker_mkQ)
  rw [length_eq_add_of_exact (f.restrictScalars A) (g.restrictScalars A)
    (by simpa) (by simpa) (by simpa), Module.length_eq_of_surjective (M := ResidueField B)
      (residue_surjective (R := A)), Module.length_eq_rank]

variable (A B M) in
/-- If `B/A` is an extension of local rings, and if `M` is a `B`-module, then
`ℓ_A(M) = ℓ_B(M) * [κ(B) : κ(A)]`. -/
/-
**IsLocalRing.length_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalRing.length_restrictScalars : length A M = length B M * Module.leng
th (ResidueField A) (ResidueField B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isFiniteLength_iff_exists_compositionSeries`：isFiniteLength_iff_exists_c
ompositionSeries : IsFiniteLength R M ↔ exists s : CompositionSeries (Submodule 
R M), s.head = ⊥ ∧ s.last = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.length_compositionSeries`：Module.length_compositionSeries (s : Co
mpositionSeries (Submodule R M)) (h₁ : s.head = ⊥) (h₂ : s.last = ⊤) : s.length 
= Module.length R M
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RelSeries.head.eq_1`：∀ {α : Type u_1} {r : SetRel α α} (x : RelSeries r)
, x.head = x.toFun 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Module.length_eq_zero`：Module.length_eq_zero [Subsingleton M] : Module.l
ength R M = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_one_mul`：add_one_mul [RightDistribClass α] (a b : α) : (a + 1) * b =
 a * b + b
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `CovBy.length_restrictScalars`：CovBy.length_restrictScalars {p q : Submod
ule B M} (h : p ⋖ q) : length A q = Module.length A p + Module.length (ResidueFi
eld A) (ResidueFie…
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `Fin.val_last`：∀ (n : ℕ), ↑(Fin.last n) = n
· 使用定理 `RelSeries.last.eq_1`：∀ {α : Type u_1} {r : SetRel α α} (x : RelSeries r)
, x.last = x.toFun (Fin.last x.length)
· 使用定理 `Module.length_top`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst
_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   Module.length R ↥⊤ = Module
.length…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If `B/A` is an extension of local rings, and if `M` is a `B`-module, then
`ℓ_A(M) = ℓ_B(M) * [κ(B) : κ(A)]`.
-/
theorem IsLocalRing.length_restrictScalars :
    length A M = length B M * Module.length (ResidueField A) (ResidueField B) := by
  by_cases h : IsFiniteLength B M
  · obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
    rw [← length_compositionSeries s hs_bot hs_top]
    suffices ∀ k, length A (s k) = k * Module.length (ResidueField A) (ResidueField B) by
      rw [← Fin.val_last s.length, ← this, ← RelSeries.last, hs_top]
      exact length_top.symm
    intro k
    induction k using Fin.induction with
    | zero => rw [← RelSeries.head, hs_bot]; simp
    | succ i hi => simpa [hi, add_one_mul] using (s.step i).length_restrictScalars A
  · have : ¬ IsFiniteLength A M := by
      contrapose! h
      rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
      exact h.imp (isNoetherian_of_tower A) (isArtinian_of_tower A)
    rw [← length_ne_top_iff, not_ne_iff] at h this
    have ne : length (ResidueField A) (ResidueField B) ≠ 0 := by
      simpa [pos_iff_ne_zero] using Module.length_pos
    rw [h, this, ENat.top_mul ne]

end tower

section flat

variable [Flat A B]

variable (B) in
/-
**CovBy.length_baseChange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CovBy.length_baseChange {p q : Submodule A M} (h : p ⋖ q) : length B (q.ba
seChange B) = length B (p.baseChange B) + length B (B ⧸ (maximalIdeal A).map (al
gebraMap A B))
参数：h : p ⋖ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearEquiv.length_eq`：LinearEquiv.length_eq {N : Type*} [AddCommGroup N
] [Module R N] (e : M ≃ₗ[R] N) : Module.length R M = Module.length R N
· 使用定理 `CovBy.le`：CovBy.le (h : a ⋖ b) : a <= b
· 使用定理 `Submodule.range_inclusion`：range_inclusion (p q : Submodule R M) (h : p 
<= q) : range (inclusion h) = comap q.subtype p
· 使用定理 `covBy_iff_quot_is_simple`：covBy_iff_quot_is_simple {A B : Submodule R M}
 (hAB : A <= B) : A ⋖ B ↔ IsSimpleModule R (B ⧸ Submodule.comap B.subtype A)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSimpleModule_iff_quot_maximal`：isSimpleModule_iff_quot_maximal : IsSim
pleModule R M ↔ exists I : Ideal R, I.IsMaximal ∧ Nonempty (M ≃ₗ[R] R ⧸ I)
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.ker_comp`：ker_comp (l : M ->ₛₗ[σ₁₂] M₂) : LinearMap.ker (((e
'' : M₂ ->ₛₗ[σ₂₃] M₃).comp l : M ->ₛₗ[σ₁₃] M₃) : M ->ₛₗ[σ₁₃] M₃) = LinearMap.ker
 l
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Module.FaithfullyFlat.of_flat_of_isLocalHom`：Module.FaithfullyFlat.of_fl
at_of_isLocalHom [IsLocalRing A] [IsLocalRing B] [Flat A B] [IsLocalHom (algebra
Map A B)] : Module.FaithfullyFlat…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Module.length_eq_add_of_exact`：Module.length_eq_add_of_exact : Module.le
ngth R M = Module.length R N + Module.length R P
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
-/
theorem CovBy.length_baseChange {p q : Submodule A M} (h : p ⋖ q) :
    length B (q.baseChange B) =
      length B (p.baseChange B) + length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  -- Reduce the statement to ℓ_B(B ⊗[A] p) = ℓ_B(B ⊗[A] q) + ℓ_B(B ⧸ m_A B)
  rw [← (toBaseChange.toLinearEquiv B p).length_eq, ← (toBaseChange.toLinearEquiv B q).length_eq]
  -- Identify q / p with A / m_A, so (B ⊗[A] p ⧸ B ⊗[A] q) ≃ₗ B ⧸ m_A B
  let f : p →ₗ[A] q := inclusion h.le
  have key : IsSimpleModule A (q ⧸ f.range) := by
    rwa [range_inclusion, ← covBy_iff_quot_is_simple h.le]
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
  obtain rfl := eq_maximalIdeal hm
  -- `0 -> B ⊗[A] p -> B ⊗[A] q -> B ⧸ m_A B -> 0` is exact by flatness, and length is additive
  let g := e.comp f.range.mkQ
  have : Function.Injective f := inclusion_injective _
  have : Function.Surjective g := e.surjective.comp f.range.mkQ_surjective
  have : Function.Exact f g := exact_iff.mpr (by simp [f, g])
  have : FaithfullyFlat A B := FaithfullyFlat.of_flat_of_isLocalHom
  rw [length_eq_add_of_exact (lTensor B B f) (lTensor B B g) (by simpa) (by simpa) (by simpa),
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).toLinearEquiv.length_eq]

variable (A B M) in
/-- If `B/A` is a flat extension of local rings, and if `M` is an `A`-module, then
`ℓ_B(B ⊗[A] M) = ℓ_A(M) * ℓ_B(B ⧸ m_A)`. -/
/-
**IsLocalRing.length_baseChange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalRing.length_baseChange : length B (B otimes[A] M) = length A M * le
ngth B (B ⧸ (maximalIdeal A).map (algebraMap A B))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isFiniteLength_iff_exists_compositionSeries`：isFiniteLength_iff_exists_c
ompositionSeries : IsFiniteLength R M ↔ exists s : CompositionSeries (Submodule 
R M), s.head = ⊥ ∧ s.last = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.length_compositionSeries`：Module.length_compositionSeries (s : Co
mpositionSeries (Submodule R M)) (h₁ : s.head = ⊥) (h₂ : s.last = ⊤) : s.length 
= Module.length R M
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RelSeries.head.eq_1`：∀ {α : Type u_1} {r : SetRel α α} (x : RelSeries r)
, x.head = x.toFun 0
· 使用引理 `Submodule.baseChange_bot`：baseChange_bot : (⊥ : Submodule R M).baseChang
e A = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Module.length_eq_zero`：Module.length_eq_zero [Subsingleton M] : Module.l
ength R M = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_one_mul`：add_one_mul [RightDistribClass α] (a b : α) : (a + 1) * b =
 a * b + b
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `CovBy.length_baseChange`：CovBy.length_baseChange {p q : Submodule A M} (
h : p ⋖ q) : length B (q.baseChange B) = length B (p.baseChange B) + length B (B
 ⧸ (maximalId…
· 使用定理 `RelSeries.step`：∀ {α : Type u_1} {r : SetRel α α} (self : RelSeries r) (
i : Fin self.length),   (self.toFun i.castSucc, self.toFun i.succ) ∈ r
· 使用定理 `Fin.val_last`：∀ (n : ℕ), ↑(Fin.last n) = n
· 使用定理 `RelSeries.last.eq_1`：∀ {α : Type u_1} {r : SetRel α α} (x : RelSeries r)
, x.last = x.toFun (Fin.last x.length)
· 使用引理 `Submodule.baseChange_top`：baseChange_top : (⊤ : Submodule R M).baseChang
e A = ⊤
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
If `B/A` is a flat extension of local rings, and if `M` is an `A`-module, then
`ℓ_B(B ⊗[A] M) = ℓ_A(M) * ℓ_B(B ⧸ m_A)`.
-/
theorem IsLocalRing.length_baseChange :
    length B (B ⊗[A] M) = length A M * length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  by_cases h : IsFiniteLength A M
  · obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
    rw [← length_compositionSeries s hs_bot hs_top]
    suffices ∀ k, length B ((s k).baseChange B) =
        k * length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) by
      rw [← Fin.val_last s.length, ← this, ← RelSeries.last, hs_top, baseChange_top, length_top]
    intro k
    induction k using Fin.induction with
    | zero => rw [← RelSeries.head, hs_bot, baseChange_bot]; simp
    | succ i hi => simpa [hi, add_one_mul] using (s.step i).length_baseChange B
  · have : ¬ IsFiniteLength B (B ⊗[A] M) := by
      contrapose! h
      rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
      have : FaithfullyFlat A B := FaithfullyFlat.of_flat_of_isLocalHom
      exact h.imp IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
        IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat
    rw [← length_ne_top_iff, not_ne_iff] at h this
    have ne : length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) ≠ 0 := by
      simpa [← pos_iff_ne_zero, length_pos_iff] using (map_maximalIdeal_lt_top (algebraMap A B)).ne
    rw [h, this, ENat.top_mul ne]

end flat

