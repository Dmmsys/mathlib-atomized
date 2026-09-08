/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Primitive Element Theorem

In this file we prove the primitive element theorem.

## Main results

- `Field.exists_primitive_element`: a finite separable extension `E / F` has a primitive element,
  i.e. there is an `α : E` such that `F⟮α⟯ = (⊤ : Subalgebra F E)`.

- `Field.exists_primitive_element_iff_finite_intermediateField`: a finite extension `E / F` has a
  primitive element if and only if there exist only finitely many intermediate fields between `E`
  and `F`.

## Implementation notes

In declaration names, `primitive_element` abbreviates `adjoin_simple_eq_top`:
it stands for the statement `F⟮α⟯ = (⊤ : Subalgebra F E)`. We did not add an extra
declaration `IsPrimitiveElement F α := F⟮α⟯ = (⊤ : Subalgebra F E)` because this
requires more unfolding without much obvious benefit.

## Tags

primitive element, separable field extension, separable extension, intermediate field, adjoin,
exists_adjoin_simple_eq_top

-/

@[expose] public section

noncomputable section

open Module Polynomial IntermediateField

namespace Field

section PrimitiveElementFinite

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

/-! ### Primitive element theorem for finite fields -/


/-- **Primitive element theorem** assuming E is finite. -/
@[stacks 09HY "second part"]
/-
**Field.exists_primitive_element_of_finite_top** 是 Mathlib 中的一个定理，位于命名空间 `Field`
。
形式化陈述：exists_primitive_element_of_finite_top [Finite E] : exists α : E, F⟮α⟯ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `instIsCyclicUnitsOfFinite`：∀ {R : Type u_1} [inst : CommRing R] [IsDomai
n R] [Finite Rˣ], IsCyclic Rˣ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `IntermediateField.zero_mem`：∀ {K : Type u_1} {L : Type u_2} [inst : Fiel
d K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K L),   0 
∈ S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Units.val_mk0`：val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a
· 使用定理 `zpow_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : DivInvMonoid M] [inst_
1 : SetLike S M] [hSM : SubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n : ℤ…
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯

--- 原说明 ---
**Primitive element theorem** assuming E is finite.
-/
theorem exists_primitive_element_of_finite_top [Finite E] : ∃ α : E, F⟮α⟯ = ⊤ := by
  obtain ⟨α, hα⟩ := @IsCyclic.exists_generator Eˣ _ _
  use α
  rw [eq_top_iff]
  rintro x -
  by_cases hx : x = 0
  · rw [hx]
    exact F⟮α.val⟯.zero_mem
  · obtain ⟨n, hn⟩ := Set.mem_range.mp (hα (Units.mk0 x hx))
    rw [show x = α ^ n by norm_cast; rw [hn, Units.val_mk0]]
    exact zpow_mem (mem_adjoin_simple_self F (E := E) ↑α) n

/-- Primitive element theorem for finite-dimensional extension of a finite field. -/
/-
**Field.exists_primitive_element_of_finite_bot** 是 Mathlib 中的一个定理，位于命名空间 `Field`
。
形式化陈述：exists_primitive_element_of_finite_bot [Finite F] [FiniteDimensional F E] 
: exists α : E, F⟮α⟯ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.exists_primitive_element_of_finite_top`：exists_primitive_element_o
f_finite_top [Finite E] : exists α : E, F⟮α⟯ = ⊤
· 使用定理 `Module.finite_of_finite`：∀ (R : Type u_1) {M : Type u_2} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite R]   [Modul
e.Finite R M]…

--- 原说明 ---
Primitive element theorem for finite-dimensional extension of a finite field.
-/
theorem exists_primitive_element_of_finite_bot [Finite F] [FiniteDimensional F E] :
    ∃ α : E, F⟮α⟯ = ⊤ :=
  haveI : Finite E := Module.finite_of_finite F
  exists_primitive_element_of_finite_top F E

end PrimitiveElementFinite

/-! ### Primitive element theorem for infinite fields -/


section PrimitiveElementInf

variable {F : Type*} [Field F] [Infinite F] {E : Type*} [Field E] (ϕ : F →+* E) (α β : E)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Field.primitive_element_inf_aux_exists_c** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：primitive_element_inf_aux_exists_c (f g : F[X]) : exists c : F, forall α' 
in (f.map ϕ).roots, forall β' in (g.map ϕ).roots, -(α' - α) / (β' - β) != ϕ c
参数：f g : F[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Infinite.exists_notMem_finset`：exists_notMem_finset [Infinite α] (s : Fi
nset α) : exists x, x ∉ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem primitive_element_inf_aux_exists_c (f g : F[X]) :
    ∃ c : F, ∀ α' ∈ (f.map ϕ).roots, ∀ β' ∈ (g.map ϕ).roots, -(α' - α) / (β' - β) ≠ ϕ c := by
  let sf := (f.map ϕ).roots
  let sg := (g.map ϕ).roots
  classical
  let s := (sf.bind fun α' => sg.map fun β' => -(α' - α) / (β' - β)).toFinset
  let s' := s.preimage ϕ fun x _ y _ h => ϕ.injective h
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset s'
  simp_rw [s', s, Finset.mem_preimage, Multiset.mem_toFinset, Multiset.mem_bind, Multiset.mem_map]
    at hc
  push Not at hc
  exact ⟨c, hc⟩

variable (F)
variable [Algebra F E]

/-- This is the heart of the proof of the primitive element theorem. It shows that if `F` is
infinite and `α` and `β` are separable over `F` then `F⟮α, β⟯` is generated by a single element. -/
/-
**Field.primitive_element_inf_aux** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：primitive_element_inf_aux [Algebra.IsSeparable F E] : exists γ : E, F⟮α, β
⟯ = F⟮γ⟯
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsSeparable.isIntegral`：Algebra.IsSeparable.isIntegral [Algebra.
IsSeparable F K] : forall x : K, IsIntegral F x
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Field.primitive_element_inf_aux_exists_c`：primitive_element_inf_aux_exis
ts_c (f g : F[X]) : exists c : F, forall α' in (f.map ϕ).roots, forall β' in (g.
map ϕ).roots, -(α' - α) / (β' …
· 使用定理 `IntermediateField.adjoin.algebraMap_mem`：∀ (F : Type u_1) [inst : Field 
F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (S : Set E) (x : F),
   (algebraMap F E) x ∈ Inter…
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanDomain.gcd_eq_zero_iff`：∀ {R : Type u} [inst : EuclideanDomain 
R] [inst_1 : DecidableEq R] {a b : R},   EuclideanDomain.gcd a b = 0 ↔ a = 0 ∧ b
 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Polynomial.separable_gcd_right`：separable_gcd_right {F : Type*} [Field F
] [DecidableEq F[X]] {g : F[X]} (f : F[X]) (hg : g.Separable) : (EuclideanDomain
.gcd f g).Separable
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `Polynomial.eval_gcd_eq_zero`：eval_gcd_eq_zero [DecidableEq R] {f g : R[X
]} {α : R} (hf : f.eval α = 0) (hg : g.eval α = 0) : (EuclideanDomain.gcd f g).e
val α = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
（共 132 条，此处仅展示前 30 条）

--- 原说明 ---
This is the heart of the proof of the primitive element theorem. It shows that i
f `F` is
infinite and `α` and `β` are separable over `F` then `F⟮α, β⟯` is generated by a
 single element.
-/
theorem primitive_element_inf_aux [Algebra.IsSeparable F E] : ∃ γ : E, F⟮α, β⟯ = F⟮γ⟯ := by
  have hα := Algebra.IsSeparable.isIntegral F α
  have hβ := Algebra.IsSeparable.isIntegral F β
  let f := minpoly F α
  let g := minpoly F β
  let ιFE := algebraMap F E
  let ιEE' := algebraMap E (SplittingField (g.map ιFE))
  obtain ⟨c, hc⟩ := primitive_element_inf_aux_exists_c (ιEE'.comp ιFE) (ιEE' α) (ιEE' β) f g
  let γ := α + c • β
  suffices β_in_Fγ : β ∈ F⟮γ⟯ by
    use γ
    apply le_antisymm
    · rw [adjoin_le_iff]
      have α_in_Fγ : α ∈ F⟮γ⟯ := by
        rw [← add_sub_cancel_right α (c • β)]
        exact F⟮γ⟯.sub_mem (mem_adjoin_simple_self F γ) (F⟮γ⟯.toSubalgebra.smul_mem β_in_Fγ c)
      rintro x (rfl | rfl) <;> assumption
    · rw [adjoin_simple_le_iff]
      have α_in_Fαβ : α ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert α {β})
      have β_in_Fαβ : β ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert_of_mem α rfl)
      exact F⟮α, β⟯.add_mem α_in_Fαβ (F⟮α, β⟯.smul_mem β_in_Fαβ)
  classical
  let p := EuclideanDomain.gcd ((f.map (algebraMap F F⟮γ⟯)).comp
    (C (AdjoinSimple.gen F γ) - (C ↑c : F⟮γ⟯[X]) * X)) (g.map (algebraMap F F⟮γ⟯))
  let h := EuclideanDomain.gcd ((f.map ιFE).comp (C γ - C (ιFE c) * X)) (g.map ιFE)
  have map_g_ne_zero : g.map ιFE ≠ 0 := map_ne_zero (minpoly.ne_zero hβ)
  have h_ne_zero : h ≠ 0 :=
    mt EuclideanDomain.gcd_eq_zero_iff.mp (not_and.mpr fun _ => map_g_ne_zero)
  suffices p_linear : p.map (algebraMap F⟮γ⟯ E) = C h.leadingCoeff * (X - C β) by
    have finale : β = algebraMap F⟮γ⟯ E (-p.coeff 0 / p.coeff 1) := by
      simp [map_div₀, map_neg, ← coeff_map, ← coeff_map, p_linear,
        mul_sub, coeff_C, mul_div_cancel_left₀ β (mt leadingCoeff_eq_zero.mp h_ne_zero)]
    rw [finale]
    exact Subtype.mem (-p.coeff 0 / p.coeff 1)
  have h_sep : h.Separable := separable_gcd_right _ (.map (Algebra.IsSeparable.isSeparable F β))
  have h_root : h.eval β = 0 := by
    apply eval_gcd_eq_zero
    · rw [eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X, eval_map_algebraMap, ←
        Algebra.smul_def, add_sub_cancel_right, minpoly.aeval]
    · rw [eval_map_algebraMap, minpoly.aeval]
  have h_splits : Splits (h.map ιEE') := by
    rw [← Polynomial.gcd_map]
    exact (SplittingField.splits _).of_dvd (map_ne_zero map_g_ne_zero)
      (EuclideanDomain.gcd_dvd_right _ _)
  have h_roots : ∀ x ∈ (h.map ιEE').roots, x = ιEE' β := by
    intro x hx
    rw [mem_roots_map h_ne_zero] at hx
    specialize hc (ιEE' γ - ιEE' (ιFE c) * x) (by
      have f_root := root_left_of_root_gcd hx
      rw [eval₂_comp, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eval₂_map] at f_root
      exact (mem_roots_map (minpoly.ne_zero hα)).mpr f_root)
    specialize hc x (by
      rw [mem_roots_map (minpoly.ne_zero hβ), ← eval₂_map]
      exact root_right_of_root_gcd hx)
    by_contra a
    apply hc
    apply (div_eq_iff (sub_ne_zero.mpr a)).mpr
    simp only [γ, Algebra.smul_def, map_add, map_mul, RingHom.comp_apply]
    ring
  rw [← eq_X_sub_C_of_separable_of_root_eq h_sep h_root h_splits h_roots]
  trans EuclideanDomain.gcd (?_ : E[X]) (?_ : E[X])
  · dsimp only [γ]
    convert! (gcd_map (algebraMap F⟮γ⟯ E)).symm
  · simp only [map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.map_sub,
      map_C, AdjoinSimple.algebraMap_gen, Polynomial.map_mul, map_X]
    congr

-- If `F` is infinite and `E/F` has only finitely many intermediate fields, then for any
-- `α` and `β` in `E`, `F⟮α, β⟯` is generated by a single element.
-- Marked as private since it's a special case of
-- `exists_primitive_element_of_finite_intermediateField`.
/-
**Field.primitive_element_inf_aux_of_finite_intermediateField** 是 Mathlib 中的一个定理
，位于命名空间 `Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem primitive_element_inf_aux_of_finite_intermediateField
    [Finite (IntermediateField F E)] : ∃ γ : E, F⟮α, β⟯ = F⟮γ⟯ := by
  let f : F → IntermediateField F E := fun x ↦ F⟮α + x • β⟯
  obtain ⟨x, y, hneq, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  use α + x • β
  apply le_antisymm
  · rw [adjoin_le_iff]
    have αxβ_in_K : α + x • β ∈ F⟮α + x • β⟯ := mem_adjoin_simple_self F _
    have αyβ_in_K : α + y • β ∈ F⟮α + y • β⟯ := mem_adjoin_simple_self F _
    dsimp [f] at *
    simp only [← heq] at αyβ_in_K
    have β_in_K := sub_mem αxβ_in_K αyβ_in_K
    rw [show (α + x • β) - (α + y • β) = (x - y) • β by rw [sub_smul]; abel1] at β_in_K
    replace β_in_K := smul_mem _ β_in_K (x := (x - y)⁻¹)
    rw [smul_smul, inv_mul_eq_div, div_self (sub_ne_zero.2 hneq), one_smul] at β_in_K
    have α_in_K : α ∈ F⟮α + x • β⟯ := by
      convert! ← sub_mem αxβ_in_K (smul_mem _ β_in_K)
      apply add_sub_cancel_right
    rintro x (rfl | rfl) <;> assumption
  · rw [adjoin_simple_le_iff]
    have α_in_Fαβ : α ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert α {β})
    have β_in_Fαβ : β ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert_of_mem α rfl)
    exact F⟮α, β⟯.add_mem α_in_Fαβ (F⟮α, β⟯.smul_mem β_in_Fαβ)

end PrimitiveElementInf

variable (F E : Type*) [Field F] [Field E]
variable [Algebra F E]

section SeparableAssumption

variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- **Primitive element theorem**: a finite separable field extension `E` of `F` has a
  primitive element, i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : Subalgebra F E)`. -/
@[stacks 030N "The moreover part"]
/-
**Field.exists_primitive_element** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：exists_primitive_element : exists α : E, F⟮α⟯ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `IntermediateField.adjoin_zero`：adjoin_zero : F⟮(0 : E)⟯ = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin_simple_adjoin_simple`：adjoin_simple_adjoin_simp
le (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮α, β⟯
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isEmpty_fintype`：isEmpty_fintype {α : Type*} : IsEmpty (Fintype α) ↔ Inf
inite α
· 使用定理 `Field.primitive_element_inf_aux`：primitive_element_inf_aux [Algebra.IsSe
parable F E] : exists γ : E, F⟮α, β⟯ = F⟮γ⟯
· 使用定理 `IntermediateField.induction_on_adjoin`：induction_on_adjoin [FiniteDimens
ional F E] (P : IntermediateField F E -> Prop) (base : P ⊥) (ih : forall (K : In
termediateField F E) (x : E…
· 使用定理 `Field.exists_primitive_element_of_finite_bot`：exists_primitive_element_o
f_finite_bot [Finite F] [FiniteDimensional F E] : exists α : E, F⟮α⟯ = ⊤
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
**Primitive element theorem**: a finite separable field extension `E` of `F` has
 a
  primitive element, i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : Subalgebra 
F E)`.
-/
theorem exists_primitive_element : ∃ α : E, F⟮α⟯ = ⊤ := by
  rcases isEmpty_or_nonempty (Fintype F) with (F_inf | ⟨⟨F_finite⟩⟩)
  · let P : IntermediateField F E → Prop := fun K => ∃ α : E, F⟮α⟯ = K
    have base : P ⊥ := ⟨0, adjoin_zero⟩
    have ih : ∀ (K : IntermediateField F E) (x : E), P K → P (K⟮x⟯.restrictScalars F) := by
      intro K β hK
      obtain ⟨α, hK⟩ := hK
      rw [← hK, adjoin_simple_adjoin_simple]
      have : Infinite F := isEmpty_fintype.mp F_inf
      obtain ⟨γ, hγ⟩ := primitive_element_inf_aux F α β
      exact ⟨γ, hγ.symm⟩
    exact induction_on_adjoin P base ih ⊤
  · exact exists_primitive_element_of_finite_bot F E

/-- Alternative phrasing of primitive element theorem:
a finite separable field extension has a basis `1, α, α^2, ..., α^n`.

See also `exists_primitive_element`. -/
/-
**Field.powerBasisOfFiniteOfSeparable** 是 Mathlib 中的一个定义，位于命名空间 `Field`。
形式化陈述：powerBasisOfFiniteOfSeparable : PowerBasis F E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Field.exists_primitive_element`：exists_primitive_element : exists α : E,
 F⟮α⟯ = ⊤

--- 原说明 ---
Alternative phrasing of primitive element theorem:
a finite separable field extension has a basis `1, α, α^2, ..., α^n`.

See also `exists_primitive_element`.
-/
noncomputable def powerBasisOfFiniteOfSeparable : PowerBasis F E :=
  let α := (exists_primitive_element F E).choose
  let pb := adjoin.powerBasis (Algebra.IsSeparable.isIntegral F α)
  have e : F⟮α⟯ = ⊤ := (exists_primitive_element F E).choose_spec
  pb.map ((IntermediateField.equivOfEq e).trans IntermediateField.topEquiv)

end SeparableAssumption

section FiniteIntermediateField

-- TODO: show a more generalized result: [F⟮α⟯ : F⟮α ^ m⟯] = m if m > 0 and α transcendental.
/-
**Field.isAlgebraic_of_adjoin_eq_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：isAlgebraic_of_adjoin_eq_adjoin {α : E} {m n : Nat} (hneq : m != n) (heq :
 F⟮α ^ m⟯ = F⟮α ^ n⟯) : IsAlgebraic F α
参数：hneq : m != n；heq : F⟮α ^ m⟯ = F⟮α ^ n⟯。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.mem_bot`：mem_bot {x : E} : x in (⊥ : IntermediateField
 F E) ↔ x in Set.range (algebraMap F E)
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `IntermediateField.adjoin_one`：adjoin_one : F⟮(1 : E)⟯ = ⊥
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IntermediateField.mem_adjoin_simple_iff`：mem_adjoin_simple_iff {α : E} (
x : E) : x in adjoin F {α} ↔ exists r s : F[X], x = aeval α r / aeval α s
· 使用定理 `isAlgebraic_zero`：isAlgebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A
)
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
（共 104 条，此处仅展示前 30 条）
-/
theorem isAlgebraic_of_adjoin_eq_adjoin {α : E} {m n : ℕ} (hneq : m ≠ n)
    (heq : F⟮α ^ m⟯ = F⟮α ^ n⟯) : IsAlgebraic F α := by
  wlog hmn : m < n
  · exact this F E hneq.symm heq.symm (hneq.lt_or_gt.resolve_left hmn)
  by_cases hm : m = 0
  · rw [hm] at heq hmn
    simp only [pow_zero, adjoin_one] at heq
    obtain ⟨y, h⟩ := mem_bot.1 (heq.symm ▸ mem_adjoin_simple_self F (α ^ n))
    refine ⟨X ^ n - C y, X_pow_sub_C_ne_zero hmn y, ?_⟩
    simp only [map_sub, map_pow, aeval_X, aeval_C, h, sub_self]
  obtain ⟨r, s, h⟩ := (mem_adjoin_simple_iff F _).1 (heq ▸ mem_adjoin_simple_self F (α ^ m))
  by_cases hzero : aeval (α ^ n) s = 0
  · simp only [hzero, div_zero, pow_eq_zero_iff hm] at h
    exact h.symm ▸ isAlgebraic_zero
  replace hm : 0 < m := Nat.pos_of_ne_zero hm
  rw [eq_div_iff hzero, ← sub_eq_zero] at h
  replace hzero : s ≠ 0 := by rintro rfl; simp only [map_zero, not_true_eq_false] at hzero
  let f : F[X] := X ^ m * expand F n s - expand F n r
  refine ⟨f, ?_, ?_⟩
  · have : f.coeff (n * s.natDegree + m) ≠ 0 := by
      have hn : 0 < n := by linarith only [hm, hmn]
      have hndvd : ¬ n ∣ n * s.natDegree + m := by
        rw [← Nat.dvd_add_iff_right (n.dvd_mul_right s.natDegree)]
        exact Nat.not_dvd_of_pos_of_lt hm hmn
      simp only [f, coeff_sub, coeff_X_pow_mul, s.coeff_expand_mul' hn, coeff_natDegree,
        coeff_expand hn r, hndvd, ite_false, sub_zero]
      exact leadingCoeff_ne_zero.2 hzero
    intro h
    simp only [h, coeff_zero, ne_eq, not_true_eq_false] at this
  · simp only [f, map_sub, map_mul, map_pow, aeval_X, expand_aeval, h]
/-
**Field.isAlgebraic_of_finite_intermediateField** 是 Mathlib 中的一个定理，位于命名空间 `Field
`。
形式化陈述：isAlgebraic_of_finite_intermediateField [Finite (IntermediateField F E)] :
 Algebra.IsAlgebraic F E
参数：IntermediateField F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_ne_map_eq_of_infinite`：Finite.exists_ne_map_eq_of_infinite
 {α β} [Infinite α] [Finite β] (f : α -> β) : exists x y : α, x != y ∧ f x = f y
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Field.isAlgebraic_of_adjoin_eq_adjoin`：isAlgebraic_of_adjoin_eq_adjoin {
α : E} {m n : Nat} (hneq : m != n) (heq : F⟮α ^ m⟯ = F⟮α ^ n⟯) : IsAlgebraic F α
-/
theorem isAlgebraic_of_finite_intermediateField
    [Finite (IntermediateField F E)] : Algebra.IsAlgebraic F E := ⟨fun α ↦
  have ⟨_m, _n, hneq, heq⟩ := Finite.exists_ne_map_eq_of_infinite fun n ↦ F⟮α ^ n⟯
  isAlgebraic_of_adjoin_eq_adjoin F E hneq heq⟩
/-
**Field.FiniteDimensional.of_finite_intermediateField** 是 Mathlib 中的一个定理，位于命名空间 
`Field.FiniteDimensional`。
形式化陈述：∀ (F : Type u_1) (E : Type u_2) [inst : Field F] [inst_1 : Field E] [inst_
2 : Algebra F E]   [Finite (IntermediateField F E)], FiniteDimensional F E
参数：F : Type u_1；E : Type u_2；IntermediateField F E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.isAlgebraic_of_finite_intermediateField`：isAlgebraic_of_finite_int
ermediateField [Finite (IntermediateField F E)] : Algebra.IsAlgebraic F E
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem FiniteDimensional.of_finite_intermediateField
    [Finite (IntermediateField F E)] : FiniteDimensional F E := by
  let IF := { K : IntermediateField F E // ∃ x, K = F⟮x⟯ }
  have := isAlgebraic_of_finite_intermediateField F E
  have : ∀ K : IF, FiniteDimensional F K.1 := fun ⟨_, x, rfl⟩ ↦ adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral _)
  have hfin := finiteDimensional_iSup_of_finite (t := fun K : IF ↦ K.1)
  have htop : ⨆ K : IF, K.1 = ⊤ := le_top.antisymm fun x _ ↦
    le_iSup (fun K : IF ↦ K.1) ⟨F⟮x⟯, x, rfl⟩ <| mem_adjoin_simple_self F x
  rw [htop] at hfin
  exact topEquiv.toLinearEquiv.finiteDimensional
/-
**Field.exists_primitive_element_of_finite_intermediateField** 是 Mathlib 中的一个定理，
位于命名空间 `Field`。
形式化陈述：exists_primitive_element_of_finite_intermediateField [Finite (Intermediate
Field F E)] (K : IntermediateField F E) : exists α : E, F⟮α⟯ = K
参数：IntermediateField F E；K : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.FiniteDimensional.of_finite_intermediateField`：∀ (F : Type u_1) (E
 : Type u_2) [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E]   [Finit
e (IntermediateField F E)], FiniteDimensi…
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Field.exists_primitive_element_of_finite_bot`：exists_primitive_element_o
f_finite_bot [Finite F] [FiniteDimensional F E] : exists α : E, F⟮α⟯ = ⊤
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.lift_adjoin_simple`：lift_adjoin_simple (K : Intermedia
teField F E) (α : K) : lift (adjoin F {α}) = adjoin F {α.1}
· 使用定理 `IntermediateField.lift_top`：lift_top (K : IntermediateField F E) : lift 
(F
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IntermediateField.induction_on_adjoin`：induction_on_adjoin [FiniteDimens
ional F E] (P : IntermediateField F E -> Prop) (base : P ⊥) (ih : forall (K : In
termediateField F E) (x : E…
· 使用定理 `IntermediateField.adjoin_zero`：adjoin_zero : F⟮(0 : E)⟯ = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IntermediateField.adjoin_simple_adjoin_simple`：adjoin_simple_adjoin_simp
le (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮α, β⟯
· 使用定理 `_private.Mathlib.FieldTheory.PrimitiveElement.0.Field.primitive_element_
inf_aux_of_finite_intermediateField`：∀ (F : Type u_1) [inst : Field F] [Infinite
 F] {E : Type u_2} [inst_2 : Field E] (α β : E) [inst_3 : Algebra F E]   [Finite
 (IntermediateFie…
-/
theorem exists_primitive_element_of_finite_intermediateField
    [Finite (IntermediateField F E)] (K : IntermediateField F E) : ∃ α : E, F⟮α⟯ = K := by
  have := FiniteDimensional.of_finite_intermediateField F E
  rcases finite_or_infinite F with (_ | _)
  · obtain ⟨α, h⟩ := exists_primitive_element_of_finite_bot F K
    exact ⟨α, by simpa only [lift_adjoin_simple, lift_top] using congr_arg lift h⟩
  · apply induction_on_adjoin (fun K ↦ ∃ α : E, F⟮α⟯ = K) ⟨0, adjoin_zero⟩
    rintro K β ⟨α, rfl⟩
    simp_rw [adjoin_simple_adjoin_simple, eq_comm]
    exact primitive_element_inf_aux_of_finite_intermediateField F α β
/-
**Field.FiniteDimensional.of_exists_primitive_element** 是 Mathlib 中的一个定理，位于命名空间 
`Field.FiniteDimensional`。
形式化陈述：∀ (F : Type u_1) (E : Type u_2) [inst : Field F] [inst_1 : Field E] [inst_
2 : Algebra F E] [Algebra.IsAlgebraic F E],   (∃ α, F⟮α⟯ = ⊤) → FiniteDimensiona
l F E
参数：F : Type u_1；E : Type u_2；∃ α, F⟮α⟯ = ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem FiniteDimensional.of_exists_primitive_element [Algebra.IsAlgebraic F E]
    (h : ∃ α : E, F⟮α⟯ = ⊤) : FiniteDimensional F E := by
  obtain ⟨α, hprim⟩ := h
  have hfin := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) α)
  rw [hprim] at hfin
  exact topEquiv.toLinearEquiv.finiteDimensional

-- A finite simple extension has only finitely many intermediate fields
/-
**Field.finite_intermediateField_of_exists_primitive_element** 是 Mathlib 中的一个定理，
位于命名空间 `Field`。
形式化陈述：finite_intermediateField_of_exists_primitive_element [Algebra.IsAlgebraic 
F E] (h : exists α : E, F⟮α⟯ = ⊤) : Finite (IntermediateField F E)
参数：h : exists α : E, F⟮α⟯ = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.FiniteDimensional.of_exists_primitive_element`：∀ (F : Type u_1) (E
 : Type u_2) [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] [Algebra
.IsAlgebraic F E],   (∃ α, F⟮α⟯ = ⊤) → Fi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `minpoly.ne_zero_of_finite`：ne_zero_of_finite (e : B) [FiniteDimensional 
A B] : minpoly A e != 0
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.map_dvd`：map_dvd (f : R ->+* S) {x y : R[X]} : x ∣ y -> x.map
 f ∣ y.map f
· 使用定理 `minpoly.dvd_map_of_isScalarTower`：dvd_map_of_isScalarTower (A K : Type*)
 {R : Type*} [CommRing A] [Field K] [Ring R] [Algebra A K] [Algebra A R] [Algebr
a K R] [IsScalarTower …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IntermediateField.adjoin_minpoly_coeff_of_exists_primitive_element`：adjo
in_minpoly_coeff_of_exists_primitive_element [FiniteDimensional F E] (hprim : ad
join F {α} = ⊤) (K : IntermediateField F E) : adjoin F (…
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
-/
theorem finite_intermediateField_of_exists_primitive_element [Algebra.IsAlgebraic F E]
    (h : ∃ α : E, F⟮α⟯ = ⊤) : Finite (IntermediateField F E) := by
  have := FiniteDimensional.of_exists_primitive_element F E h
  obtain ⟨α, hprim⟩ := h
  -- Let `f` be the minimal polynomial of `α ∈ E` over `F`
  let f : F[X] := minpoly F α
  let G := { g : E[X] // g.Monic ∧ g ∣ f.map (algebraMap F E) }
  -- Then `f` has only finitely many monic factors
  have hfin : Finite G := @Finite.of_fintype _ <| fintypeSubtypeMonicDvd
    (f.map (algebraMap F E)) <| map_ne_zero (minpoly.ne_zero_of_finite F α)
  -- If `K` is an intermediate field of `E/F`, let `g` be the minimal polynomial of `α` over `K`
  -- which is a monic factor of `f`
  let g : IntermediateField F E → G := fun K ↦
    ⟨(minpoly K α).map (algebraMap K E), (minpoly.monic <| .of_finite K α).map _, by
      convert! Polynomial.map_dvd (algebraMap K E) (minpoly.dvd_map_of_isScalarTower F K α)
      rw [Polynomial.map_map]; rfl⟩
  -- The map `K ↦ g` is injective
  have hinj : Function.Injective g := fun K K' heq ↦ by
    rw [Subtype.mk.injEq] at heq
    apply_fun fun f : E[X] ↦ adjoin F (f.coeffs : Set E) at heq
    simpa only [adjoin_minpoly_coeff_of_exists_primitive_element F hprim] using heq
  -- Therefore there are only finitely many intermediate fields
  exact Finite.of_injective g hinj

/-- **Steinitz theorem**: an algebraic extension `E` of `F` has a
  primitive element (i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : Subalgebra F E)`)
  if and only if there exist only finitely many intermediate fields between `E` and `F`. -/
@[stacks 030N "Equivalence of (1) & (2)"]
/-
**Field.exists_primitive_element_iff_finite_intermediateField** 是 Mathlib 中的一个定理
，位于命名空间 `Field`。
形式化陈述：exists_primitive_element_iff_finite_intermediateField : (Algebra.IsAlgebra
ic F E ∧ exists α : E, F⟮α⟯ = ⊤) ↔ Finite (IntermediateField F E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.finite_intermediateField_of_exists_primitive_element`：finite_inter
mediateField_of_exists_primitive_element [Algebra.IsAlgebraic F E] (h : exists α
 : E, F⟮α⟯ = ⊤) : Finite (IntermediateField F E)
· 使用定理 `Field.isAlgebraic_of_finite_intermediateField`：isAlgebraic_of_finite_int
ermediateField [Finite (IntermediateField F E)] : Algebra.IsAlgebraic F E
· 使用定理 `Field.exists_primitive_element_of_finite_intermediateField`：exists_primi
tive_element_of_finite_intermediateField [Finite (IntermediateField F E)] (K : I
ntermediateField F E) : exists α : E, F⟮α⟯ = K

--- 原说明 ---
**Steinitz theorem**: an algebraic extension `E` of `F` has a
  primitive element (i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : Subalgebra 
F E)`)
  if and only if there exist only finitely many intermediate fields between `E` 
and `F`.
-/
theorem exists_primitive_element_iff_finite_intermediateField :
    (Algebra.IsAlgebraic F E ∧ ∃ α : E, F⟮α⟯ = ⊤) ↔ Finite (IntermediateField F E) :=
  ⟨fun ⟨_, h⟩ ↦ finite_intermediateField_of_exists_primitive_element F E h,
    fun _ ↦ ⟨isAlgebraic_of_finite_intermediateField F E,
      exists_primitive_element_of_finite_intermediateField F E _⟩⟩

end FiniteIntermediateField

end Field

variable (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-
**AlgHom.natCard_of_splits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.natCard_of_splits (L : Type*) [Field L] [Algebra F L] (hL : forall 
x : E, ((minpoly F x).map (algebraMap F L)).Splits) : Nat.card (E ->ₐ[F] L) = fi
nrank F E
参数：L : Type*；hL : forall x : E, ((minpoly F x).map (algebraMap F L)).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.natCard_of_powerBasis`：AlgHom.natCard_of_powerBasis (pb : PowerBa
sis K S) (h_sep : IsSeparable K pb.gen) (h_splits : ((minpoly K pb.gen).map (alg
ebraMap K L)).Spli…
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerBasis.finrank`：finrank [StrongRankCondition R] (pb : PowerBasis R S
) : Module.finrank R S = pb.dim
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem AlgHom.natCard_of_splits (L : Type*) [Field L] [Algebra F L]
    (hL : ∀ x : E, ((minpoly F x).map (algebraMap F L)).Splits) :
    Nat.card (E →ₐ[F] L) = finrank F E :=
  (AlgHom.natCard_of_powerBasis (L := L) (Field.powerBasisOfFiniteOfSeparable F E)
    (Algebra.IsSeparable.isSeparable _ _) <| hL _).trans
      (PowerBasis.finrank _).symm

@[simp]
/-
**AlgHom.card_of_splits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.card_of_splits (L : Type*) [Field L] [Algebra F L] (hL : forall x :
 E, ((minpoly F x).map (algebraMap F L)).Splits) : Fintype.card (E ->ₐ[F] L) = f
inrank F E
参数：L : Type*；hL : forall x : E, ((minpoly F x).map (algebraMap F L)).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `AlgHom.natCard_of_splits`：AlgHom.natCard_of_splits (L : Type*) [Field L]
 [Algebra F L] (hL : forall x : E, ((minpoly F x).map (algebraMap F L)).Splits) 
: Nat.card (E …
-/
theorem AlgHom.card_of_splits (L : Type*) [Field L] [Algebra F L]
    (hL : ∀ x : E, ((minpoly F x).map (algebraMap F L)).Splits) :
    Fintype.card (E →ₐ[F] L) = finrank F E := by
  rw [Fintype.card_eq_nat_card, AlgHom.natCard_of_splits F E L hL]

@[simp]
/-
**AlgHom.card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.card (K : Type*) [Field K] [IsAlgClosed K] [Algebra F K] : Fintype.
card (E ->ₐ[F] K) = finrank F E
参数：K : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.card_of_splits`：AlgHom.card_of_splits (L : Type*) [Field L] [Alge
bra F L] (hL : forall x : E, ((minpoly F x).map (algebraMap F L)).Splits) : Fint
ype.card (E…
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
-/
theorem AlgHom.card (K : Type*) [Field K] [IsAlgClosed K] [Algebra F K] :
    Fintype.card (E →ₐ[F] K) = finrank F E :=
  AlgHom.card_of_splits _ _ _ (fun _ ↦ IsAlgClosed.splits _)

section iff

namespace Field

open Module IntermediateField Polynomial Algebra Set

variable (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/-
**Field.primitive_element_iff_minpoly_natDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fi
eld`。
形式化陈述：primitive_element_iff_minpoly_natDegree_eq (α : E) : F⟮α⟯ = ⊤ ↔ (minpoly F
 α).natDegree = finrank F E
参数：α : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin.finrank`：∀ {K : Type u} [inst : Field K] {L : T
ype u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegral K x → M
odule.finrank K ↥K⟮x⟯ …
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IntermediateField.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq [Finite
Dimensional K E] (h_le : F <= E) (h_finrank : finrank K F = finrank K E) : F = E
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem primitive_element_iff_minpoly_natDegree_eq (α : E) :
    F⟮α⟯ = ⊤ ↔ (minpoly F α).natDegree = finrank F E := by
  rw [← adjoin.finrank (IsIntegral.of_finite F α), ← finrank_top F E]
  refine ⟨fun h => ?_, fun h => eq_of_le_of_finrank_eq le_top h⟩
  exact congr_arg (fun K : IntermediateField F E => finrank F K) h
/-
**Field.primitive_element_iff_minpoly_degree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Field
`。
形式化陈述：primitive_element_iff_minpoly_degree_eq (α : E) : F⟮α⟯ = ⊤ ↔ (minpoly F α)
.degree = finrank F E
参数：α : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_iff_natDegree_eq`：degree_eq_iff_natDegree_eq {p : R
[X]} {n : Nat} (hp : p != 0) : p.degree = n ↔ p.natDegree = n
· 使用定理 `minpoly.ne_zero_of_finite`：ne_zero_of_finite (e : B) [FiniteDimensional 
A B] : minpoly A e != 0
· 使用定理 `Field.primitive_element_iff_minpoly_natDegree_eq`：primitive_element_iff_
minpoly_natDegree_eq (α : E) : F⟮α⟯ = ⊤ ↔ (minpoly F α).natDegree = finrank F E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem primitive_element_iff_minpoly_degree_eq (α : E) :
    F⟮α⟯ = ⊤ ↔ (minpoly F α).degree = finrank F E := by
  rw [degree_eq_iff_natDegree_eq, primitive_element_iff_minpoly_natDegree_eq]
  exact minpoly.ne_zero_of_finite F α

variable [Algebra.IsSeparable F E] (A : Type*) [Field A] [Algebra F A]
  (hA : ∀ x : E, ((minpoly F x).map (algebraMap F A)).Splits)
include hA
/-
**Field.primitive_element_iff_algHom_eq_of_eval'** 是 Mathlib 中的一个定理，位于命名空间 `Fiel
d`。
形式化陈述：primitive_element_iff_algHom_eq_of_eval' (α : E) : F⟮α⟯ = ⊤ ↔ Function.Inj
ective fun φ : E ->ₐ[F] A => φ α
参数：α : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.card_rootSet_eq_natDegree`：card_rootSet_eq_natDegree [Algebra
 F K] {p : F[X]} (hsep : p.Separable) (hsplit : Splits (p.map (algebraMap F K)))
 : Fintype.card (p.rootSet…
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits`：Algebra.IsA
lgebraic.range_eval_eq_rootSet_minpoly_of_splits {F K : Type*} (L : Type*) [Fiel
d F] [Field K] [Field L] [Algebra F L] [Algebra F…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `AlgHom.card_of_splits`：AlgHom.card_of_splits (L : Type*) [Field L] [Alge
bra F L] (hL : forall x : E, ((minpoly F x).map (algebraMap F L)).Splits) : Fint
ype.card (E…
· 使用定理 `Set.toFinset_range`：toFinset_range [DecidableEq α] [Fintype β] (f : β ->
 α) [Fintype (Set.range f)] : (Set.range f).toFinset = Finset.univ.image f
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem primitive_element_iff_algHom_eq_of_eval' (α : E) :
    F⟮α⟯ = ⊤ ↔ Function.Injective fun φ : E →ₐ[F] A ↦ φ α := by
  classical
  simp_rw [primitive_element_iff_minpoly_natDegree_eq, ← card_rootSet_eq_natDegree (K := A)
    (Algebra.IsSeparable.isSeparable F α) (hA _), ← toFinset_card,
    ← (Algebra.IsAlgebraic.of_finite F E).range_eval_eq_rootSet_minpoly_of_splits _ hA α,
    ← AlgHom.card_of_splits F E A hA, Fintype.card, toFinset_range, Finset.card_image_iff,
    Finset.coe_univ, injOn_univ]
/-
**Field.primitive_element_iff_algHom_eq_of_eval** 是 Mathlib 中的一个定理，位于命名空间 `Field
`。
形式化陈述：primitive_element_iff_algHom_eq_of_eval (α : E) (φ : E ->ₐ[F] A) : F⟮α⟯ = 
⊤ ↔ forall ψ : E ->ₐ[F] A, φ α = ψ α -> φ = ψ
参数：α : E；φ : E ->ₐ[F] A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Field.primitive_element_iff_algHom_eq_of_eval'`：primitive_element_iff_al
gHom_eq_of_eval' (α : E) : F⟮α⟯ = ⊤ ↔ Function.Injective fun φ : E ->ₐ[F] A => φ
 α
· 使用定理 `IntermediateField.eq_of_le_of_finrank_eq'`：eq_of_le_of_finrank_eq' [Fini
teDimensional F L] (h_le : F <= E) (h_finrank : finrank F L = finrank E L) : F =
 E
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.finrank_top`：∀ {F : Type u_1} [inst : Field F] {E : Ty
pe u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.finrank (↥⊤) E = 1
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.card_of_splits`：AlgHom.card_of_splits (L : Type*) [Field L] [Alge
bra F L] (hL : forall x : E, ((minpoly F x).map (algebraMap F L)).Splits) : Fint
ype.card (E…
· 使用定理 `IsIntegral.minpoly_splits_tower_top`：IsIntegral.minpoly_splits_tower_top
 [Algebra K L] [Algebra R L] [IsScalarTower R K L] (int : IsIntegral R x) (h : S
plits ((minpoly R x).map …
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
· 使用定理 `Fintype.card_eq_one_iff`：card_eq_one_iff : card α = 1 ↔ exists x : α, fo
rall y, y = x
· 使用定理 `AlgHom.restrictScalars_injective`：restrictScalars_injective : Function.I
njective (restrictScalars R : (A ->ₐ[S] B) -> A ->ₐ[R] B)
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
theorem primitive_element_iff_algHom_eq_of_eval (α : E)
    (φ : E →ₐ[F] A) : F⟮α⟯ = ⊤ ↔ ∀ ψ : E →ₐ[F] A, φ α = ψ α → φ = ψ := by
  refine ⟨fun h ψ hψ ↦ (Field.primitive_element_iff_algHom_eq_of_eval' F A hA α).mp h hψ,
    fun h ↦ eq_of_le_of_finrank_eq' le_top ?_⟩
  let : Algebra F⟮α⟯ A := (φ.comp F⟮α⟯.val).toAlgebra
  rw [IntermediateField.finrank_top, ← AlgHom.card_of_splits _ _ A, Fintype.card_eq_one_iff]
  · exact ⟨{ __ := φ, commutes' := fun _ ↦ rfl }, fun ψ ↦ AlgHom.restrictScalars_injective F <|
      Eq.symm <| h _ (ψ.commutes <| AdjoinSimple.gen F α).symm⟩
  · exact fun x ↦ (IsIntegral.of_finite F x).minpoly_splits_tower_top (hA x)

end Field

end iff

