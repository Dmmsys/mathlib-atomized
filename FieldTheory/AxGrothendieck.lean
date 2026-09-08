/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed
public import Mathlib.ModelTheory.Algebra.Ring.Definability

/-!
# Ax-Grothendieck

This file proves that if `K` is an algebraically closed field,
then any injective polynomial map `K^n → K^n` is also surjective.

## Main results

* `ax_grothendieck_zeroLocus`: If `K` is algebraically closed, `ι` is a finite type, and
  `S : Set (ι → K)` is the `zeroLocus` of some ideal of `MvPolynomial ι K`, then any injective
  polynomial map `S → S` is also surjective on `S`.
* `ax_grothendieck_univ`: Any injective polynomial map `K^n → K^n` is also surjective if `K` is an
  algebraically closed field.
* `ax_grothendieck_of_definable`: Any injective polynomial map `S → S` is also surjective on `S` if
  `K` is an algebraically closed field and `S` is a definable subset of `K^n`.
* `ax_grothendieck_of_locally_finite`: any injective polynomial map `R^n → R^n` is also surjective
  whenever `R` is an algebraic extension of a finite field.

## References

The first-order theory of algebraically closed fields, along with the Lefschetz Principle and
the Ax-Grothendieck Theorem were first formalized in Lean 3 by Joseph Hua
[here](https://github.com/Jlh18/ModelTheoryInLean8) with the master's thesis
[here](https://github.com/Jlh18/ModelTheory8Report)

-/

@[expose] public section


noncomputable section

open MvPolynomial Finset

/-- Any injective polynomial map over an algebraic extension of a finite field is surjective. -/
/-
**ax_grothendieck_of_locally_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ax_grothendieck_of_locally_finite {ι K R : Type*} [Field K] [Finite K] [Co
mmRing R] [Finite ι] [Algebra K R] [alg : Algebra.IsAlgebraic K R] (ps : ι -> Mv
Polynomial ι R) (S : Set (ι -> R)) (hm : S.MapsTo (fun v i => eval v (ps i)) S) 
(hinj : S.InjOn (fun v i => eval v (ps i))) : S.SurjOn (fun v i => eval v (ps i)
) S
参数：ps : ι -> MvPolynomial ι R；S : Set (ι -> R)；hm : S.MapsTo (fun v i => eval v 
(ps i)) S；hinj : S.InjOn (fun v i => eval v (ps i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAlgebraic_iff_isIntegral`：isAlgebraic_iff_isIntegral {x : A} : IsAlgeb
raic K x ↔ IsIntegral K x
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Finset.mem_union_right`：mem_union_right (s : Finset α) (h : a in t) : a 
in s union t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.mem_union_left`：mem_union_left (t : Finset α) (h : a in s) : a in
 s union t
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `isNoetherian_adjoin_finset`：isNoetherian_adjoin_finset [IsNoetherianRing
 R] (s : Finset A) (hs : forall x in s, IsIntegral R x) : IsNoetherian R (Algebr
a.adjoin R (s : …
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.finite_of_finite`：∀ (R : Type u_1) {M : Type u_2} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite R]   [Modul
e.Finite R M]…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `MvPolynomial.eval_mem`：eval_mem {p : MvPolynomial σ S} {s : subS} (hs : 
forall i in p.support, p.coeff i in s) {v : σ -> S} (hv : forall i, v i in s) : 
MvPolynomia…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.injective_iff_surjective`：injective_iff_surjective {f : α -> α} :
 Injective f ↔ Surjective f
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
Any injective polynomial map over an algebraic extension of a finite field is su
rjective.
-/
theorem ax_grothendieck_of_locally_finite {ι K R : Type*} [Field K] [Finite K] [CommRing R]
    [Finite ι] [Algebra K R] [alg : Algebra.IsAlgebraic K R] (ps : ι → MvPolynomial ι R)
    (S : Set (ι → R))
    (hm : S.MapsTo (fun v i => eval v (ps i)) S)
    (hinj : S.InjOn (fun v i => eval v (ps i))) :
    S.SurjOn (fun v i => eval v (ps i)) S := by
  have is_int : ∀ x : R, IsIntegral K x := fun x => isAlgebraic_iff_isIntegral.1
    (alg.isAlgebraic x)
  classical
  intro v hvS
  cases nonempty_fintype ι
  /- `s` is the set of all coefficients of the polynomial, as well as all of
    the coordinates of `v`, the point I am trying to find the preimage of. -/
  let s : Finset R :=
    (Finset.biUnion (univ : Finset ι) fun i => (ps i).support.image fun x => coeff x (ps i)) ∪
      (univ : Finset ι).image v
  have hv : ∀ i, v i ∈ Algebra.adjoin K (s : Set R) := fun j =>
    Algebra.subset_adjoin (mem_union_right _ (mem_image.2 ⟨j, mem_univ _, rfl⟩))
  have hs₁ : ∀ (i : ι) (k : ι →₀ ℕ),
      k ∈ (ps i).support → coeff k (ps i) ∈ Algebra.adjoin K (s : Set R) :=
    fun i k hk => Algebra.subset_adjoin
      (mem_union_left _ (mem_biUnion.2 ⟨i, mem_univ _, mem_image_of_mem _ hk⟩))
  have := isNoetherian_adjoin_finset s fun x _ => is_int x
  have : Finite (Algebra.adjoin K (s : Set R)) := Module.finite_of_finite K
  -- The restriction of the polynomial map, `ps`, to the subalgebra generated by `s`
  let S' : Set (ι → Algebra.adjoin K (s : Set R)) :=
    (fun v => Subtype.val ∘ v) ⁻¹' S
  let res : S' → S' := fun x => ⟨fun i =>
    ⟨eval (fun j : ι => (x.1 j : R)) (ps i), eval_mem (hs₁ _) fun i => (x.1 i).2⟩,
      hm x.2⟩
  have hres_surj : Function.Surjective res := by
    rw [← Finite.injective_iff_surjective]
    intro x y hxy
    ext i
    simp only [Subtype.ext_iff, funext_iff] at hxy
    exact congr_fun (hinj x.2 y.2 (funext hxy)) i
  rcases hres_surj ⟨fun i => ⟨v i, hv i⟩, hvS⟩ with ⟨⟨w, hwS'⟩, hw⟩
  refine ⟨fun i => w i, hwS', ?_⟩
  simpa [Subtype.ext_iff, funext_iff] using hw

end

namespace FirstOrder

open MvPolynomial FreeCommRing Language FirstOrder.Field FirstOrder.Ring BoundedFormula

variable {ι α : Type*} [Finite α] {K : Type*} [Field K] [CompatibleRing K]

/-- The collection of first-order formulas corresponding to the Ax-Grothendieck theorem. -/
/-
**FirstOrder.genericPolyMapSurjOnOfInjOn** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder`。
形式化陈述：genericPolyMapSurjOnOfInjOn [Finite ι] (φ : ring.Formula (α oplus ι)) (mon
s : ι -> Finset (ι ->₀ Nat)) : Language.ring.Sentence
参数：φ : ring.Formula (α oplus ι)；mons : ι -> Finset (ι ->₀ Nat)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The collection of first-order formulas corresponding to the Ax-Grothendieck theo
rem.
-/
noncomputable def genericPolyMapSurjOnOfInjOn [Finite ι]
    (φ : ring.Formula (α ⊕ ι))
    (mons : ι → Finset (ι →₀ ℕ)) : Language.ring.Sentence :=
  let l1 : ι → Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    fun i =>
      (termOfFreeCommRing (genericPolyMap mons i)).relabel
        (Sum.inl ∘ Sum.map id (fun i => (0, i)))
    =' (termOfFreeCommRing (genericPolyMap mons i)).relabel
        (Sum.inl ∘ Sum.map id (fun i => (1, i)))
  -- p(x) = p(y) as a formula
  let f1 : Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    iInf l1
  let l2 : ι → Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    fun i => .var (Sum.inl (Sum.inr (0, i))) =' .var (Sum.inl (Sum.inr (1, i)))
  -- x = y as a formula
  let f2 : Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    iInf l2
  let injOn : Language.ring.Formula (α ⊕ Σ i : ι, mons i) :=
    Formula.iAlls (Fin 2 × ι)
      (φ.relabel (Sum.map Sum.inl (fun i => (0, i))) ⟹
       φ.relabel (Sum.map Sum.inl (fun i => (1, i))) ⟹
        (f1.imp f2).relabel (fun x => (Equiv.sumAssoc _ _ _).symm (Sum.inr x)))
  let l3 : ι → Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    fun i => (termOfFreeCommRing (genericPolyMap mons i)).relabel
        (Sum.inl ∘ Sum.map id (fun i => (0, i))) ='
      .var (Sum.inl (Sum.inr (1, i)))
  let f3 : Language.ring.Formula ((Σ i : ι, mons i) ⊕ (Fin 2 × ι)) :=
    iInf l3
  let surjOn : Language.ring.Formula (α ⊕ Σ i : ι, mons i) :=
    Formula.iAlls ι
      (Formula.imp (φ.relabel (Sum.map Sum.inl id)) <|
        Formula.iExs ι <|
          ((φ.relabel (Sum.map Sum.inl (fun i => (0, i)))) ⊓
            (f3.relabel (fun x => (Equiv.sumAssoc _ _ _).symm (Sum.inr x)))).relabel
        (fun (i : (α ⊕ (Σ i : ι, mons i)) ⊕ (Fin 2 × ι)) =>
          show ((α ⊕ (Σ i : ι, mons i)) ⊕ ι) ⊕ ι
          from Sum.elim (Sum.inl ∘ Sum.inl)
            (fun i => if i.1 = 0 then Sum.inr i.2 else (Sum.inl (Sum.inr i.2))) i))
  let mapsTo : Language.ring.Formula (α ⊕ Σ i : ι, mons i) :=
    Formula.iAlls ι
      (Formula.imp (φ.relabel (Sum.map Sum.inl id))
        (φ.subst <| Sum.elim
          (fun a => .var (Sum.inl (Sum.inl a)))
          (fun i => (termOfFreeCommRing (genericPolyMap mons i)).relabel
            (fun i => (Equiv.sumAssoc _ _ _).symm (Sum.inr i)))))
  Formula.iAlls (α ⊕ Σ i : ι, mons i) ((mapsTo.imp <| injOn.imp <| surjOn).relabel Sum.inr)
/-
**FirstOrder.realize_genericPolyMapSurjOnOfInjOn** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder`。
形式化陈述：realize_genericPolyMapSurjOnOfInjOn [Finite ι] (φ : ring.Formula (α oplus 
ι)) (mons : ι -> Finset (ι ->₀ Nat)) : (K ⊨ genericPolyMapSurjOnOfInjOn φ mons) 
↔ forall (v : α -> K) (p : { p : ι -> MvPolynomial ι K // (forall i, (p i).suppo
rt subseteq mons i) }), let f : (ι -> K) -> (ι -> K)
参数：φ : ring.Formula (α oplus ι)；mons : ι -> Finset (ι ->₀ Nat)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.natAdd_zero`：∀ {n : ℕ}, Fin.natAdd 0 = Fin.cast ⋯
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.curry_symm_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Sort u_11)
, ⇑(Equiv.curry α β γ).symm = Function.uncurry
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FirstOrder.Ring.realize_termOfFreeCommRing`：realize_termOfFreeCommRing (
p : FreeCommRing α) (v : α -> R) : (termOfFreeCommRing p).realize v = FreeCommRi
ng.lift v p
· 使用定理 `FirstOrder.Ring.lift_genericPolyMap`：lift_genericPolyMap [DecidableEq κ]
 [CommRing R] [DecidableEq R] (monoms : ι -> Finset (κ ->₀ Nat)) (f : (i : ι) × 
{ x // x in monoms i } op…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.cons_one`：cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall 
i : Fin n.succ, α i.succ) : cons x p 1 = p 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_genericPolyMapSurjOnOfInjOn
    [Finite ι] (φ : ring.Formula (α ⊕ ι)) (mons : ι → Finset (ι →₀ ℕ)) :
    (K ⊨ genericPolyMapSurjOnOfInjOn φ mons) ↔
      ∀ (v : α → K) (p : { p : ι → MvPolynomial ι K // (∀ i, (p i).support ⊆ mons i) }),
        let f : (ι → K) → (ι → K) := fun v i => eval v (p.1 i)
        let S : Set (ι → K) := {x | φ.Realize (Sum.elim v x)}
        S.MapsTo f S → S.InjOn f → S.SurjOn f S := by
  classical
  have injOnAlt : ∀ {S : Set (ι → K)} (f : (ι → K) → (ι → K)),
      S.InjOn f ↔ ∀ x y, x ∈ S → y ∈ S → f x = f y → x = y := by
    simp [Set.InjOn]; tauto
  simp only [Sentence.Realize, Formula.Realize, genericPolyMapSurjOnOfInjOn, Formula.relabel,
    Function.comp_def, Sum.map, id_eq, Equiv.sumAssoc, Equiv.coe_fn_symm_mk, Sum.elim_inr,
    realize_iAlls, realize_imp, realize_relabel, Fin.natAdd_zero, realize_subst, realize_iInf,
    realize_bdEqual, Term.realize_relabel,
    Equiv.forall_congr_left (Equiv.curry (Fin 2) ι K), Equiv.curry_symm_apply,
    Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, realize_iExs, realize_inf, Sum.forall_sum,
    Set.MapsTo, Set.mem_ofPred_eq, injOnAlt, funext_iff, Set.SurjOn, Set.image,
    Set.subset_def, Equiv.forall_congr_left (mvPolynomialSupportLEEquiv mons)]
  simp +singlePass only [← Sum.elim_comp_inl_inr]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Fin.castAdd_zero, Fin.cast_eq_self,
    Nat.add_zero, Term.realize_var, Term.realize_relabel, realize_termOfFreeCommRing,
    lift_genericPolyMap, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair, Fin.cons_zero,
    Fin.cons_one, ↓reduceIte, one_ne_zero]
/-
**FirstOrder.ACF_models_genericPolyMapSurjOnOfInjOn_of_prime** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder`。
形式化陈述：ACF_models_genericPolyMapSurjOnOfInjOn_of_prime [Finite ι] {p : Nat} (hp :
 p.Prime) (φ : ring.Formula (α oplus ι)) (mons : ι -> Finset (ι ->₀ Nat)) : Theo
ry.ACF p ⊨ᵇ genericPolyMapSurjOnOfInjOn φ mons
参数：hp : p.Prime；φ : ring.Formula (α oplus ι)；mons : ι -> Finset (ι ->₀ Nat)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Theory.IsComplete.realize_sentence_iff`：realize_sent
ence_iff (h : T.IsComplete) (φ : L.Sentence) (M : Type*) [L.Structure M] [M ⊨ T]
 [Nonempty M] : M ⊨ φ ↔ T ⊨ᵇ φ
· 使用定理 `FirstOrder.Field.ACF_isComplete`：ACF_isComplete {p : Nat} (hp : p.Prime 
∨ p = 0) : (Theory.ACF p).IsComplete
· 使用定理 `FirstOrder.Field.instModelACFOfCharPOfIsAlgClosed`：∀ {K : Type u_1} [ins
t : Field K] [inst_1 : FirstOrder.Ring.CompatibleRing K] {p : ℕ} [CharP K p] [Is
AlgClosed K],   K ⊨ FirstOrder.Language…
· 使用定理 `AlgebraicClosure.instCharP`：∀ (k : Type u) [inst : Field k] {p : ℕ} [Cha
rP k p], CharP (AlgebraicClosure k) p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `FirstOrder.realize_genericPolyMapSurjOnOfInjOn`：realize_genericPolyMapSu
rjOnOfInjOn [Finite ι] (φ : ring.Formula (α oplus ι)) (mons : ι -> Finset (ι ->₀
 Nat)) : (K ⊨ genericPolyMapSurjOnOf…
· 使用定理 `ax_grothendieck_of_locally_finite`：ax_grothendieck_of_locally_finite {ι 
K R : Type*} [Field K] [Finite K] [CommRing R] [Finite ι] [Algebra K R] [alg : A
lgebra.IsAlgebraic K R]…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
-/
theorem ACF_models_genericPolyMapSurjOnOfInjOn_of_prime [Finite ι]
    {p : ℕ} (hp : p.Prime) (φ : ring.Formula (α ⊕ ι)) (mons : ι → Finset (ι →₀ ℕ)) :
    Theory.ACF p ⊨ᵇ genericPolyMapSurjOnOfInjOn φ mons := by
  have : Fact p.Prime := ⟨hp⟩
  let := compatibleRingOfRing (AlgebraicClosure (ZMod p))
  rw [← (ACF_isComplete (Or.inl hp)).realize_sentence_iff _
    (AlgebraicClosure (ZMod p)), realize_genericPolyMapSurjOnOfInjOn]
  rintro v ⟨f, _⟩
  exact ax_grothendieck_of_locally_finite (K := ZMod p) (ι := ι) f _
/-
**FirstOrder.ACF_models_genericPolyMapSurjOnOfInjOn_of_prime_or_zero** 是 Mathlib
 中的一个定理，位于命名空间 `FirstOrder`。
形式化陈述：ACF_models_genericPolyMapSurjOnOfInjOn_of_prime_or_zero [Finite ι] {p : Na
t} (hp : p.Prime ∨ p = 0) (φ : ring.Formula (α oplus ι)) (mons : ι -> Finset (ι 
->₀ Nat)) : Theory.ACF p ⊨ᵇ genericPolyMapSurjOnOfInjOn φ mons
参数：hp : p.Prime ∨ p = 0；φ : ring.Formula (α oplus ι)；mons : ι -> Finset (ι ->₀ N
at)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.ACF_models_genericPolyMapSurjOnOfInjOn_of_prime`：ACF_models_g
enericPolyMapSurjOnOfInjOn_of_prime [Finite ι] {p : Nat} (hp : p.Prime) (φ : rin
g.Formula (α oplus ι)) (mons : ι -> Finset (ι ->…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize`：ACF_ze
ro_realize_iff_infinite_ACF_prime_realize {φ : Language.ring.Sentence} : Theory.
ACF 0 ⊨ᵇ φ ↔ Set.Infinite { p : Nat.Primes | Theory.AC…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.infinite_univ`：infinite_univ [h : Infinite α] : (@univ α).Infinite
· 使用定理 `Nat.Primes.infinite`：Infinite Nat.Primes
-/
theorem ACF_models_genericPolyMapSurjOnOfInjOn_of_prime_or_zero
    [Finite ι] {p : ℕ} (hp : p.Prime ∨ p = 0)
    (φ : ring.Formula (α ⊕ ι)) (mons : ι → Finset (ι →₀ ℕ)) :
    Theory.ACF p ⊨ᵇ genericPolyMapSurjOnOfInjOn φ mons := by
  rcases hp with hp | rfl
  · exact ACF_models_genericPolyMapSurjOnOfInjOn_of_prime hp φ mons
  · rw [ACF_zero_realize_iff_infinite_ACF_prime_realize]
    convert! Set.infinite_univ (α := Nat.Primes)
    rw [Set.eq_univ_iff_forall]
    intro ⟨p, hp⟩
    exact ACF_models_genericPolyMapSurjOnOfInjOn_of_prime hp φ mons

end FirstOrder

open FirstOrder Language Field Ring MvPolynomial

variable {K ι : Type*} [Field K] [IsAlgClosed K] [Finite ι]

/-- A slight generalization of the **Ax-Grothendieck** theorem

If `K` is an algebraically closed field, `ι` is a finite type, and `S` is a definable subset of
`ι → K`, then any injective polynomial map `S → S`  is also surjective on `S`. -/
/-
**ax_grothendieck_of_definable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ax_grothendieck_of_definable [CompatibleRing K] {c : Set K} (S : Set (ι ->
 K)) (hS : c.Definable Language.ring S) (ps : ι -> MvPolynomial ι K) : S.MapsTo 
(fun v i => eval v (ps i)) S -> S.InjOn (fun v i => eval v (ps i)) -> S.SurjOn (
fun v i => eval v (ps i)) S
参数：S : Set (ι -> K)；hS : c.Definable Language.ring S；ps : ι -> MvPolynomial ι K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.definable_iff_finitely_definable`：definable_iff_finitely_definable :
 A.Definable L s ↔ exists (A0 : Finset M), (A0 : Set M) subseteq A ∧ (A0 : Set M
).Definable L s
· 使用定理 `Set.definable_iff_exists_formula_sum`：definable_iff_exists_formula_sum :
 A.Definable L s ↔ exists φ : L.Formula (A oplus α), s = {v | φ.Realize (Sum.eli
m (↑) v)}
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `FirstOrder.ACF_models_genericPolyMapSurjOnOfInjOn_of_prime_or_zero`：ACF_
models_genericPolyMapSurjOnOfInjOn_of_prime_or_zero [Finite ι] {p : Nat} (hp : p
.Prime ∨ p = 0) (φ : ring.Formula (α oplus ι)) (mons : ι…
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `FirstOrder.realize_genericPolyMapSurjOnOfInjOn`：realize_genericPolyMapSu
rjOnOfInjOn [Finite ι] (φ : ring.Formula (α oplus ι)) (mons : ι -> Finset (ι ->₀
 Nat)) : (K ⊨ genericPolyMapSurjOnOf…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Theory.IsComplete.realize_sentence_iff`：realize_sent
ence_iff (h : T.IsComplete) (φ : L.Sentence) (M : Type*) [L.Structure M] [M ⊨ T]
 [Nonempty M] : M ⊨ φ ↔ T ⊨ᵇ φ
· 使用定理 `FirstOrder.Field.ACF_isComplete`：ACF_isComplete {p : Nat} (hp : p.Prime 
∨ p = 0) : (Theory.ACF p).IsComplete
· 使用定理 `FirstOrder.Field.instModelACFOfCharPOfIsAlgClosed`：∀ {K : Type u_1} [ins
t : Field K] [inst_1 : FirstOrder.Ring.CompatibleRing K] {p : ℕ} [CharP K p] [Is
AlgClosed K],   K ⊨ FirstOrder.Language…
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a

--- 原说明 ---
A slight generalization of the **Ax-Grothendieck** theorem

If `K` is an algebraically closed field, `ι` is a finite type, and `S` is a defi
nable subset of
`ι → K`, then any injective polynomial map `S → S`  is also surjective on `S`.
-/
theorem ax_grothendieck_of_definable [CompatibleRing K] {c : Set K}
    (S : Set (ι → K)) (hS : c.Definable Language.ring S)
    (ps : ι → MvPolynomial ι K) :
    S.MapsTo (fun v i => eval v (ps i)) S →
    S.InjOn (fun v i => eval v (ps i)) →
    S.SurjOn (fun v i => eval v (ps i)) S := by
  let := Fintype.ofFinite ι
  let p : ℕ := ringChar K
  rw [Set.definable_iff_finitely_definable] at hS
  rcases hS with ⟨c, _, hS⟩
  rw [Set.definable_iff_exists_formula_sum] at hS
  rcases hS with ⟨φ, hφ⟩
  rw [hφ]
  have := ACF_models_genericPolyMapSurjOnOfInjOn_of_prime_or_zero
    (CharP.char_is_prime_or_zero K p) φ (fun i => (ps i).support)
  rw [← (ACF_isComplete (CharP.char_is_prime_or_zero K p)).realize_sentence_iff _ K,
    realize_genericPolyMapSurjOnOfInjOn] at this
  exact this Subtype.val ⟨ps, fun i => Set.Subset.refl _⟩

/-- The **Ax-Grothendieck** theorem

If `K` is an algebraically closed field, and `S : Set (ι → K)` is the `zeroLocus` of an ideal
of the multivariable polynomial ring, then any injective polynomial map `S → S`  is also
surjective on `S`. -/
/-
**ax_grothendieck_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ax_grothendieck_zeroLocus (I : Ideal (MvPolynomial ι K)) (p : ι -> MvPolyn
omial ι K) : let S
参数：I : Ideal (MvPolynomial ι K)；p : ι -> MvPolynomial ι K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `ax_grothendieck_of_definable`：ax_grothendieck_of_definable [CompatibleRi
ng K] {c : Set K} (S : Set (ι -> K)) (hS : c.Definable Language.ring S) (ps : ι 
-> MvPolynomial ι …
· 使用定理 `FirstOrder.Ring.mvPolynomial_zeroLocus_definable`：mvPolynomial_zeroLocus
_definable {ι K : Type*} [Field K] [CompatibleRing K] (S : Finset (MvPolynomial 
ι K)) : Set.Definable (⋃ p in S, p.coe…

--- 原说明 ---
The **Ax-Grothendieck** theorem

If `K` is an algebraically closed field, and `S : Set (ι → K)` is the `zeroLocus
` of an ideal
of the multivariable polynomial ring, then any injective polynomial map `S → S` 
 is also
surjective on `S`.
-/
theorem ax_grothendieck_zeroLocus
    (I : Ideal (MvPolynomial ι K))
    (p : ι → MvPolynomial ι K) :
    let S := zeroLocus K I
    S.MapsTo (fun v i => eval v (p i)) S →
    S.InjOn (fun v i => eval v (p i)) →
    S.SurjOn (fun v i => eval v (p i)) S := by
  let := compatibleRingOfRing K
  intro S
  obtain ⟨s, rfl⟩ : I.FG := IsNoetherian.noetherian I
  exact ax_grothendieck_of_definable S (mvPolynomial_zeroLocus_definable s) p

/-- A special case of the **Ax-Grothendieck** theorem

Any injective polynomial map `K^n → K^n` is also surjective if `K` is an
algebraically closed field. -/
/-
**ax_grothendieck_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ax_grothendieck_univ (p : ι -> MvPolynomial ι K) : (fun v i => eval v (p i
)).Injective -> (fun v i => eval v (p i)).Surjective
参数：p : ι -> MvPolynomial ι K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.zeroLocus_bot`：zeroLocus_bot : zeroLocus K (⊥ : Ideal (MvPo
lynomial σ k)) = ⊤
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ax_grothendieck_zeroLocus`：ax_grothendieck_zeroLocus (I : Ideal (MvPolyn
omial ι K)) (p : ι -> MvPolynomial ι K) : let S

--- 原说明 ---
A special case of the **Ax-Grothendieck** theorem

Any injective polynomial map `K^n → K^n` is also surjective if `K` is an
algebraically closed field.
-/
theorem ax_grothendieck_univ (p : ι → MvPolynomial ι K) :
    (fun v i => eval v (p i)).Injective →
    (fun v i => eval v (p i)).Surjective := by
  simpa using ax_grothendieck_zeroLocus 0 p
